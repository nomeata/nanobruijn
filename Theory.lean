/-
# OSNF (Outermost-Shift Normal Form) — formal model

Most of the theory is proved. Four `sorry`s remain, all about the
isOSNF-preservation of `adjust_child` / `mk_osnf_compound`.

## The canonical form

The implementation uses explicit Shift nodes to defer shifting work. An OSNF
expression is one of:

1. `bvar 0` — the only `bvar` leaf.
2. `const id`.
3. `app f a` where both children are in OSNF and the compound's minimum free
   de Bruijn index is 0.
4. `lam body` where body is in OSNF and the compound's minimum free de Bruijn
   index is 0.
5. `shift n core` with `n > 0`, `core` in OSNF, `core`'s minimum free index 0,
   and `core` having at least one free variable.

Under this scheme, `bvar i` with `i > 0` is represented as `shift i (bvar 0)`.
There is no special leaf case for `bvar i`, only for `bvar 0`.

## Theorems we care about

- `to_osnf_erase` : `to_osnf` preserves denotation.
- `to_osnf_isOSNF` : the result is in OSNF.
- `osnf_unique` : OSNF is unique per denotation.
- `to_osnf_idempotent` : consequence.
- `equiv_iff_osnf_eq` : two SExprs are shift-equivalent iff they have the same OSNF.
-/

/-! ## FVarList: delta-encoded sorted sets of natural numbers

Used to track the set of free bvar indices appearing in an `SExpr`. The
delta encoding makes `shift` O(1) (touches only the head), matching the
behavior of `Shift` nodes in the implementation. -/

/-- Delta-encoded sorted set of natural numbers.
    `[]` is the empty set; `d :: rest` encodes `{d} ∪ {d + 1 + x | x ∈ decode rest}`. -/
abbrev FVarList := List Nat

namespace FVarList

/-- Shift all indices up by `k`. O(1): only changes the head. -/
def shift (k : Nat) : FVarList → FVarList
  | [] => []
  | d :: rest => (d + k) :: rest

/-- Remove bvar(0) and decrement all others (exiting a binder body). -/
def unbind : FVarList → FVarList
  | [] => []
  | 0 :: rest => rest
  | (d + 1) :: rest => d :: rest

/-- The lower bound (smallest free bvar index). -/
def lb : FVarList → Option Nat
  | [] => none
  | d :: _ => some d

/-- Merge two delta-encoded sorted sets. -/
def union (as bs : FVarList) : FVarList :=
  match as, bs with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x < y then
      x :: union xs ((y - x - 1) :: ys)
    else if x = y then
      x :: union xs ys
    else -- x > y
      y :: union ((x - y - 1) :: xs) ys
termination_by (as.length + bs.length, as.length)

/-- Absolute-value membership: `MemAbs i xs` iff the absolute index `i` is in
    the set decoded by `xs`. -/
inductive MemAbs : Nat → FVarList → Prop where
  | head (d : Nat) (rest : FVarList) : MemAbs d (d :: rest)
  | tail (i d : Nat) (rest : FVarList) (h : MemAbs i rest) :
      MemAbs (d + 1 + i) (d :: rest)

theorem not_memAbs_nil (i : Nat) : ¬ MemAbs i [] := by
  intro h; cases h

theorem memAbs_ge_head (d i : Nat) (rest : FVarList) (h : MemAbs i (d :: rest)) :
    i ≥ d := by
  cases h with
  | head => exact Nat.le_refl d
  | tail => omega

theorem memAbs_cons_cases (i d : Nat) (rest : FVarList) (h : MemAbs i (d :: rest)) :
    i = d ∨ ∃ jj, i = d + 1 + jj ∧ MemAbs jj rest := by
  cases h with
  | head => exact Or.inl rfl
  | tail jj _ _ hrest => exact Or.inr ⟨jj, by omega, hrest⟩

theorem memAbs_shift_iff (k i : Nat) (xs : FVarList) :
    MemAbs i (shift k xs) ↔ ∃ j, MemAbs j xs ∧ i = j + k := by
  cases xs with
  | nil =>
    simp only [shift]
    exact ⟨fun h => absurd h (not_memAbs_nil _),
           fun ⟨_, h, _⟩ => absurd h (not_memAbs_nil _)⟩
  | cons d rest =>
    simp only [shift]
    constructor
    · intro h
      cases h with
      | head _ _ => exact ⟨d, MemAbs.head _ _, by omega⟩
      | tail j' _ _ hrest => exact ⟨d + 1 + j', MemAbs.tail _ _ _ hrest, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      cases hj with
      | head _ _ =>
        have : d + k = d + k := rfl
        exact MemAbs.head _ _
      | tail j' _ _ hrest =>
        have heq : d + 1 + j' + k = (d + k) + 1 + j' := by omega
        rw [heq]
        exact MemAbs.tail _ _ _ hrest

private theorem memAbs_union_iff_aux (n : Nat) :
    ∀ (xs ys : FVarList), xs.length + ys.length ≤ n →
    ∀ (i : Nat), (MemAbs i (union xs ys) ↔ MemAbs i xs ∨ MemAbs i ys) := by
  induction n with
  | zero =>
    intro xs ys hn i
    match xs, ys with
    | [], [] =>
      simp only [union]
      exact ⟨Or.inr, fun h => h.resolve_left (not_memAbs_nil i)⟩
    | _ :: _, _ => simp at hn
    | [], _ :: _ => simp at hn
  | succ n' ih =>
    intro xs ys hn i
    match xs, ys with
    | [], ys =>
      simp only [union]
      exact ⟨Or.inr, fun h => h.resolve_left (not_memAbs_nil i)⟩
    | x :: xs', [] =>
      simp only [union]
      exact ⟨Or.inl, fun h => h.resolve_right (not_memAbs_nil i)⟩
    | x :: xs', y :: ys' =>
      simp only [union]
      split
      · -- x < y
        rename_i hxy
        have hlen : xs'.length + ((y - x - 1) :: ys').length ≤ n' := by
          simp at hn ⊢; omega
        have IH : ∀ j, MemAbs j (union xs' ((y - x - 1) :: ys')) ↔
                        MemAbs j xs' ∨ MemAbs j ((y - x - 1) :: ys') :=
          ih xs' ((y - x - 1) :: ys') hlen
        constructor
        · intro h
          rcases memAbs_cons_cases i x _ h with rfl | ⟨j', hiEq, hrest⟩
          · exact Or.inl (MemAbs.head _ _)
          · subst hiEq
            rcases (IH j').mp hrest with hxs | hys
            · exact Or.inl (MemAbs.tail j' x xs' hxs)
            · rcases memAbs_cons_cases j' (y - x - 1) _ hys with rfl | ⟨jj, hjEq, hys'rest⟩
              · have : x + 1 + (y - x - 1) = y := by omega
                rw [this]; exact Or.inr (MemAbs.head _ _)
              · subst hjEq
                have : x + 1 + (y - x - 1 + 1 + jj) = y + 1 + jj := by omega
                rw [this]; exact Or.inr (MemAbs.tail jj y ys' hys'rest)
        · rintro (hx | hy)
          · rcases memAbs_cons_cases i x _ hx with rfl | ⟨j', hiEq, hrest⟩
            · exact MemAbs.head _ _
            · subst hiEq
              exact MemAbs.tail j' x _ ((IH j').mpr (Or.inl hrest))
          · rcases memAbs_cons_cases i y _ hy with hiy | ⟨jj, hiEq, hys'rest⟩
            · have heq : i = x + 1 + (y - x - 1) := by omega
              rw [heq]
              exact MemAbs.tail (y - x - 1) x _
                ((IH (y - x - 1)).mpr (Or.inr (MemAbs.head _ _)))
            · have heq : i = x + 1 + (y - x - 1 + 1 + jj) := by omega
              rw [heq]
              exact MemAbs.tail _ x _
                ((IH (y - x - 1 + 1 + jj)).mpr
                  (Or.inr (MemAbs.tail jj _ ys' hys'rest)))
      · rename_i hxy
        split
        · -- x = y
          rename_i heq
          have hlen : xs'.length + ys'.length ≤ n' := by
            simp at hn ⊢; omega
          have IH : ∀ j, MemAbs j (union xs' ys') ↔
                          MemAbs j xs' ∨ MemAbs j ys' :=
            ih xs' ys' hlen
          constructor
          · intro h
            rcases memAbs_cons_cases i x _ h with rfl | ⟨j', hiEq, hrest⟩
            · exact Or.inl (MemAbs.head _ _)
            · subst hiEq
              rcases (IH j').mp hrest with hxs | hys
              · exact Or.inl (MemAbs.tail j' x xs' hxs)
              · rw [heq]; exact Or.inr (MemAbs.tail j' y ys' hys)
          · rintro (hx | hy)
            · rcases memAbs_cons_cases i x _ hx with rfl | ⟨j', hiEq, hrest⟩
              · exact MemAbs.head _ _
              · subst hiEq
                exact MemAbs.tail j' x _ ((IH j').mpr (Or.inl hrest))
            · rcases memAbs_cons_cases i y _ hy with hiy | ⟨j', hiEq, hrest⟩
              · have : i = x := by omega
                rw [this]; exact MemAbs.head _ _
              · have : i = x + 1 + j' := by omega
                rw [this]
                exact MemAbs.tail _ x _ ((IH j').mpr (Or.inr hrest))
        · -- x > y
          rename_i hne
          have hgt : x > y := by omega
          have hlen : ((x - y - 1) :: xs').length + ys'.length ≤ n' := by
            simp at hn ⊢; omega
          have IH : ∀ j, MemAbs j (union ((x - y - 1) :: xs') ys') ↔
                          MemAbs j ((x - y - 1) :: xs') ∨ MemAbs j ys' :=
            ih ((x - y - 1) :: xs') ys' hlen
          constructor
          · intro h
            rcases memAbs_cons_cases i y _ h with rfl | ⟨j', hiEq, hrest⟩
            · exact Or.inr (MemAbs.head _ _)
            · subst hiEq
              rcases (IH j').mp hrest with hxs | hys
              · rcases memAbs_cons_cases j' (x - y - 1) _ hxs with rfl | ⟨jj, hjEq, hxs'rest⟩
                · have : y + 1 + (x - y - 1) = x := by omega
                  rw [this]; exact Or.inl (MemAbs.head _ _)
                · subst hjEq
                  have : y + 1 + (x - y - 1 + 1 + jj) = x + 1 + jj := by omega
                  rw [this]; exact Or.inl (MemAbs.tail jj x xs' hxs'rest)
              · exact Or.inr (MemAbs.tail j' y ys' hys)
          · rintro (hx | hy)
            · rcases memAbs_cons_cases i x _ hx with hix | ⟨j', hiEq, hrest⟩
              · have heq : i = y + 1 + (x - y - 1) := by omega
                rw [heq]
                exact MemAbs.tail _ y _
                  ((IH (x - y - 1)).mpr (Or.inl (MemAbs.head _ _)))
              · have heq : i = y + 1 + (x - y - 1 + 1 + j') := by omega
                rw [heq]
                exact MemAbs.tail _ y _
                  ((IH (x - y - 1 + 1 + j')).mpr
                    (Or.inl (MemAbs.tail j' _ xs' hrest)))
            · rcases memAbs_cons_cases i y _ hy with hiy | ⟨j', hiEq, hrest⟩
              · have : i = y := hiy
                rw [this]; exact MemAbs.head _ _
              · have : i = y + 1 + j' := hiEq
                rw [this]
                exact MemAbs.tail j' y _ ((IH j').mpr (Or.inr hrest))

theorem memAbs_union_iff (i : Nat) (xs ys : FVarList) :
    MemAbs i (union xs ys) ↔ MemAbs i xs ∨ MemAbs i ys :=
  memAbs_union_iff_aux (xs.length + ys.length) xs ys (Nat.le_refl _) i

theorem memAbs_unbind_iff (i : Nat) (xs : FVarList) :
    MemAbs i (unbind xs) ↔ MemAbs (i + 1) xs := by
  cases xs with
  | nil =>
    simp only [unbind]
    exact ⟨fun h => absurd h (not_memAbs_nil _),
           fun h => absurd h (not_memAbs_nil _)⟩
  | cons d rest =>
    match d with
    | 0 =>
      simp only [unbind]
      constructor
      · intro h
        have heq : i + 1 = 0 + 1 + i := by omega
        rw [heq]
        exact MemAbs.tail i 0 rest h
      · intro h
        generalize hq : i + 1 = q at h
        cases h with
        | head _ _ => omega
        | tail j' _ _ hrest =>
          have : i = j' := by omega
          rw [this]; exact hrest
    | d' + 1 =>
      simp only [unbind]
      constructor
      · intro h
        cases h with
        | head _ _ => exact MemAbs.head _ _
        | tail j' _ _ hrest =>
          have : d' + 1 + j' + 1 = d' + 1 + 1 + j' := by omega
          rw [this]
          exact MemAbs.tail j' (d' + 1) rest hrest
      · intro h
        generalize hq : i + 1 = q at h
        cases h with
        | head _ _ =>
          have : i = d' := by omega
          rw [this]; exact MemAbs.head _ _
        | tail j' _ _ hrest =>
          have : i = d' + 1 + j' := by omega
          rw [this]
          exact MemAbs.tail j' d' rest hrest

end FVarList

/-! ## Plain expressions and shift -/

inductive Expr where
  | bvar (i : Nat)
  | app (f a : Expr)
  | lam (body : Expr)  -- simplified: no binder type
  | const (id : Nat)
  deriving Repr, DecidableEq

namespace Expr

/-- Shift free variables by `k` above cutoff `c`. -/
def shift : Expr → (k : Nat) → (c : Nat := 0) → Expr
  | bvar i, k, c => if i ≥ c then bvar (i + k) else bvar i
  | app f a, k, c => app (f.shift k c) (a.shift k c)
  | lam body, k, c => lam (body.shift k (c + 1))
  | const id, _, _ => const id

theorem shift_zero (e : Expr) (c : Nat) : e.shift 0 c = e := by
  induction e generalizing c with
  | bvar i => simp only [shift]; split <;> (first | (congr 1; omega) | rfl)
  | app f a ihf iha => simp only [shift, ihf, iha]
  | lam body ih => simp only [shift, ih]
  | const _ => rfl

theorem shift_shift (e : Expr) (j k c : Nat) :
    (e.shift j c).shift k c = e.shift (j + k) c := by
  induction e generalizing c with
  | bvar i =>
    simp only [shift]
    by_cases h : i ≥ c
    · simp only [h, ↓reduceIte, shift, show i + j ≥ c from by omega, Expr.bvar.injEq]; omega
    · simp only [h, ↓reduceIte, shift]
  | app f a ihf iha => simp only [shift, ihf, iha]
  | lam body ih => simp only [shift, ih]
  | const _ => rfl

theorem shift_shift_comm (e : Expr) (j k c d : Nat) (hcd : c ≤ d) (hdj : d ≤ c + j) :
    (e.shift j c).shift k d = e.shift (j + k) c := by
  induction e generalizing c d with
  | bvar i =>
    simp only [shift]
    by_cases h : i ≥ c
    · simp only [h, ↓reduceIte, shift, show i + j ≥ d from by omega, Expr.bvar.injEq]; omega
    · simp only [h, ↓reduceIte, shift, show ¬(i ≥ d) from by omega]
  | app f a ihf iha => simp only [shift, ihf c d hcd hdj, iha c d hcd hdj]
  | lam body ih =>
    simp only [shift]
    exact congrArg Expr.lam (ih (c + 1) (d + 1) (by omega) (by omega))
  | const _ => rfl

private theorem shift_comm_lt_gen (e : Expr) (k amount cutoff base : Nat) (hlt : k < cutoff) :
    (e.shift k base).shift amount (cutoff + base) =
    (e.shift amount (cutoff - k + base)).shift k base := by
  induction e generalizing k cutoff base with
  | bvar i =>
    simp only [shift]
    by_cases h : i ≥ base
    · simp only [h, ↓reduceIte]
      by_cases hi : i + k ≥ cutoff + base
      · simp only [shift, hi, ↓reduceIte, show i ≥ cutoff - k + base from by omega,
          show i + amount ≥ base from by omega, Expr.bvar.injEq]; omega
      · simp only [shift, hi, ↓reduceIte, show ¬(i ≥ cutoff - k + base) from by omega, h]
    · simp only [h, ↓reduceIte, shift, show ¬(i ≥ cutoff + base) from by omega,
        show ¬(i ≥ cutoff - k + base) from by omega]
  | app f a ihf iha => simp only [shift, ihf k cutoff base hlt, iha k cutoff base hlt]
  | lam body ih =>
    simp only [shift]
    exact congrArg Expr.lam (ih k cutoff (base + 1) hlt)
  | const _ => rfl

theorem shift_comm_lt (e : Expr) (k amount cutoff : Nat) (hlt : k < cutoff) :
    (e.shift k 0).shift amount cutoff = (e.shift amount (cutoff - k)).shift k 0 := by
  have h := shift_comm_lt_gen e k amount cutoff 0 hlt
  simp only [Nat.add_zero] at h; exact h

/-- An expression has a free variable at index `i` above cutoff `c`. -/
inductive HasFreeVar : Expr → Nat → Nat → Prop where
  | bvar (i c : Nat) (h : i ≥ c) : HasFreeVar (bvar i) i c
  | app_left (f a : Expr) (i c : Nat) (h : HasFreeVar f i c) : HasFreeVar (app f a) i c
  | app_right (f a : Expr) (i c : Nat) (h : HasFreeVar a i c) : HasFreeVar (app f a) i c
  | lam (body : Expr) (i c : Nat) (h : HasFreeVar body i (c + 1)) : HasFreeVar (lam body) i c

/-- External free-variable predicate: `ExtFreeVar e k` iff, treating `e` as a
    term at depth 0, there is a bvar whose **external index** (internal name
    minus the number of binders it sits under) equals `k`. This is the view
    matched by `SExpr.fvars`: under a lambda, body's external index `k+1`
    corresponds to `lam body`'s external index `k`. -/
inductive ExtFreeVar : Expr → Nat → Prop where
  | bvar (i : Nat) : ExtFreeVar (bvar i) i
  | app_left {f a : Expr} {k : Nat} (h : ExtFreeVar f k) : ExtFreeVar (app f a) k
  | app_right {f a : Expr} {k : Nat} (h : ExtFreeVar a k) : ExtFreeVar (app f a) k
  | lam {body : Expr} {k : Nat} (h : ExtFreeVar body (k + 1)) : ExtFreeVar (lam body) k

/-- All free variables of `e` at cutoff `c` are `≥ bound`. -/
def AllFreeVarsGe (e : Expr) (bound : Nat) (c : Nat := 0) : Prop :=
  ∀ i, HasFreeVar e i c → i ≥ bound

private theorem allFreeVarsGe_shift_gen (e : Expr) (k c : Nat) :
    AllFreeVarsGe (e.shift k c) (c + k) c := by
  intro i hi
  induction e generalizing c with
  | bvar j =>
    simp only [shift] at hi
    by_cases hj : j ≥ c
    · simp only [hj, ite_true] at hi; cases hi with | bvar _ _ hge => omega
    · simp only [hj, ite_false] at hi; cases hi with | bvar _ _ hge => omega
  | app f a ihf iha =>
    simp only [shift] at hi
    cases hi with
    | app_left _ _ _ _ hf => exact ihf c hf
    | app_right _ _ _ _ ha => exact iha c ha
  | lam body ih =>
    simp only [shift] at hi
    cases hi with
    | lam _ _ _ hb => have := ih (c + 1) hb; omega
  | const _ => simp only [shift] at hi; cases hi

theorem allFreeVarsGe_shift_zero (e : Expr) (k : Nat) :
    AllFreeVarsGe (e.shift k 0) k 0 := by
  have := allFreeVarsGe_shift_gen e k 0; simpa using this

theorem no_freevar_zero_in_shifted (e : Expr) (k : Nat) (hk : k > 0) :
    ¬ HasFreeVar (e.shift k 0) 0 0 := by
  intro h; have := allFreeVarsGe_shift_zero e k 0 h; omega

theorem shift_eq_of_no_freevars (e : Expr) (k c : Nat)
    (h : ∀ i, ¬ HasFreeVar e i c) : e.shift k c = e := by
  induction e generalizing c with
  | bvar i =>
    simp only [shift]
    by_cases hic : i ≥ c
    · exact absurd (HasFreeVar.bvar i c hic) (h i)
    · rw [if_neg hic]
  | app f a ihf iha =>
    simp only [shift]
    rw [ihf c (fun i hi => h i (HasFreeVar.app_left _ _ _ _ hi))]
    rw [iha c (fun i hi => h i (HasFreeVar.app_right _ _ _ _ hi))]
  | lam body ih =>
    simp only [shift]
    rw [ih (c + 1) (fun i hi => h i (HasFreeVar.lam _ _ _ hi))]
  | const _ => rfl

/-- Stronger forward decomposition of ExtFreeVar on a shift. -/
theorem extFreeVar_shift_extract (e : Expr) (n c i : Nat) :
    ExtFreeVar (e.shift n c) i →
    (ExtFreeVar e (i - n) ∧ i ≥ n + c) ∨ (ExtFreeVar e i ∧ i < c) := by
  induction e generalizing c i with
  | bvar j =>
    intro h
    simp only [shift] at h
    by_cases hjc : j ≥ c
    · simp only [hjc, ↓reduceIte] at h
      cases h with
      | bvar _ =>
        left
        refine ⟨?_, ?_⟩
        · have : j + n - n = j := by omega
          rw [this]; exact ExtFreeVar.bvar _
        · omega
    · simp only [hjc, ↓reduceIte] at h
      cases h with
      | bvar _ => right; exact ⟨ExtFreeVar.bvar _, by omega⟩
  | app f a ihf iha =>
    intro h
    simp only [shift] at h
    cases h with
    | app_left hf =>
      rcases ihf c i hf with ⟨hfe, hi⟩ | ⟨hfe, hi⟩
      · exact Or.inl ⟨ExtFreeVar.app_left hfe, hi⟩
      · exact Or.inr ⟨ExtFreeVar.app_left hfe, hi⟩
    | app_right ha =>
      rcases iha c i ha with ⟨hae, hi⟩ | ⟨hae, hi⟩
      · exact Or.inl ⟨ExtFreeVar.app_right hae, hi⟩
      · exact Or.inr ⟨ExtFreeVar.app_right hae, hi⟩
  | lam body ih =>
    intro h
    simp only [shift] at h
    cases h with
    | lam hb =>
      rcases ih (c+1) (i+1) hb with ⟨hbe, hi⟩ | ⟨hbe, hi⟩
      · left
        refine ⟨?_, ?_⟩
        · have : i + 1 - n = (i - n) + 1 := by omega
          rw [this] at hbe
          exact ExtFreeVar.lam hbe
        · omega
      · right
        exact ⟨ExtFreeVar.lam hbe, by omega⟩
  | const _ =>
    intro h
    simp only [shift] at h
    cases h

/-- Shift preserves / creates external bvars with a cutoff-parametrized predictable pattern. -/
theorem extFreeVar_shift_fwd (e : Expr) (n c k : Nat) :
    ExtFreeVar (e.shift n c) k → k ≥ n + c ∨ k < c := by
  induction e generalizing c k with
  | bvar i =>
    intro h
    simp only [shift] at h
    by_cases hic : i ≥ c
    · simp only [hic, ↓reduceIte] at h
      cases h; left; omega
    · simp only [hic, ↓reduceIte] at h
      cases h; right; omega
  | app f a ihf iha =>
    intro h
    simp only [shift] at h
    cases h with
    | app_left hf => exact ihf c k hf
    | app_right ha => exact iha c k ha
  | lam body ih =>
    intro h
    simp only [shift] at h
    cases h with
    | lam hb =>
      have := ih (c+1) (k+1) hb
      omega
  | const _ =>
    intro h
    simp only [shift] at h
    cases h

/-- Specialised to cutoff 0. -/
theorem extFreeVar_shift_zero_ge (e : Expr) (n k : Nat)
    (h : ExtFreeVar (e.shift n 0) k) : k ≥ n := by
  rcases extFreeVar_shift_fwd e n 0 k h with hge | hlt
  · omega
  · omega

/-- Shifting back: external bvar j in e gives external bvar j+n (if j ≥ c) in
    e.shift n c. -/
theorem extFreeVar_shift_bwd (e : Expr) (j : Nat) (h : ExtFreeVar e j) (n c : Nat) :
    ExtFreeVar (e.shift n c) (if j ≥ c then j + n else j) := by
  induction h generalizing c with
  | bvar i =>
    simp only [shift]
    by_cases hic : i ≥ c
    · simp only [hic, ↓reduceIte]; exact ExtFreeVar.bvar _
    · simp only [hic, ↓reduceIte]; exact ExtFreeVar.bvar _
  | app_left _ ih =>
    simp only [shift]; exact ExtFreeVar.app_left (ih c)
  | app_right _ ih =>
    simp only [shift]; exact ExtFreeVar.app_right (ih c)
  | @lam body k hb ih =>
    simp only [shift]
    have ih' := ih (c + 1)
    apply ExtFreeVar.lam
    by_cases hkc : k ≥ c
    · simp only [hkc, ↓reduceIte]
      simp only [show k + 1 ≥ c + 1 from by omega, ↓reduceIte] at ih'
      show (body.shift n (c + 1)).ExtFreeVar (k + n + 1)
      have : k + n + 1 = k + 1 + n := by omega
      rw [this]; exact ih'
    · simp only [hkc, ↓reduceIte]
      simp only [show ¬(k + 1 ≥ c + 1) from by omega, ↓reduceIte] at ih'
      exact ih'

/-- If all external free vars of e are below c, shift at cutoff c is a no-op. -/
theorem shift_eq_of_extFreeVars_lt (e : Expr) (k c : Nat)
    (h : ∀ j, ExtFreeVar e j → j < c) : e.shift k c = e := by
  induction e generalizing c with
  | bvar i =>
    simp only [shift]
    split
    · rename_i hic
      exfalso; exact absurd (h i (ExtFreeVar.bvar _)) (by omega)
    · rfl
  | app f a ihf iha =>
    simp only [shift]
    rw [ihf c (fun j hj => h j (ExtFreeVar.app_left hj))]
    rw [iha c (fun j hj => h j (ExtFreeVar.app_right hj))]
  | lam body ih =>
    simp only [shift]
    refine congrArg Expr.lam (ih (c + 1) ?_)
    intro j hj
    by_cases hj0 : j = 0
    · omega
    · have hj1 : j ≥ 1 := by omega
      have : ExtFreeVar (Expr.lam body) (j - 1) := by
        have heq : (j - 1) + 1 = j := by omega
        rw [← heq] at hj
        exact ExtFreeVar.lam hj
      have := h (j - 1) this
      omega
  | const _ => rfl

/-- Specialisation: closed (no ExtFreeVar) expression shift at cutoff 0 is a no-op. -/
theorem shift_eq_of_no_extFreeVar (e : Expr) (k : Nat)
    (h : ∀ j, ¬ ExtFreeVar e j) : e.shift k 0 = e :=
  shift_eq_of_extFreeVars_lt e k 0 (fun j hj => absurd hj (h j))

theorem shift_injective (k c : Nat) : ∀ (e₁ e₂ : Expr),
    e₁.shift k c = e₂.shift k c → e₁ = e₂ := by
  intro e₁
  induction e₁ generalizing c with
  | bvar i =>
    intro e₂ h
    cases e₂ with
    | bvar j =>
      simp only [shift] at h
      split at h <;> split at h <;> simp_all [bvar.injEq] <;> omega
    | app f a => simp only [shift] at h; split at h <;> simp at h
    | lam body => simp only [shift] at h; split at h <;> simp at h
    | const n => simp only [shift] at h; split at h <;> simp at h
  | app f₁ a₁ ihf iha =>
    intro e₂ h
    cases e₂ with
    | bvar j => simp only [shift] at h; split at h <;> simp at h
    | app f₂ a₂ =>
      simp only [shift, app.injEq] at h
      have h1 := ihf c f₂ h.1
      have h2 := iha c a₂ h.2
      subst h1; subst h2; rfl
    | lam body => simp only [shift] at h; simp at h
    | const n => simp only [shift] at h; simp at h
  | lam body₁ ih =>
    intro e₂ h
    cases e₂ with
    | bvar j => simp only [shift] at h; split at h <;> simp at h
    | app f a => simp only [shift] at h; simp at h
    | lam body₂ =>
      simp only [shift, lam.injEq] at h
      exact congrArg lam (ih (c + 1) body₂ h)
    | const n => simp only [shift] at h; simp at h
  | const n₁ =>
    intro e₂ h
    cases e₂ with
    | bvar j => simp only [shift] at h; split at h <;> simp at h
    | app f a => simp only [shift] at h; simp at h
    | lam body => simp only [shift] at h; simp at h
    | const n₂ => simp only [shift, const.injEq] at h; exact congrArg const h

end Expr

/-! ## SExpr: expressions with explicit Shift nodes

Models the implementation's `Expr` + `ExprPtr`: an `SExpr` is either a plain
constructor (bvar, app, lam, const) or a `shift n inner` wrapper. Only cutoff
0 is modeled — that's what `mk_shift` in the implementation produces. -/

inductive SExpr where
  | bvar (i : Nat)
  | app (f a : SExpr)
  | lam (body : SExpr)
  | const (id : Nat)
  | shift (amount : Nat) (inner : SExpr)
  deriving Repr, DecidableEq

namespace SExpr

/-! ### Erasure: interpret an SExpr as a plain Expr by pushing shifts through -/

/-- Erase all Shift nodes, producing the plain Expr this SExpr denotes. -/
def erase : SExpr → Expr
  | bvar i => .bvar i
  | app f a => .app f.erase a.erase
  | lam body => .lam body.erase
  | const id => .const id
  | shift k inner => inner.erase.shift k 0

/-- Two SExprs are shift-equivalent iff they erase to the same Expr. -/
def equiv (e₁ e₂ : SExpr) : Prop := e₁.erase = e₂.erase

/-! ### Free variable tracking -/

/-- Compute the delta-encoded free variable list for an SExpr. -/
def fvars : SExpr → FVarList
  | bvar i => [i]
  | app f a => FVarList.union f.fvars a.fvars
  | lam body => FVarList.unbind body.fvars
  | const _ => []
  | shift k inner => FVarList.shift k inner.fvars

/-- `fvar_lb_val` as a Nat, returning 0 for closed expressions. -/
def fvar_lb_val (e : SExpr) : Nat :=
  match e.fvars with
  | [] => 0
  | d :: _ => d

/-! ### Link between structural fvars and external fvars on erase -/

theorem memAbs_fvars_iff_extFreeVar (e : SExpr) (i : Nat) :
    FVarList.MemAbs i e.fvars ↔ Expr.ExtFreeVar e.erase i := by
  induction e generalizing i with
  | bvar j =>
    simp only [fvars, erase]
    constructor
    · intro h
      rcases FVarList.memAbs_cons_cases i j [] h with hij | ⟨jj, _, hrest⟩
      · rw [hij]; exact Expr.ExtFreeVar.bvar _
      · exact absurd hrest (FVarList.not_memAbs_nil _)
    · intro h
      cases h with
      | bvar _ => exact FVarList.MemAbs.head _ _
  | const n =>
    simp only [fvars, erase]
    constructor
    · intro h; exact absurd h (FVarList.not_memAbs_nil _)
    · intro h; cases h
  | app f a ihf iha =>
    simp only [fvars, erase]
    rw [FVarList.memAbs_union_iff, ihf, iha]
    constructor
    · rintro (hf | ha)
      · exact Expr.ExtFreeVar.app_left hf
      · exact Expr.ExtFreeVar.app_right ha
    · intro h
      cases h with
      | app_left hf => exact Or.inl hf
      | app_right ha => exact Or.inr ha
  | lam body ih =>
    simp only [fvars, erase]
    rw [FVarList.memAbs_unbind_iff, ih]
    constructor
    · intro h; exact Expr.ExtFreeVar.lam h
    · intro h; cases h with | lam h => exact h
  | shift k inner ih =>
    simp only [fvars, erase]
    rw [FVarList.memAbs_shift_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have : Expr.ExtFreeVar inner.erase j := (ih j).mp hj
      have := Expr.extFreeVar_shift_bwd inner.erase j this k 0
      simp only [show j ≥ 0 from Nat.zero_le _, ↓reduceIte] at this
      exact this
    · intro h
      rcases Expr.extFreeVar_shift_extract inner.erase k 0 i h with ⟨hfe, hge⟩ | ⟨_, hlt⟩
      · refine ⟨i - k, (ih (i - k)).mpr hfe, ?_⟩
        omega
      · omega

/-- `e.fvars = []` iff the erasure has no external free bvars. -/
theorem fvars_empty_iff_no_extFreeVar (e : SExpr) :
    e.fvars = [] ↔ ∀ i, ¬ Expr.ExtFreeVar e.erase i := by
  constructor
  · intro h i hext
    have := (memAbs_fvars_iff_extFreeVar e i).mpr hext
    rw [h] at this
    exact FVarList.not_memAbs_nil _ this
  · intro h
    match hfv : e.fvars with
    | [] => rfl
    | d :: rest =>
      exfalso
      have : FVarList.MemAbs d e.fvars := by rw [hfv]; exact FVarList.MemAbs.head _ _
      exact h d ((memAbs_fvars_iff_extFreeVar e d).mp this)

/-- If fvar_lb_val is 0 and fvars is non-empty, 0 is an external free var. -/
theorem fvar_lb_zero_has_extFreeVar_zero (e : SExpr)
    (hlb : fvar_lb_val e = 0) (hne : e.fvars ≠ []) :
    Expr.ExtFreeVar e.erase 0 := by
  apply (memAbs_fvars_iff_extFreeVar e 0).mp
  match hfv : e.fvars with
  | [] => exact absurd hfv hne
  | d :: rest =>
    have hd : d = 0 := by
      unfold fvar_lb_val at hlb
      rw [hfv] at hlb
      exact hlb
    rw [hd]
    exact FVarList.MemAbs.head _ _

/-- If fvar_lb_val = k, then all external free vars are ≥ k. -/
theorem extFreeVar_ge_fvar_lb (e : SExpr) (i : Nat)
    (h : Expr.ExtFreeVar e.erase i) :
    i ≥ fvar_lb_val e := by
  have hmem : FVarList.MemAbs i e.fvars := (memAbs_fvars_iff_extFreeVar e i).mpr h
  match hfv : e.fvars with
  | [] => rw [hfv] at hmem; exact absurd hmem (FVarList.not_memAbs_nil _)
  | d :: rest =>
    unfold fvar_lb_val; rw [hfv]
    rw [hfv] at hmem
    exact FVarList.memAbs_ge_head d i rest hmem

/-! ### OSNF definition

`bvar 0` and `const id` are the only leaves. `bvar i` with `i > 0` is
represented as `shift i (bvar 0)`. -/

/-- Outermost-Shift Normal Form. -/
inductive IsOSNF : SExpr → Prop where
  | bvar0 : IsOSNF (bvar 0)
  | const (id : Nat) : IsOSNF (const id)
  | app (f a : SExpr) (hf : IsOSNF f) (ha : IsOSNF a)
      (hlb : fvar_lb_val (app f a) = 0) : IsOSNF (app f a)
  | lam (body : SExpr) (hb : IsOSNF body)
      (hlb : fvar_lb_val (lam body) = 0) : IsOSNF (lam body)
  | shifted (n : Nat) (core : SExpr) (hn : n > 0)
      (hc : IsOSNF core)
      (hlb : core.fvar_lb_val = 0)
      (hfv : core.fvars ≠ []) :
      IsOSNF (shift n core)

/-! ### adjust_child: subtract amount from free variable indices in a child -/

/-- Adjust a child expression by subtracting `amount` from free variable
    indices at or above `cutoff`. Recurses into compound expressions (app/lam).
    Precondition: `BvarsGe e amount cutoff`. -/
def adjust_child (e : SExpr) (amount : Nat) (cutoff : Nat) : SExpr :=
  match e with
  | bvar i => if i ≥ cutoff then bvar (i - amount) else bvar i
  | app f a => app (adjust_child f amount cutoff) (adjust_child a amount cutoff)
  | lam body => lam (adjust_child body amount (cutoff + 1))
  | const id => const id
  | shift k inner =>
    if k ≥ cutoff + amount then
      -- strong case: outer shift handles the drop
      let k' := k - amount
      if k' = 0 then inner else shift k' inner
    else if k ≥ cutoff then
      -- middle case: absorb part of outer shift, recurse with reduced amount
      let inner' := adjust_child inner (amount + cutoff - k) 0
      if cutoff = 0 then inner' else shift cutoff inner'
    else
      -- weak case: recurse into inner with reduced cutoff
      shift k (adjust_child inner amount (cutoff - k))

/-! ### BvarsGe: precondition for adjust_child -/

inductive BvarsGe : SExpr → Nat → Nat → Prop where
  | bvar_lt (i amount cutoff : Nat) (h : i < cutoff) : BvarsGe (bvar i) amount cutoff
  | bvar_ge (i amount cutoff : Nat) (h : i ≥ cutoff + amount) : BvarsGe (bvar i) amount cutoff
  | app (f a : SExpr) (amount cutoff : Nat)
    (hf : BvarsGe f amount cutoff) (ha : BvarsGe a amount cutoff) :
    BvarsGe (app f a) amount cutoff
  | lam (body : SExpr) (amount cutoff : Nat)
    (hb : BvarsGe body amount (cutoff + 1)) :
    BvarsGe (lam body) amount cutoff
  | const_intro (id amount cutoff : Nat) : BvarsGe (const id) amount cutoff
  | shift_ge (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (hka : k ≥ cutoff + amount) :
    BvarsGe (shift k inner) amount cutoff
  | shift_mid (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (hge : k ≥ cutoff) (hlt : k < cutoff + amount)
    (hi : BvarsGe inner (amount + cutoff - k) 0) :
    BvarsGe (shift k inner) amount cutoff
  | shift_lt (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (hlt : k < cutoff) (hi : BvarsGe inner amount (cutoff - k)) :
    BvarsGe (shift k inner) amount cutoff

/-! ### adjust_child preserves erasure (under BvarsGe) -/

theorem adjust_child_erase (e : SExpr) (amount cutoff : Nat)
    (h : BvarsGe e amount cutoff) :
    (adjust_child e amount cutoff).erase.shift amount cutoff = e.erase := by
  induction h with
  | bvar_lt i amount cutoff hlt =>
    show ((if i ≥ cutoff then bvar (i - amount) else bvar i) : SExpr).erase.shift amount cutoff = _
    rw [if_neg (show ¬(i ≥ cutoff) by omega)]
    show (Expr.bvar i).shift amount cutoff = Expr.bvar i
    simp only [Expr.shift, show ¬(i ≥ cutoff) from by omega, ↓reduceIte]
  | bvar_ge i amount cutoff hge =>
    show ((if i ≥ cutoff then bvar (i - amount) else bvar i) : SExpr).erase.shift amount cutoff = _
    rw [if_pos (show i ≥ cutoff by omega)]
    show (Expr.bvar (i - amount)).shift amount cutoff = Expr.bvar i
    simp only [Expr.shift, show i - amount ≥ cutoff from by omega, ↓reduceIte]
    congr 1; omega
  | app f a amount cutoff _hf _ha ihf iha =>
    show (Expr.app (adjust_child f amount cutoff).erase
          (adjust_child a amount cutoff).erase).shift amount cutoff
         = Expr.app f.erase a.erase
    rw [Expr.shift]; congr 1 <;> assumption
  | lam body amount cutoff _hb ih =>
    show (Expr.lam (adjust_child body amount (cutoff + 1)).erase).shift amount cutoff
         = Expr.lam body.erase
    rw [Expr.shift]; exact congrArg Expr.lam ih
  | const_intro id amount cutoff =>
    show (Expr.const id).shift amount cutoff = Expr.const id
    rfl
  | shift_ge k inner amount cutoff hka =>
    simp only [adjust_child, if_pos hka]
    by_cases hk0 : k - amount = 0
    · simp only [hk0, ↓reduceIte]
      have hkeq : k = amount := by omega
      have hc0 : cutoff = 0 := by omega
      subst hkeq; subst hc0
      simp only [erase]
    · rw [if_neg hk0]
      show ((inner.erase.shift (k - amount) 0).shift amount cutoff : Expr) = _
      rw [Expr.shift_shift_comm inner.erase (k - amount) amount 0 cutoff
            (by omega) (by omega)]
      congr 1; omega
  | shift_mid k inner amount cutoff hge hlt hi ih =>
    simp only [adjust_child, if_neg (show ¬(k ≥ cutoff + amount) from by omega),
               if_pos hge]
    by_cases hc0 : cutoff = 0
    · subst hc0
      simp only [↓reduceIte]
      have hshift : amount + 0 - k + k = amount := by omega
      calc (adjust_child inner (amount + 0 - k) 0).erase.shift amount 0
          = (adjust_child inner (amount + 0 - k) 0).erase.shift (amount + 0 - k + k) 0 := by
            rw [hshift]
        _ = ((adjust_child inner (amount + 0 - k) 0).erase.shift (amount + 0 - k) 0).shift k 0 := by
            rw [Expr.shift_shift]
        _ = inner.erase.shift k 0 := by rw [ih]
    · simp only [hc0, ↓reduceIte]
      show (((adjust_child inner (amount + cutoff - k) 0).erase.shift cutoff 0).shift amount cutoff : Expr) = _
      rw [Expr.shift_shift_comm _ cutoff amount 0 cutoff (by omega) (by omega)]
      have hshift : amount + cutoff - k + k = cutoff + amount := by omega
      calc (adjust_child inner (amount + cutoff - k) 0).erase.shift (cutoff + amount) 0
          = (adjust_child inner (amount + cutoff - k) 0).erase.shift (amount + cutoff - k + k) 0 := by
            rw [hshift]
        _ = ((adjust_child inner (amount + cutoff - k) 0).erase.shift (amount + cutoff - k) 0).shift k 0 := by
            rw [Expr.shift_shift]
        _ = inner.erase.shift k 0 := by rw [ih]
  | shift_lt k inner amount cutoff hlt hi ih =>
    simp only [adjust_child, if_neg (show ¬(k ≥ cutoff + amount) from by omega),
               if_neg (show ¬(k ≥ cutoff) from by omega)]
    show (((adjust_child inner amount (cutoff - k)).erase.shift k 0).shift amount cutoff : Expr) = _
    rw [Expr.shift_comm_lt _ k amount cutoff (by omega)]
    exact congrArg (·.shift k 0) ih

/-! ### BvarsGe semantic characterisation -/

/-- From an ExtFreeVar-based semantic bound, produce a structural BvarsGe. -/
theorem bvarsGe_of_extSemantic (e : SExpr) (amount cutoff : Nat)
    (h : ∀ i, Expr.ExtFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount) :
    BvarsGe e amount cutoff := by
  induction e generalizing amount cutoff with
  | bvar j =>
    by_cases hjc : j ≥ cutoff
    · exact BvarsGe.bvar_ge j amount cutoff (h j (Expr.ExtFreeVar.bvar j) hjc)
    · exact BvarsGe.bvar_lt j amount cutoff (by omega)
  | const n => exact BvarsGe.const_intro n amount cutoff
  | app f a ihf iha =>
    refine BvarsGe.app f a amount cutoff ?_ ?_
    · refine ihf amount cutoff ?_
      intro i hi hic
      exact h i (Expr.ExtFreeVar.app_left hi) hic
    · refine iha amount cutoff ?_
      intro i hi hic
      exact h i (Expr.ExtFreeVar.app_right hi) hic
  | lam body ih =>
    refine BvarsGe.lam body amount cutoff ?_
    refine ih amount (cutoff + 1) ?_
    intro i hi hic
    -- From h on (lam body): ExtFreeVar (lam body) (i-1) → i-1 ≥ cutoff → i-1 ≥ cutoff+amount
    have hext : Expr.ExtFreeVar (lam body).erase (i - 1) := by
      show Expr.ExtFreeVar (Expr.lam body.erase) (i - 1)
      have hi1 : (i - 1) + 1 = i := by omega
      rw [← hi1] at hi
      exact Expr.ExtFreeVar.lam hi
    have := h (i - 1) hext (by omega)
    omega
  | shift k inner ih =>
    by_cases hk1 : k ≥ cutoff + amount
    · exact BvarsGe.shift_ge k inner amount cutoff hk1
    by_cases hk2 : k ≥ cutoff
    · refine BvarsGe.shift_mid k inner amount cutoff hk2 (by omega) ?_
      refine ih (amount + cutoff - k) 0 ?_
      intro i hi _
      -- hi : ExtFreeVar inner.erase i, need i ≥ 0 + (amount + cutoff - k)
      -- Use h with i' = i + k: ExtFreeVar (inner.shift k 0) (i+k) → i+k ≥ cutoff
      have hext : Expr.ExtFreeVar (inner.erase.shift k 0) (i + k) := by
        have := Expr.extFreeVar_shift_bwd inner.erase i hi k 0
        simp only [show i ≥ 0 from Nat.zero_le _, ↓reduceIte] at this
        exact this
      have := h (i + k) hext (by omega)
      omega
    · refine BvarsGe.shift_lt k inner amount cutoff (by omega) ?_
      refine ih amount (cutoff - k) ?_
      intro i hi hic
      have hext : Expr.ExtFreeVar (inner.erase.shift k 0) (i + k) := by
        have := Expr.extFreeVar_shift_bwd inner.erase i hi k 0
        simp only [show i ≥ 0 from Nat.zero_le _, ↓reduceIte] at this
        exact this
      have := h (i + k) hext (by omega)
      omega

/-- All external free vars of e.erase are ≥ fvar_lb_val e. -/
theorem bvarsGe_fvar_lb (e : SExpr) : BvarsGe e (fvar_lb_val e) 0 := by
  refine bvarsGe_of_extSemantic e (fvar_lb_val e) 0 ?_
  intro i hi _
  have := extFreeVar_ge_fvar_lb e i hi
  omega

/-! ### Children of compound satisfy BvarsGe -/

theorem bvarsGe_child_app_left (f a : SExpr) :
    BvarsGe f (fvar_lb_val (app f a)) 0 := by
  refine bvarsGe_of_extSemantic f _ 0 ?_
  intro i hi _
  have := extFreeVar_ge_fvar_lb (app f a) i (Expr.ExtFreeVar.app_left hi)
  omega

theorem bvarsGe_child_app_right (f a : SExpr) :
    BvarsGe a (fvar_lb_val (app f a)) 0 := by
  refine bvarsGe_of_extSemantic a _ 0 ?_
  intro i hi _
  have := extFreeVar_ge_fvar_lb (app f a) i (Expr.ExtFreeVar.app_right hi)
  omega

theorem bvarsGe_child_lam (body : SExpr) :
    BvarsGe body (fvar_lb_val (lam body)) 1 := by
  refine bvarsGe_of_extSemantic body _ 1 ?_
  intro i hi hi1
  -- hi : ExtFreeVar body.erase i, hi1 : i ≥ 1
  -- Need: i ≥ 1 + fvar_lb_val (lam body)
  -- ExtFreeVar (lam body).erase (i-1) via lam constructor
  have hext : Expr.ExtFreeVar (lam body).erase (i - 1) := by
    show Expr.ExtFreeVar (Expr.lam body.erase) (i - 1)
    have : (i - 1) + 1 = i := by omega
    rw [← this] at hi
    exact Expr.ExtFreeVar.lam hi
  have := extFreeVar_ge_fvar_lb (lam body) (i - 1) hext
  omega

/-! ### mk_osnf_compound: normalize a compound expression whose children are in OSNF -/

/-- Given a compound expression (app or lam) whose children are already in OSNF,
    compute its OSNF by extracting the common fvar_lb as an outer shift. -/
def mk_osnf_compound (e : SExpr) : SExpr :=
  let lb := e.fvar_lb_val
  if lb = 0 then e
  else
    let core := match e with
      | app f a => app (adjust_child f lb 0) (adjust_child a lb 0)
      | lam body => lam (adjust_child body lb 1)
      | other => other  -- const/bvar/shift: unchanged (unused by callers)
    shift lb core

/-- BvarsGe implies the semantic extent constraint. -/
theorem extFreeVar_of_bvarsGe (e : SExpr) (amount cutoff : Nat)
    (h : BvarsGe e amount cutoff) :
    ∀ i, Expr.ExtFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount := by
  induction h with
  | bvar_lt i amount cutoff hlt =>
    intro j hj hjc
    cases hj with | bvar _ => omega
  | bvar_ge i amount cutoff hge =>
    intro j hj hjc
    cases hj with | bvar _ => omega
  | app f a amount cutoff hf ha ihf iha =>
    intro i hi hic
    change Expr.ExtFreeVar (Expr.app f.erase a.erase) i at hi
    cases hi with
    | app_left h => exact ihf i h hic
    | app_right h => exact iha i h hic
  | lam body amount cutoff hb ih =>
    intro i hi hic
    change Expr.ExtFreeVar (Expr.lam body.erase) i at hi
    cases hi with
    | lam h =>
      have := ih (i + 1) h (by omega)
      omega
  | const_intro id amount cutoff =>
    intro i hi _
    cases hi
  | shift_ge k inner amount cutoff hka =>
    intro i hi _
    have := Expr.extFreeVar_shift_zero_ge inner.erase k i hi
    omega
  | shift_mid k inner amount cutoff hge hlt hi ih =>
    intro i hi_ext hic
    rcases Expr.extFreeVar_shift_extract inner.erase k 0 i hi_ext with
      ⟨hinner, hge'⟩ | ⟨_, hlt0⟩
    · have := ih (i - k) hinner (by omega)
      omega
    · omega
  | shift_lt k inner amount cutoff hlt hi ih =>
    intro i hi_ext hic
    rcases Expr.extFreeVar_shift_extract inner.erase k 0 i hi_ext with
      ⟨hinner, hge'⟩ | ⟨_, hlt0⟩
    · have := ih (i - k) hinner (by omega)
      omega
    · omega

/-! ### Semantic characterisation of adjust_child's external free vars -/

theorem adjust_child_extFreeVar_iff (e : SExpr) (amount cutoff : Nat)
    (hbv : BvarsGe e amount cutoff) (k : Nat) :
    Expr.ExtFreeVar (adjust_child e amount cutoff).erase k ↔
    (k ≥ cutoff ∧ Expr.ExtFreeVar e.erase (k + amount)) ∨
    (k < cutoff ∧ Expr.ExtFreeVar e.erase k) := by
  have hadj := adjust_child_erase e amount cutoff hbv
  constructor
  · intro h
    have hshift := Expr.extFreeVar_shift_bwd _ _ h amount cutoff
    rw [hadj] at hshift
    by_cases hkc : k ≥ cutoff
    · simp only [hkc, ↓reduceIte] at hshift
      exact Or.inl ⟨hkc, hshift⟩
    · simp only [hkc, ↓reduceIte] at hshift
      exact Or.inr ⟨by omega, hshift⟩
  · rintro (⟨hkc, h⟩ | ⟨hkc, h⟩)
    · -- k ≥ cutoff, ExtFreeVar e.erase (k + amount)
      rw [← hadj] at h
      rcases Expr.extFreeVar_shift_extract _ amount cutoff (k + amount) h with
        ⟨hfe, hge⟩ | ⟨hfe, hlt⟩
      · have : k + amount - amount = k := by omega
        rw [this] at hfe
        exact hfe
      · omega
    · -- k < cutoff, ExtFreeVar e.erase k
      rw [← hadj] at h
      rcases Expr.extFreeVar_shift_extract _ amount cutoff k h with
        ⟨_, hge⟩ | ⟨hfe, _⟩
      · omega
      · exact hfe

/-- If fvar_lb_val e = 0, then adjust_child preserves this property. -/
theorem adjust_child_preserves_fvar_lb_zero (e : SExpr) (amount cutoff : Nat)
    (h : fvar_lb_val e = 0) (hbv : BvarsGe e amount cutoff) :
    fvar_lb_val (adjust_child e amount cutoff) = 0 := by
  -- Case analysis: either e is closed or 0 ∈ e.fvars
  match hfv : e.fvars with
  | [] =>
    -- e closed → adj e closed → fvar_lb_val = 0
    have hclosed : ∀ i, ¬ Expr.ExtFreeVar e.erase i :=
      (fvars_empty_iff_no_extFreeVar e).mp hfv
    have hclosed' : ∀ k, ¬ Expr.ExtFreeVar (adjust_child e amount cutoff).erase k := by
      intro k hk
      rw [adjust_child_extFreeVar_iff e amount cutoff hbv k] at hk
      rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩
      · exact hclosed _ h'
      · exact hclosed _ h'
    have : (adjust_child e amount cutoff).fvars = [] :=
      (fvars_empty_iff_no_extFreeVar _).mpr hclosed'
    unfold fvar_lb_val; rw [this]
  | d :: rest =>
    -- d = 0 (from fvar_lb_val = 0)
    have hd : d = 0 := by unfold fvar_lb_val at h; rw [hfv] at h; exact h
    -- ExtFreeVar e.erase 0
    have hext0 : Expr.ExtFreeVar e.erase 0 := by
      apply (memAbs_fvars_iff_extFreeVar e 0).mp
      rw [hfv, hd]; exact FVarList.MemAbs.head _ _
    -- ExtFreeVar (adj e).erase 0
    have hadj0 : Expr.ExtFreeVar (adjust_child e amount cutoff).erase 0 := by
      rw [adjust_child_extFreeVar_iff e amount cutoff hbv 0]
      by_cases hc : cutoff = 0
      · left
        subst hc
        have hsem := extFreeVar_of_bvarsGe e amount 0 hbv 0 hext0 (Nat.zero_le _)
        have ham : amount = 0 := by omega
        subst ham
        refine ⟨by omega, ?_⟩
        simpa using hext0
      · right
        exact ⟨by omega, hext0⟩
    -- fvar_lb_val (adj e) = 0
    have hmem : FVarList.MemAbs 0 (adjust_child e amount cutoff).fvars :=
      (memAbs_fvars_iff_extFreeVar _ 0).mpr hadj0
    match hfv' : (adjust_child e amount cutoff).fvars with
    | [] => exact absurd hmem (by rw [hfv']; exact FVarList.not_memAbs_nil _)
    | d' :: rest' =>
      have hd' : d' = 0 := by
        have hle := FVarList.memAbs_ge_head d' 0 rest' (by rw [← hfv']; exact hmem)
        omega
      unfold fvar_lb_val; rw [hfv']; exact hd'

/-- adjust_child preserves fvars non-emptiness. -/
theorem adjust_child_fvars_nonempty (e : SExpr) (amount cutoff : Nat)
    (hbv : BvarsGe e amount cutoff) (hne : e.fvars ≠ []) :
    (adjust_child e amount cutoff).fvars ≠ [] := by
  intro habs
  have hclosed := (fvars_empty_iff_no_extFreeVar _).mp habs
  apply hne
  apply (fvars_empty_iff_no_extFreeVar _).mpr
  intro i hi
  by_cases hic : i ≥ cutoff
  · have hge := extFreeVar_of_bvarsGe e amount cutoff hbv i hi hic
    have hext : Expr.ExtFreeVar (adjust_child e amount cutoff).erase (i - amount) := by
      rw [adjust_child_extFreeVar_iff e amount cutoff hbv (i - amount)]
      refine Or.inl ⟨by omega, ?_⟩
      have : i - amount + amount = i := by omega
      rw [this]; exact hi
    exact hclosed _ hext
  · have hext : Expr.ExtFreeVar (adjust_child e amount cutoff).erase i := by
      rw [adjust_child_extFreeVar_iff e amount cutoff hbv i]
      exact Or.inr ⟨by omega, hi⟩
    exact hclosed _ hext

/-! ### mk_osnf_compound preserves erasure -/

theorem mk_osnf_compound_erase_app (f a : SExpr) :
    (mk_osnf_compound (app f a)).erase = (app f a).erase := by
  show (let lb := (app f a).fvar_lb_val;
        if lb = 0 then app f a
        else shift lb (app (adjust_child f lb 0) (adjust_child a lb 0))).erase = _
  simp only
  split
  · rfl
  · rename_i hlb
    show (Expr.app (adjust_child f (fvar_lb_val (app f a)) 0).erase
                    (adjust_child a (fvar_lb_val (app f a)) 0).erase).shift _ 0 = _
    rw [Expr.shift]
    congr 1
    · exact adjust_child_erase f _ 0 (bvarsGe_child_app_left f a)
    · exact adjust_child_erase a _ 0 (bvarsGe_child_app_right f a)

theorem mk_osnf_compound_erase_lam (body : SExpr) :
    (mk_osnf_compound (lam body)).erase = (lam body).erase := by
  show (let lb := (lam body).fvar_lb_val;
        if lb = 0 then lam body
        else shift lb (lam (adjust_child body lb 1))).erase = _
  simp only
  split
  · rfl
  · rename_i hlb
    show (Expr.lam (adjust_child body (fvar_lb_val (lam body)) 1).erase).shift _ 0 = _
    rw [Expr.shift]
    congr 1
    exact adjust_child_erase body _ 1 (bvarsGe_child_lam body)

/-! ### mk_osnf_compound produces OSNF -/

/-- The `adjust_child` of an OSNF expression is still OSNF (structure preserved),
    with fvar_lb_val shifted down. -/
theorem adjust_child_preserves_osnf (e : SExpr) (amount cutoff : Nat)
    (h : IsOSNF e) (hbvars : BvarsGe e amount cutoff) :
    IsOSNF (adjust_child e amount cutoff) := by
  induction h generalizing amount cutoff with
  | bvar0 =>
    -- adjust_child (bvar 0) amount cutoff = bvar 0 regardless
    show IsOSNF (if 0 ≥ cutoff then bvar (0 - amount) else bvar 0)
    split
    · show IsOSNF (bvar (0 - amount))
      have : 0 - amount = 0 := by omega
      rw [this]
      exact IsOSNF.bvar0
    · exact IsOSNF.bvar0
  | const id =>
    show IsOSNF (const id)
    exact IsOSNF.const id
  | app f a hf ha hlb ihf iha =>
    have hbvf : BvarsGe f amount cutoff := by
      cases hbvars with | app _ _ _ _ hf' _ => exact hf'
    have hbva : BvarsGe a amount cutoff := by
      cases hbvars with | app _ _ _ _ _ ha' => exact ha'
    have hadjf : IsOSNF (adjust_child f amount cutoff) := ihf amount cutoff hbvf
    have hadja : IsOSNF (adjust_child a amount cutoff) := iha amount cutoff hbva
    have hlb' : fvar_lb_val (adjust_child (app f a) amount cutoff) = 0 :=
      adjust_child_preserves_fvar_lb_zero (app f a) amount cutoff hlb hbvars
    show IsOSNF (app (adjust_child f amount cutoff) (adjust_child a amount cutoff))
    exact IsOSNF.app _ _ hadjf hadja hlb'
  | lam body hb hlb ih =>
    have hbvb : BvarsGe body amount (cutoff + 1) := by
      cases hbvars with | lam _ _ _ hb' => exact hb'
    have hadjb : IsOSNF (adjust_child body amount (cutoff + 1)) := ih amount (cutoff + 1) hbvb
    have hlb' : fvar_lb_val (adjust_child (lam body) amount cutoff) = 0 :=
      adjust_child_preserves_fvar_lb_zero (lam body) amount cutoff hlb hbvars
    show IsOSNF (lam (adjust_child body amount (cutoff + 1)))
    exact IsOSNF.lam _ hadjb hlb'
  | shifted n core hn hc hlb_core hfv_core ih_core =>
    -- adjust_child (shift n core) amount cutoff has 3 branches
    show IsOSNF (if n ≥ cutoff + amount then
                  (let k' := n - amount; if k' = 0 then core else shift k' core)
                else if n ≥ cutoff then
                  (let inner' := adjust_child core (amount + cutoff - n) 0
                   if cutoff = 0 then inner' else shift cutoff inner')
                else shift n (adjust_child core amount (cutoff - n)))
    cases hbvars with
    | shift_ge _ _ _ _ hka =>
      simp only [if_pos hka]
      by_cases hk0 : n - amount = 0
      · simp only [hk0, ↓reduceIte]
        exact hc
      · simp only [hk0, ↓reduceIte]
        exact IsOSNF.shifted (n - amount) core (by omega) hc hlb_core hfv_core
    | shift_mid _ _ _ _ hge hlt hi =>
      simp only [if_neg (show ¬(n ≥ cutoff + amount) from by omega), if_pos hge]
      by_cases hc0 : cutoff = 0
      · subst hc0
        simp only [↓reduceIte]
        -- Output: adjust_child core (amount + 0 - n) 0
        exact ih_core _ _ hi
      · simp only [hc0, ↓reduceIte]
        -- Output: shift cutoff (adjust_child core (amount + cutoff - n) 0)
        have hadjc := ih_core _ _ hi
        have hlb' := adjust_child_preserves_fvar_lb_zero core _ 0 hlb_core hi
        have hfv' := adjust_child_fvars_nonempty core _ 0 hi hfv_core
        exact IsOSNF.shifted cutoff _ (by omega) hadjc hlb' hfv'
    | shift_lt _ _ _ _ hlt hi =>
      simp only [if_neg (show ¬(n ≥ cutoff + amount) from by omega),
                 if_neg (show ¬(n ≥ cutoff) from by omega)]
      -- Output: shift n (adjust_child core amount (cutoff - n))
      have hadjc := ih_core amount (cutoff - n) hi
      have hlb' := adjust_child_preserves_fvar_lb_zero core amount (cutoff - n) hlb_core hi
      have hfv' := adjust_child_fvars_nonempty core amount (cutoff - n) hi hfv_core
      exact IsOSNF.shifted n _ hn hadjc hlb' hfv'

theorem mk_osnf_compound_app_isOSNF (f a : SExpr) (hf : IsOSNF f) (ha : IsOSNF a) :
    IsOSNF (mk_osnf_compound (app f a)) := by
  sorry

theorem mk_osnf_compound_lam_isOSNF (body : SExpr) (hb : IsOSNF body) :
    IsOSNF (mk_osnf_compound (lam body)) := by
  sorry

/-! ### to_osnf: compute the OSNF of an expression (recursive, bottom-up) -/

/-- Compute the OSNF of an expression.
    - `bvar 0`: already in OSNF.
    - `bvar i` for i > 0: represented as `shift i (bvar 0)`.
    - `const id`: already in OSNF.
    - `app f a` / `lam body`: normalize children, then extract `fvar_lb` via `mk_osnf_compound`.
    - `shift k inner`: collapse with inner's OSNF. -/
def to_osnf : SExpr → SExpr
  | bvar i => if i = 0 then bvar 0 else shift i (bvar 0)
  | const id => const id
  | app f a => mk_osnf_compound (app f.to_osnf a.to_osnf)
  | lam body => mk_osnf_compound (lam body.to_osnf)
  | shift k inner =>
    match inner.to_osnf with
    | shift m core => if k + m = 0 then core else shift (k + m) core
    | e =>
      if k = 0 then e
      else match e.fvars with
        | [] => e
        | _ => shift k e

/-! ### Main theorems

`to_osnf_erase`, `osnf_unique`, `to_osnf_idempotent`, `equiv_iff_osnf_eq` are
fully proved. `to_osnf_isOSNF` still depends on the isOSNF preservation of
`adjust_child`/`mk_osnf_compound`, which are `sorry` for now. -/

/-- `to_osnf e` is in OSNF. -/
theorem to_osnf_isOSNF (e : SExpr) : IsOSNF (to_osnf e) := sorry

/-- `to_osnf` preserves denotation. -/
theorem to_osnf_erase (e : SExpr) : (to_osnf e).erase = e.erase := by
  induction e with
  | bvar i =>
    simp only [to_osnf]
    split
    · rename_i hi0; subst hi0; rfl
    · rename_i hi0
      show (Expr.bvar 0).shift i 0 = Expr.bvar i
      simp only [Expr.shift, show 0 ≥ 0 from Nat.zero_le _, ↓reduceIte, Nat.zero_add]
  | const id => rfl
  | app f a ihf iha =>
    show (mk_osnf_compound (app f.to_osnf a.to_osnf)).erase = Expr.app f.erase a.erase
    rw [mk_osnf_compound_erase_app]
    show Expr.app (f.to_osnf).erase (a.to_osnf).erase = Expr.app f.erase a.erase
    rw [ihf, iha]
  | lam body ih =>
    show (mk_osnf_compound (lam body.to_osnf)).erase = Expr.lam body.erase
    rw [mk_osnf_compound_erase_lam]
    show Expr.lam (body.to_osnf).erase = Expr.lam body.erase
    rw [ih]
  | shift k inner ih =>
    show (match inner.to_osnf with
      | shift m core => if k + m = 0 then core else shift (k + m) core
      | e => if k = 0 then e else match e.fvars with | [] => e | _ => shift k e).erase
         = inner.erase.shift k 0
    split
    · rename_i m core heq
      have ih' : (shift m core).erase = inner.erase := by rw [← heq]; exact ih
      split
      · rename_i hkm
        have hk0 : k = 0 := by omega
        have hm0 : m = 0 := by omega
        subst hk0; subst hm0
        rw [SExpr.erase, Expr.shift_zero] at ih'
        rw [ih', Expr.shift_zero]
      · rename_i hkm
        rw [SExpr.erase]
        rw [SExpr.erase] at ih'
        rw [← ih', Expr.shift_shift]
        congr 1; omega
    · rename_i e hnotShift
      split
      · rename_i hk0; subst hk0
        rw [ih, Expr.shift_zero]
      · rename_i hk0
        -- e = inner.to_osnf, not a shift. match e.fvars
        have : ∀ (fvs : FVarList), inner.to_osnf.fvars = fvs →
            (match fvs with | [] => inner.to_osnf | _ => shift k (inner.to_osnf)).erase
              = inner.erase.shift k 0 := by
          intro fvs hfvs
          match fvs with
          | [] =>
            show inner.to_osnf.erase = inner.erase.shift k 0
            have hclosed := (fvars_empty_iff_no_extFreeVar inner.to_osnf).mp hfvs
            rw [← ih]
            exact (Expr.shift_eq_of_no_extFreeVar inner.to_osnf.erase k hclosed).symm
          | d :: rest =>
            show (shift k inner.to_osnf).erase = inner.erase.shift k 0
            rw [SExpr.erase, ih]
        exact this _ rfl

-- Helper for osnf_unique: a shifted core has external free var at n.
private theorem shifted_has_extFreeVar_n (n : Nat) (core : SExpr)
    (hc : IsOSNF core) (hlb : core.fvar_lb_val = 0) (hfv : core.fvars ≠ []) :
    Expr.ExtFreeVar (core.erase.shift n 0) n := by
  have hc0 := fvar_lb_zero_has_extFreeVar_zero core hlb hfv
  have := Expr.extFreeVar_shift_bwd core.erase 0 hc0 n 0
  simp only [show 0 ≥ 0 from Nat.zero_le _, ↓reduceIte, Nat.zero_add] at this
  exact this

-- Non-shift OSNF matched against shift n core: contradiction.
private theorem osnf_nonshift_ne_shifted {e : SExpr} (he : IsOSNF e)
    (hlbE : fvar_lb_val e = 0 ∨ e.fvars = [])
    {n : Nat} (hn : n > 0) {core : SExpr}
    (hc : IsOSNF core) (hlb : core.fvar_lb_val = 0) (hfv : core.fvars ≠ [])
    (heq : e.erase = (shift n core).erase) : False := by
  simp only [erase] at heq
  have hs : Expr.ExtFreeVar (core.erase.shift n 0) n :=
    shifted_has_extFreeVar_n n core hc hlb hfv
  rcases hlbE with hlbE | hfvE
  · -- e has ext fvar at 0 (if non-closed) or is closed
    by_cases hfvE2 : e.fvars = []
    · have hnone : ∀ i, ¬ Expr.ExtFreeVar e.erase i :=
        (fvars_empty_iff_no_extFreeVar _).mp hfvE2
      rw [heq] at hnone
      exact hnone n hs
    · have h0 : Expr.ExtFreeVar e.erase 0 :=
        fvar_lb_zero_has_extFreeVar_zero e hlbE hfvE2
      rw [heq] at h0
      have := Expr.extFreeVar_shift_zero_ge core.erase n 0 h0
      omega
  · have hnone : ∀ i, ¬ Expr.ExtFreeVar e.erase i :=
      (fvars_empty_iff_no_extFreeVar _).mp hfvE
    rw [heq] at hnone
    exact hnone n hs

/-- **Uniqueness of OSNF**: If two expressions in OSNF denote the same term,
    they are syntactically equal. -/
theorem osnf_unique (e₁ e₂ : SExpr) (h₁ : IsOSNF e₁) (h₂ : IsOSNF e₂)
    (heq : e₁.erase = e₂.erase) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | bvar0 =>
    cases h₂ with
    | bvar0 => rfl
    | const id => simp [erase] at heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hlb hfv =>
      exfalso
      refine osnf_nonshift_ne_shifted IsOSNF.bvar0 (Or.inl rfl) hn hc hlb hfv ?_
      exact heq
  | const id =>
    cases h₂ with
    | bvar0 => simp [erase] at heq
    | const id' =>
      simp only [erase, Expr.const.injEq] at heq
      exact congrArg _ heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hlb hfv =>
      exfalso
      refine osnf_nonshift_ne_shifted (IsOSNF.const id) (Or.inr ?_) hn hc hlb hfv heq
      rfl
  | app f₁ a₁ hf₁ ha₁ hlb₁ ihf iha =>
    cases h₂ with
    | bvar0 => simp [erase] at heq
    | const id => simp [erase] at heq
    | app f₂ a₂ hf₂ ha₂ hlb₂ =>
      simp only [erase, Expr.app.injEq] at heq
      have hfe := ihf f₂ hf₂ heq.1
      have hae := iha a₂ ha₂ heq.2
      subst hfe; subst hae; rfl
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hlb hfv =>
      exfalso
      exact osnf_nonshift_ne_shifted
        (IsOSNF.app f₁ a₁ hf₁ ha₁ hlb₁) (Or.inl hlb₁) hn hc hlb hfv heq
  | lam body₁ hb₁ hlb₁ ih =>
    cases h₂ with
    | bvar0 => simp [erase] at heq
    | const id => simp [erase] at heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body₂ hb₂ hlb₂ =>
      simp only [erase, Expr.lam.injEq] at heq
      have := ih body₂ hb₂ heq
      subst this; rfl
    | shifted n core hn hc hlb hfv =>
      exfalso
      exact osnf_nonshift_ne_shifted
        (IsOSNF.lam body₁ hb₁ hlb₁) (Or.inl hlb₁) hn hc hlb hfv heq
  | shifted n₁ core₁ hn₁ hc₁ hlb₁ hfv₁ ih_core =>
    cases h₂ with
    | bvar0 =>
      exfalso
      refine osnf_nonshift_ne_shifted IsOSNF.bvar0 (Or.inl rfl) hn₁ hc₁ hlb₁ hfv₁ ?_
      exact heq.symm
    | const id =>
      exfalso
      refine osnf_nonshift_ne_shifted (IsOSNF.const id) (Or.inr rfl) hn₁ hc₁ hlb₁ hfv₁ ?_
      exact heq.symm
    | app f a hf ha hlb =>
      exfalso
      exact osnf_nonshift_ne_shifted
        (IsOSNF.app f a hf ha hlb) (Or.inl hlb) hn₁ hc₁ hlb₁ hfv₁ heq.symm
    | lam body hb hlb =>
      exfalso
      exact osnf_nonshift_ne_shifted
        (IsOSNF.lam body hb hlb) (Or.inl hlb) hn₁ hc₁ hlb₁ hfv₁ heq.symm
    | shifted n₂ core₂ hn₂ hc₂ hlb₂ hfv₂ =>
      simp only [erase] at heq
      have hs1 := shifted_has_extFreeVar_n n₁ core₁ hc₁ hlb₁ hfv₁
      have hs2 := shifted_has_extFreeVar_n n₂ core₂ hc₂ hlb₂ hfv₂
      rw [heq] at hs1
      rw [← heq] at hs2
      have h12 : n₁ ≥ n₂ := Expr.extFreeVar_shift_zero_ge core₂.erase n₂ n₁ hs1
      have h21 : n₂ ≥ n₁ := Expr.extFreeVar_shift_zero_ge core₁.erase n₁ n₂ hs2
      have hneq : n₁ = n₂ := by omega
      subst hneq
      have hceq : core₁.erase = core₂.erase :=
        Expr.shift_injective n₁ 0 _ _ heq
      have := ih_core core₂ hc₂ hceq
      subst this; rfl

/-- **Corollary**: `to_osnf` is idempotent. -/
theorem to_osnf_idempotent (e : SExpr) : to_osnf (to_osnf e) = to_osnf e :=
  osnf_unique _ _ (to_osnf_isOSNF _) (to_osnf_isOSNF _) (to_osnf_erase _)

/-- **Corollary**: Two expressions are shift-equivalent iff they have the same OSNF. -/
theorem equiv_iff_osnf_eq (e₁ e₂ : SExpr) :
    equiv e₁ e₂ ↔ to_osnf e₁ = to_osnf e₂ := by
  constructor
  · intro heq
    have h1 := to_osnf_isOSNF e₁
    have h2 := to_osnf_isOSNF e₂
    have he1 := to_osnf_erase e₁
    have he2 := to_osnf_erase e₂
    exact osnf_unique _ _ h1 h2 (by rw [he1, he2]; exact heq)
  · intro heq
    unfold equiv
    rw [← to_osnf_erase e₁, ← to_osnf_erase e₂, heq]

end SExpr
