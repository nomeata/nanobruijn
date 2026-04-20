/-
# OSNF (Outermost-Shift Normal Form) — formal model

All five main theorems are proved: `to_osnf_erase`, `to_osnf_isOSNF`,
`osnf_unique`, `to_osnf_idempotent`, `equiv_iff_osnf_eq`. Zero sorries, zero
axioms.

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
  induction e generalizing c <;> grind [shift]

theorem shift_shift (e : Expr) (j k c : Nat) :
    (e.shift j c).shift k c = e.shift (j + k) c := by
  induction e generalizing c <;> grind [shift]

theorem shift_shift_comm (e : Expr) (j k c d : Nat) (hcd : c ≤ d) (hdj : d ≤ c + j) :
    (e.shift j c).shift k d = e.shift (j + k) c := by
  induction e generalizing c d <;> grind [shift]

private theorem shift_comm_lt_gen (e : Expr) (k amount cutoff base : Nat) (hlt : k < cutoff) :
    (e.shift k base).shift amount (cutoff + base) =
    (e.shift amount (cutoff - k + base)).shift k base := by
  induction e generalizing k cutoff base <;> grind [shift]

theorem shift_comm_lt (e : Expr) (k amount cutoff : Nat) (hlt : k < cutoff) :
    (e.shift k 0).shift amount cutoff = (e.shift amount (cutoff - k)).shift k 0 := by
  have h := shift_comm_lt_gen e k amount cutoff 0 hlt
  grind

/-- Free-variable predicate on de Bruijn expressions. `HasFreeVar e k` iff
    `e` has a free variable at external index `k` (the standard notion:
    under `lam`, the body's `k+1` becomes the lambda's `k`). -/
inductive HasFreeVar : Expr → Nat → Prop where
  | bvar (i : Nat) : HasFreeVar (bvar i) i
  | app_left {f a : Expr} {k : Nat} (h : HasFreeVar f k) : HasFreeVar (app f a) k
  | app_right {f a : Expr} {k : Nat} (h : HasFreeVar a k) : HasFreeVar (app f a) k
  | lam {body : Expr} {k : Nat} (h : HasFreeVar body (k + 1)) : HasFreeVar (lam body) k

/-! Case-analysis lemmas that teach `grind` how to decompose `HasFreeVar`. -/

@[grind =] theorem hasFreeVar_bvar_iff (i j : Nat) : HasFreeVar (bvar j) i ↔ i = j :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ HasFreeVar.bvar _⟩

@[grind] theorem hasFreeVar_bvar_self (i : Nat) : HasFreeVar (bvar i) i := HasFreeVar.bvar _

@[grind =] theorem hasFreeVar_app_iff (f a : Expr) (k : Nat) :
    HasFreeVar (app f a) k ↔ HasFreeVar f k ∨ HasFreeVar a k :=
  ⟨fun h => by cases h with | app_left h => exact Or.inl h | app_right h => exact Or.inr h,
   fun h => h.elim HasFreeVar.app_left HasFreeVar.app_right⟩

@[grind =] theorem hasFreeVar_lam_iff (body : Expr) (k : Nat) :
    HasFreeVar (lam body) k ↔ HasFreeVar body (k + 1) :=
  ⟨fun h => by cases h; assumption, HasFreeVar.lam⟩

@[grind] theorem hasFreeVar_const (id k : Nat) : ¬ HasFreeVar (const id) k := by
  intro h; cases h

/-- Stronger forward decomposition of HasFreeVar on a shift. -/
theorem hasFreeVar_shift_extract (e : Expr) (n c i : Nat) :
    HasFreeVar (e.shift n c) i →
    (HasFreeVar e (i - n) ∧ i ≥ n + c) ∨ (HasFreeVar e i ∧ i < c) := by
  induction e generalizing c i <;> grind [shift]

/-- Shift preserves / creates external bvars with a cutoff-parametrized predictable pattern. -/
theorem hasFreeVar_shift_fwd (e : Expr) (n c k : Nat) :
    HasFreeVar (e.shift n c) k → k ≥ n + c ∨ k < c := by
  induction e generalizing c k <;> grind [shift]

/-- Specialised to cutoff 0. -/
theorem hasFreeVar_shift_zero_ge (e : Expr) (n k : Nat)
    (h : HasFreeVar (e.shift n 0) k) : k ≥ n := by
  have := hasFreeVar_shift_fwd e n 0 k h; omega

/-- Shifting back: external bvar j in e gives external bvar j+n (if j ≥ c) in
    e.shift n c. -/
theorem hasFreeVar_shift_bwd (e : Expr) (j : Nat) (h : HasFreeVar e j) (n c : Nat) :
    HasFreeVar (e.shift n c) (if j ≥ c then j + n else j) := by
  induction h generalizing c <;> grind [shift]

/-- If all external free vars of e are below c, shift at cutoff c is a no-op. -/
theorem shift_eq_of_hasFreeVars_lt (e : Expr) (k c : Nat)
    (h : ∀ j, HasFreeVar e j → j < c) : e.shift k c = e := by
  induction e generalizing c with
  | bvar i =>
    have := h i (HasFreeVar.bvar _)
    grind [shift]
  | app f a ihf iha =>
    grind [shift]
  | lam body ih =>
    refine congrArg Expr.lam (ih (c + 1) ?_)
    intro j hj; have := h (j - 1); grind
  | const _ => rfl

/-- Specialisation: closed (no HasFreeVar) expression shift at cutoff 0 is a no-op. -/
theorem shift_eq_of_no_hasFreeVar (e : Expr) (k : Nat)
    (h : ∀ j, ¬ HasFreeVar e j) : e.shift k 0 = e :=
  shift_eq_of_hasFreeVars_lt e k 0 (fun j hj => absurd hj (h j))

theorem shift_injective (k c : Nat) : ∀ (e₁ e₂ : Expr),
    e₁.shift k c = e₂.shift k c → e₁ = e₂ := by
  intro e₁
  induction e₁ generalizing c <;> intro e₂ h <;> cases e₂ <;> grind [shift]

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

theorem memAbs_fvars_iff_hasFreeVar (e : SExpr) (i : Nat) :
    FVarList.MemAbs i e.fvars ↔ Expr.HasFreeVar e.erase i := by
  induction e generalizing i with
  | bvar j => simp only [fvars, erase]; grind [FVarList.memAbs_cons_cases, FVarList.not_memAbs_nil, FVarList.MemAbs.head]
  | const n =>
    simp only [fvars, erase]
    exact ⟨fun h => absurd h (FVarList.not_memAbs_nil _), fun h => by cases h⟩
  | app f a ihf iha =>
    simp only [fvars, erase, FVarList.memAbs_union_iff, ihf, iha]
    grind
  | lam body ih =>
    simp only [fvars, erase, FVarList.memAbs_unbind_iff, ih]
    grind
  | shift k inner ih =>
    simp only [fvars, erase, FVarList.memAbs_shift_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hf : Expr.HasFreeVar inner.erase j := (ih j).mp hj
      have := Expr.hasFreeVar_shift_bwd inner.erase j hf k 0
      simpa using this
    · intro h
      rcases Expr.hasFreeVar_shift_extract inner.erase k 0 i h with ⟨hfe, hge⟩ | ⟨_, hlt⟩
      · exact ⟨i - k, (ih (i - k)).mpr hfe, by omega⟩
      · omega

/-- `e.fvars = []` iff the erasure has no external free bvars. -/
theorem fvars_empty_iff_no_hasFreeVar (e : SExpr) :
    e.fvars = [] ↔ ∀ i, ¬ Expr.HasFreeVar e.erase i := by
  constructor
  · intro h i hext
    have := (memAbs_fvars_iff_hasFreeVar e i).mpr hext
    grind [FVarList.not_memAbs_nil]
  · intro h
    match hfv : e.fvars with
    | [] => rfl
    | d :: rest =>
      have : FVarList.MemAbs d e.fvars := by rw [hfv]; exact FVarList.MemAbs.head _ _
      grind [memAbs_fvars_iff_hasFreeVar]

/-- If fvar_lb_val is 0 and fvars is non-empty, 0 is an external free var. -/
theorem fvar_lb_zero_has_hasFreeVar_zero (e : SExpr)
    (hlb : fvar_lb_val e = 0) (hne : e.fvars ≠ []) :
    Expr.HasFreeVar e.erase 0 := by
  apply (memAbs_fvars_iff_hasFreeVar e 0).mp
  match hfv : e.fvars with
  | [] => exact absurd hfv hne
  | d :: rest =>
    have hd : d = 0 := by unfold fvar_lb_val at hlb; rw [hfv] at hlb; exact hlb
    grind [FVarList.MemAbs.head]

/-- If fvar_lb_val = k, then all external free vars are ≥ k. -/
theorem hasFreeVar_ge_fvar_lb (e : SExpr) (i : Nat)
    (h : Expr.HasFreeVar e.erase i) :
    i ≥ fvar_lb_val e := by
  have hmem : FVarList.MemAbs i e.fvars := (memAbs_fvars_iff_hasFreeVar e i).mpr h
  match hfv : e.fvars with
  | [] => grind [FVarList.not_memAbs_nil]
  | d :: rest =>
    have := FVarList.memAbs_ge_head d i rest (by rw [← hfv]; exact hmem)
    unfold fvar_lb_val; rw [hfv]; exact this

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
  | bvar_lt i amount cutoff hlt => grind [adjust_child, erase, Expr.shift]
  | bvar_ge i amount cutoff hge => grind [adjust_child, erase, Expr.shift]
  | app f a amount cutoff _hf _ha ihf iha => grind [adjust_child, erase, Expr.shift]
  | lam body amount cutoff _hb ih => grind [adjust_child, erase, Expr.shift]
  | const_intro id amount cutoff => rfl
  | shift_ge k inner amount cutoff hka =>
    simp only [adjust_child, if_pos hka]
    by_cases hk0 : k - amount = 0
    · have hkeq : k = amount := by omega
      have hc0 : cutoff = 0 := by omega
      subst hkeq; subst hc0; grind [erase]
    · rw [if_neg hk0]
      show ((inner.erase.shift (k - amount) 0).shift amount cutoff : Expr) = _
      rw [Expr.shift_shift_comm inner.erase (k - amount) amount 0 cutoff (by omega) (by omega)]
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

/-- From an HasFreeVar-based semantic bound, produce a structural BvarsGe. -/
theorem bvarsGe_of_extSemantic (e : SExpr) (amount cutoff : Nat)
    (h : ∀ i, Expr.HasFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount) :
    BvarsGe e amount cutoff := by
  induction e generalizing amount cutoff with
  | bvar j =>
    by_cases hjc : j ≥ cutoff
    · exact BvarsGe.bvar_ge j amount cutoff (h j (Expr.HasFreeVar.bvar j) hjc)
    · exact BvarsGe.bvar_lt j amount cutoff (by omega)
  | const n => exact BvarsGe.const_intro n amount cutoff
  | app f a ihf iha =>
    refine BvarsGe.app f a amount cutoff (ihf amount cutoff ?_) (iha amount cutoff ?_)
    · grind [Expr.HasFreeVar.app_left, erase]
    · grind [Expr.HasFreeVar.app_right, erase]
  | lam body ih =>
    refine BvarsGe.lam body amount cutoff (ih amount (cutoff + 1) ?_)
    intro i hi hic
    have hext : Expr.HasFreeVar (lam body).erase (i - 1) := by
      have : (i - 1) + 1 = i := by omega
      exact Expr.HasFreeVar.lam (this ▸ hi)
    have := h (i - 1) hext (by omega); omega
  | shift k inner ih =>
    by_cases hk1 : k ≥ cutoff + amount
    · exact BvarsGe.shift_ge k inner amount cutoff hk1
    by_cases hk2 : k ≥ cutoff
    · refine BvarsGe.shift_mid k inner amount cutoff hk2 (by omega) ?_
      refine ih (amount + cutoff - k) 0 ?_
      intro i hi _
      have hext : Expr.HasFreeVar (inner.erase.shift k 0) (i + k) := by
        have := Expr.hasFreeVar_shift_bwd inner.erase i hi k 0
        simp only [show i ≥ 0 from Nat.zero_le _, ↓reduceIte] at this
        exact this
      have := h (i + k) hext (by omega)
      omega
    · refine BvarsGe.shift_lt k inner amount cutoff (by omega) ?_
      refine ih amount (cutoff - k) ?_
      intro i hi hic
      have hext : Expr.HasFreeVar (inner.erase.shift k 0) (i + k) := by
        have := Expr.hasFreeVar_shift_bwd inner.erase i hi k 0
        simp only [show i ≥ 0 from Nat.zero_le _, ↓reduceIte] at this
        exact this
      have := h (i + k) hext (by omega)
      omega

/-- All external free vars of e.erase are ≥ fvar_lb_val e. -/
theorem bvarsGe_fvar_lb (e : SExpr) : BvarsGe e (fvar_lb_val e) 0 := by
  refine bvarsGe_of_extSemantic e (fvar_lb_val e) 0 ?_
  intro i hi _
  have := hasFreeVar_ge_fvar_lb e i hi
  omega

/-! ### Children of compound satisfy BvarsGe -/

theorem bvarsGe_child_app_left (f a : SExpr) :
    BvarsGe f (fvar_lb_val (app f a)) 0 := by
  refine bvarsGe_of_extSemantic f _ 0 ?_
  intro i hi _
  have := hasFreeVar_ge_fvar_lb (app f a) i (Expr.HasFreeVar.app_left hi)
  omega

theorem bvarsGe_child_app_right (f a : SExpr) :
    BvarsGe a (fvar_lb_val (app f a)) 0 := by
  refine bvarsGe_of_extSemantic a _ 0 ?_
  intro i hi _
  have := hasFreeVar_ge_fvar_lb (app f a) i (Expr.HasFreeVar.app_right hi)
  omega

theorem bvarsGe_child_lam (body : SExpr) :
    BvarsGe body (fvar_lb_val (lam body)) 1 := by
  refine bvarsGe_of_extSemantic body _ 1 ?_
  intro i hi hi1
  have hext : Expr.HasFreeVar (lam body).erase (i - 1) := by
    have : (i - 1) + 1 = i := by omega
    exact Expr.HasFreeVar.lam (this ▸ hi)
  have := hasFreeVar_ge_fvar_lb (lam body) (i - 1) hext; omega

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
theorem hasFreeVar_of_bvarsGe (e : SExpr) (amount cutoff : Nat)
    (h : BvarsGe e amount cutoff) :
    ∀ i, Expr.HasFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount := by
  induction h with
  | bvar_lt i amount cutoff hlt => grind [erase]
  | bvar_ge i amount cutoff hge => grind [erase]
  | app f a amount cutoff hf ha ihf iha => grind [erase]
  | lam body amount cutoff hb ih =>
    intro i hi hic
    change Expr.HasFreeVar (Expr.lam body.erase) i at hi
    cases hi with | lam h => have := ih (i + 1) h (by omega); omega
  | const_intro id amount cutoff => grind [erase]
  | shift_ge k inner amount cutoff hka =>
    intro i hi _
    have := Expr.hasFreeVar_shift_zero_ge inner.erase k i hi; omega
  | shift_mid k inner amount cutoff hge hlt hi ih =>
    intro i hi_ext hic
    rcases Expr.hasFreeVar_shift_extract inner.erase k 0 i hi_ext with
      ⟨hinner, hge'⟩ | ⟨_, hlt0⟩
    · have := ih (i - k) hinner (by omega); omega
    · omega
  | shift_lt k inner amount cutoff hlt hi ih =>
    intro i hi_ext hic
    rcases Expr.hasFreeVar_shift_extract inner.erase k 0 i hi_ext with
      ⟨hinner, hge'⟩ | ⟨_, hlt0⟩
    · have := ih (i - k) hinner (by omega); omega
    · omega

/-! ### Semantic characterisation of adjust_child's external free vars -/

theorem adjust_child_hasFreeVar_iff (e : SExpr) (amount cutoff : Nat)
    (hbv : BvarsGe e amount cutoff) (k : Nat) :
    Expr.HasFreeVar (adjust_child e amount cutoff).erase k ↔
    (k ≥ cutoff ∧ Expr.HasFreeVar e.erase (k + amount)) ∨
    (k < cutoff ∧ Expr.HasFreeVar e.erase k) := by
  have hadj := adjust_child_erase e amount cutoff hbv
  constructor
  · intro h
    have hshift := Expr.hasFreeVar_shift_bwd _ _ h amount cutoff
    rw [hadj] at hshift
    by_cases hkc : k ≥ cutoff
    · simp only [hkc, ↓reduceIte] at hshift; exact Or.inl ⟨hkc, hshift⟩
    · simp only [hkc, ↓reduceIte] at hshift; exact Or.inr ⟨by omega, hshift⟩
  · rintro (⟨hkc, h⟩ | ⟨hkc, h⟩)
    · rw [← hadj] at h
      rcases Expr.hasFreeVar_shift_extract _ amount cutoff (k + amount) h with
        ⟨hfe, _⟩ | ⟨_, _⟩
      · have heq : k + amount - amount = k := by omega
        rw [heq] at hfe; exact hfe
      · omega
    · rw [← hadj] at h
      rcases Expr.hasFreeVar_shift_extract _ amount cutoff k h with
        ⟨_, _⟩ | ⟨hfe, _⟩
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
    have hclosed : ∀ i, ¬ Expr.HasFreeVar e.erase i :=
      (fvars_empty_iff_no_hasFreeVar e).mp hfv
    have hclosed' : ∀ k, ¬ Expr.HasFreeVar (adjust_child e amount cutoff).erase k := by
      intro k hk
      rw [adjust_child_hasFreeVar_iff e amount cutoff hbv k] at hk
      rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩
      · exact hclosed _ h'
      · exact hclosed _ h'
    have : (adjust_child e amount cutoff).fvars = [] :=
      (fvars_empty_iff_no_hasFreeVar _).mpr hclosed'
    unfold fvar_lb_val; rw [this]
  | d :: rest =>
    -- d = 0 (from fvar_lb_val = 0)
    have hd : d = 0 := by unfold fvar_lb_val at h; rw [hfv] at h; exact h
    -- HasFreeVar e.erase 0
    have hext0 : Expr.HasFreeVar e.erase 0 := by
      apply (memAbs_fvars_iff_hasFreeVar e 0).mp
      rw [hfv, hd]; exact FVarList.MemAbs.head _ _
    -- HasFreeVar (adj e).erase 0
    have hadj0 : Expr.HasFreeVar (adjust_child e amount cutoff).erase 0 := by
      rw [adjust_child_hasFreeVar_iff e amount cutoff hbv 0]
      by_cases hc : cutoff = 0
      · left
        subst hc
        have hsem := hasFreeVar_of_bvarsGe e amount 0 hbv 0 hext0 (Nat.zero_le _)
        have ham : amount = 0 := by omega
        subst ham
        refine ⟨by omega, ?_⟩
        simpa using hext0
      · right
        exact ⟨by omega, hext0⟩
    -- fvar_lb_val (adj e) = 0
    have hmem : FVarList.MemAbs 0 (adjust_child e amount cutoff).fvars :=
      (memAbs_fvars_iff_hasFreeVar _ 0).mpr hadj0
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
  have hclosed := (fvars_empty_iff_no_hasFreeVar _).mp habs
  apply hne
  apply (fvars_empty_iff_no_hasFreeVar _).mpr
  intro i hi
  by_cases hic : i ≥ cutoff
  · have hge := hasFreeVar_of_bvarsGe e amount cutoff hbv i hi hic
    have hext : Expr.HasFreeVar (adjust_child e amount cutoff).erase (i - amount) := by
      rw [adjust_child_hasFreeVar_iff e amount cutoff hbv (i - amount)]
      refine Or.inl ⟨by omega, ?_⟩
      have : i - amount + amount = i := by omega
      rw [this]; exact hi
    exact hclosed _ hext
  · have hext : Expr.HasFreeVar (adjust_child e amount cutoff).erase i := by
      rw [adjust_child_hasFreeVar_iff e amount cutoff hbv i]
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

-- Helper: head of fvars is an element.
private theorem memAbs_fvar_lb_val (e : SExpr) (hne : e.fvars ≠ []) :
    FVarList.MemAbs (fvar_lb_val e) e.fvars := by
  match hfv : e.fvars with
  | [] => exact absurd hfv hne
  | d :: rest =>
    have heq : fvar_lb_val e = d := by unfold fvar_lb_val; rw [hfv]
    rw [heq]; exact FVarList.MemAbs.head _ _

-- Helper: when fvar_lb_val > 0, get HasFreeVar at fvar_lb_val.
private theorem hasFreeVar_at_fvar_lb_val (e : SExpr) (hne : e.fvars ≠ []) :
    Expr.HasFreeVar e.erase (fvar_lb_val e) :=
  (memAbs_fvars_iff_hasFreeVar _ _).mp (memAbs_fvar_lb_val e hne)

-- Helper: if HasFreeVar (adj e).erase 0, then (adj e).fvar_lb_val = 0.
private theorem fvar_lb_val_zero_of_hasFreeVar_zero (e' : SExpr)
    (h : Expr.HasFreeVar e'.erase 0) : fvar_lb_val e' = 0 := by
  have hmem : FVarList.MemAbs 0 e'.fvars :=
    (memAbs_fvars_iff_hasFreeVar _ _).mpr h
  match hfv : e'.fvars with
  | [] => exact absurd (hfv ▸ hmem) (FVarList.not_memAbs_nil _)
  | d' :: rest' =>
    have hge := FVarList.memAbs_ge_head d' 0 rest' (hfv ▸ hmem)
    have hd'0 : d' = 0 := by omega
    show (match e'.fvars with | [] => 0 | d :: _ => d) = 0
    rw [hfv]; exact hd'0

-- Helper: HasFreeVar e.erase i → e.fvars ≠ [].
private theorem fvars_ne_nil_of_hasFreeVar (e' : SExpr) (i : Nat)
    (h : Expr.HasFreeVar e'.erase i) : e'.fvars ≠ [] := by
  intro habs; exact (fvars_empty_iff_no_hasFreeVar _).mp habs i h


theorem mk_osnf_compound_app_isOSNF (f a : SExpr) (hf : IsOSNF f) (ha : IsOSNF a) :
    IsOSNF (mk_osnf_compound (app f a)) := by
  show IsOSNF (let lb := fvar_lb_val (app f a);
               if lb = 0 then app f a
               else shift lb (app (adjust_child f lb 0) (adjust_child a lb 0)))
  simp only
  split
  · rename_i hlb; exact IsOSNF.app _ _ hf ha hlb
  · rename_i hlb
    have hlb_pos : fvar_lb_val (app f a) > 0 := by omega
    have hne : (app f a).fvars ≠ [] := by
      intro habs; unfold fvar_lb_val at hlb; rw [habs] at hlb; exact hlb rfl
    have hbvf := bvarsGe_child_app_left f a
    have hbva := bvarsGe_child_app_right f a
    have hbv_app : BvarsGe (app f a) (fvar_lb_val (app f a)) 0 :=
      BvarsGe.app _ _ _ _ hbvf hbva
    have hadjf := adjust_child_preserves_osnf f _ 0 hf hbvf
    have hadja := adjust_child_preserves_osnf a _ 0 ha hbva
    have h_ext_0 :
        Expr.HasFreeVar
          (adjust_child (app f a) (fvar_lb_val (app f a)) 0).erase 0 := by
      rw [adjust_child_hasFreeVar_iff (app f a) _ 0 hbv_app 0]
      exact Or.inl ⟨by omega, by simpa using hasFreeVar_at_fvar_lb_val (app f a) hne⟩
    have h_lb_zero' := fvar_lb_val_zero_of_hasFreeVar_zero _ h_ext_0
    have h_fvars_ne := fvars_ne_nil_of_hasFreeVar _ _ h_ext_0
    exact IsOSNF.shifted _ _ hlb_pos
      (IsOSNF.app _ _ hadjf hadja h_lb_zero') h_lb_zero' h_fvars_ne

theorem mk_osnf_compound_lam_isOSNF (body : SExpr) (hb : IsOSNF body) :
    IsOSNF (mk_osnf_compound (lam body)) := by
  show IsOSNF (let lb := fvar_lb_val (lam body);
               if lb = 0 then lam body
               else shift lb (lam (adjust_child body lb 1)))
  simp only
  split
  · rename_i hlb; exact IsOSNF.lam _ hb hlb
  · rename_i hlb
    have hlb_pos : fvar_lb_val (lam body) > 0 := by omega
    have hne : (lam body).fvars ≠ [] := by
      intro habs; unfold fvar_lb_val at hlb; rw [habs] at hlb; exact hlb rfl
    have hbvb := bvarsGe_child_lam body
    have hbv_lam : BvarsGe (lam body) (fvar_lb_val (lam body)) 0 :=
      BvarsGe.lam _ _ _ hbvb
    have hadjb := adjust_child_preserves_osnf body _ 1 hb hbvb
    have h_ext_0 :
        Expr.HasFreeVar
          (adjust_child (lam body) (fvar_lb_val (lam body)) 0).erase 0 := by
      rw [adjust_child_hasFreeVar_iff (lam body) _ 0 hbv_lam 0]
      exact Or.inl ⟨by omega, by simpa using hasFreeVar_at_fvar_lb_val (lam body) hne⟩
    have h_lb_zero' := fvar_lb_val_zero_of_hasFreeVar_zero _ h_ext_0
    have h_fvars_ne := fvars_ne_nil_of_hasFreeVar _ _ h_ext_0
    exact IsOSNF.shifted _ _ hlb_pos
      (IsOSNF.lam _ hadjb h_lb_zero') h_lb_zero' h_fvars_ne

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

/-! ### Main theorems -/

-- Helper: IsOSNF.shifted preserves fvar_lb_val and fvars.
private theorem isOSNF_shifted_parts {n : Nat} {c : SExpr} (h : IsOSNF (shift n c)) :
    n > 0 ∧ IsOSNF c ∧ c.fvar_lb_val = 0 ∧ c.fvars ≠ [] := by
  cases h with
  | shifted _ _ hn hc hlb hfv => exact ⟨hn, hc, hlb, hfv⟩

-- Helper: a non-shift OSNF has fvar_lb_val = 0.
private theorem isOSNF_not_shift_fvar_lb_val_zero {e : SExpr}
    (he : IsOSNF e) (h1 : ∀ m c, e ≠ shift m c) : fvar_lb_val e = 0 := by
  cases he with
  | bvar0 => rfl
  | const _ => rfl
  | app _ _ _ _ hlb => exact hlb
  | lam _ _ hlb => exact hlb
  | shifted n c _ _ _ _ => exact absurd rfl (h1 n c)

/-- `to_osnf e` is in OSNF. -/
theorem to_osnf_isOSNF (e : SExpr) : IsOSNF (to_osnf e) := by
  induction e with
  | bvar i =>
    show IsOSNF (if i = 0 then bvar 0 else shift i (bvar 0))
    split
    · exact IsOSNF.bvar0
    · rename_i hi0
      exact IsOSNF.shifted i (bvar 0) (by omega) IsOSNF.bvar0 rfl
        (by simp [fvars])
  | const id => exact IsOSNF.const id
  | app f a ihf iha =>
    show IsOSNF (mk_osnf_compound (app f.to_osnf a.to_osnf))
    exact mk_osnf_compound_app_isOSNF _ _ ihf iha
  | lam body ih =>
    show IsOSNF (mk_osnf_compound (lam body.to_osnf))
    exact mk_osnf_compound_lam_isOSNF _ ih
  | shift k inner ih =>
    show IsOSNF (match inner.to_osnf with
      | shift m core => if k + m = 0 then core else shift (k + m) core
      | e => if k = 0 then e else match e.fvars with | [] => e | _ => shift k e)
    split
    · rename_i m core heq
      have hih : IsOSNF (shift m core) := heq ▸ ih
      obtain ⟨hm, hc, hlb, hfv⟩ := isOSNF_shifted_parts hih
      split
      next hkm => exfalso; omega
      next hkm =>
        exact IsOSNF.shifted (k + m) core (by omega) hc hlb hfv
    · rename_i e hnotshift
      split
      next hk0 => subst hk0; exact ih
      next hk0 =>
        -- match e.fvars
        have : ∀ (fvs : FVarList), inner.to_osnf.fvars = fvs →
            IsOSNF (match fvs with | [] => inner.to_osnf | _ => shift k (inner.to_osnf)) := by
          intro fvs hfvs
          cases fvs with
          | nil => exact ih
          | cons hd tl =>
            have hfv : inner.to_osnf.fvars ≠ [] := by rw [hfvs]; exact List.cons_ne_nil _ _
            have hlb : fvar_lb_val inner.to_osnf = 0 :=
              isOSNF_not_shift_fvar_lb_val_zero ih
                (fun m c hEq => hnotshift m c (hEq ▸ rfl))
            exact IsOSNF.shifted k _ (by omega) ih hlb hfv
        exact this _ rfl

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
            have hclosed := (fvars_empty_iff_no_hasFreeVar inner.to_osnf).mp hfvs
            rw [← ih]
            exact (Expr.shift_eq_of_no_hasFreeVar inner.to_osnf.erase k hclosed).symm
          | d :: rest =>
            show (shift k inner.to_osnf).erase = inner.erase.shift k 0
            rw [SExpr.erase, ih]
        exact this _ rfl

-- Helper for osnf_unique: a shifted core has external free var at n.
private theorem shifted_has_hasFreeVar_n (n : Nat) (core : SExpr)
    (hc : IsOSNF core) (hlb : core.fvar_lb_val = 0) (hfv : core.fvars ≠ []) :
    Expr.HasFreeVar (core.erase.shift n 0) n := by
  have hc0 := fvar_lb_zero_has_hasFreeVar_zero core hlb hfv
  have := Expr.hasFreeVar_shift_bwd core.erase 0 hc0 n 0
  simp only [show 0 ≥ 0 from Nat.zero_le _, ↓reduceIte, Nat.zero_add] at this
  exact this

-- Non-shift OSNF matched against shift n core: contradiction.
private theorem osnf_nonshift_ne_shifted {e : SExpr} (he : IsOSNF e)
    (hlbE : fvar_lb_val e = 0 ∨ e.fvars = [])
    {n : Nat} (hn : n > 0) {core : SExpr}
    (hc : IsOSNF core) (hlb : core.fvar_lb_val = 0) (hfv : core.fvars ≠ [])
    (heq : e.erase = (shift n core).erase) : False := by
  simp only [erase] at heq
  have hs : Expr.HasFreeVar (core.erase.shift n 0) n :=
    shifted_has_hasFreeVar_n n core hc hlb hfv
  rcases hlbE with hlbE | hfvE
  · -- e has ext fvar at 0 (if non-closed) or is closed
    by_cases hfvE2 : e.fvars = []
    · have hnone : ∀ i, ¬ Expr.HasFreeVar e.erase i :=
        (fvars_empty_iff_no_hasFreeVar _).mp hfvE2
      rw [heq] at hnone
      exact hnone n hs
    · have h0 : Expr.HasFreeVar e.erase 0 :=
        fvar_lb_zero_has_hasFreeVar_zero e hlbE hfvE2
      rw [heq] at h0
      have := Expr.hasFreeVar_shift_zero_ge core.erase n 0 h0
      omega
  · have hnone : ∀ i, ¬ Expr.HasFreeVar e.erase i :=
      (fvars_empty_iff_no_hasFreeVar _).mp hfvE
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
      have hs1 := shifted_has_hasFreeVar_n n₁ core₁ hc₁ hlb₁ hfv₁
      have hs2 := shifted_has_hasFreeVar_n n₂ core₂ hc₂ hlb₂ hfv₂
      rw [heq] at hs1
      rw [← heq] at hs2
      have h12 : n₁ ≥ n₂ := Expr.hasFreeVar_shift_zero_ge core₂.erase n₂ n₁ hs1
      have h21 : n₂ ≥ n₁ := Expr.hasFreeVar_shift_zero_ge core₁.erase n₁ n₂ hs2
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
