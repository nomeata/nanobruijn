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

/-! ## FVarList: free-variable index lists

A plain `List Nat` interpreted as a multiset of absolute free-variable
indices. The operations are the obvious ones — shift is `map`, unbind is
`filterMap`, union is `++`. -/

abbrev FVarList := List Nat

namespace FVarList

/-- Shift every index up by `k`. -/
def shift (k : Nat) (xs : FVarList) : FVarList := xs.map (· + k)

/-- Remove bvar(0) and decrement the others (exit a binder body). -/
def unbind (xs : FVarList) : FVarList :=
  xs.filterMap fun i => if i = 0 then none else some (i - 1)

/-- Union = append. Membership is by `∈`; duplicates are fine. -/
def union (as bs : FVarList) : FVarList := as ++ bs

/-- Smallest element; 0 for the empty list. -/
def lb_val : FVarList → Nat
  | [] => 0
  | [x] => x
  | x :: xs => min x (lb_val xs)

theorem lb_val_le_of_mem (xs : FVarList) (i : Nat) (h : i ∈ xs) : lb_val xs ≤ i := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    match xs, h with
    | [], List.Mem.head _ => exact Nat.le_refl _
    | y :: ys, h =>
      simp only [lb_val]
      cases h with
      | head => exact Nat.min_le_left _ _
      | tail _ hmem => exact Nat.le_trans (Nat.min_le_right _ _) (ih hmem)

theorem mem_of_lb_val_eq {xs : FVarList} (hne : xs ≠ []) :
    lb_val xs ∈ xs := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    match xs with
    | [] => exact List.mem_cons_self
    | y :: ys =>
      simp only [lb_val]
      by_cases hle : x ≤ lb_val (y :: ys)
      · simp only [Nat.min_eq_left hle]; exact List.mem_cons_self
      · have : min x (lb_val (y :: ys)) = lb_val (y :: ys) := by
          apply Nat.min_eq_right; omega
        rw [this]; exact List.mem_cons_of_mem _ (ih (by simp))

@[simp] theorem shift_nil (k : Nat) : shift k ([] : FVarList) = [] := rfl
@[simp] theorem shift_cons (k d : Nat) (rest : FVarList) :
    shift k (d :: rest) = (d + k) :: shift k rest := rfl

@[simp] theorem mem_shift {k i : Nat} {xs : FVarList} :
    i ∈ shift k xs ↔ ∃ j ∈ xs, i = j + k := by
  unfold shift; grind [List.mem_map]

@[simp] theorem mem_union {i : Nat} {xs ys : FVarList} :
    i ∈ union xs ys ↔ i ∈ xs ∨ i ∈ ys := by
  unfold union; exact List.mem_append

@[simp] theorem mem_unbind {i : Nat} {xs : FVarList} :
    i ∈ unbind xs ↔ (i + 1) ∈ xs := by
  unfold unbind; simp [List.mem_filterMap]
  grind

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
  fun_induction Expr.shift e j c generalizing d <;> grind [shift]

private theorem shift_comm_lt_gen (e : Expr) (k amount cutoff base : Nat) (hlt : k < cutoff) :
    (e.shift k base).shift amount (cutoff + base) =
    (e.shift amount (cutoff - k + base)).shift k base := by
  fun_induction Expr.shift e k base generalizing cutoff <;> grind [shift]

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
  have := hasFreeVar_shift_fwd e n 0 k h; grind

/-- Shifting back: external bvar j in e gives external bvar j+n (if j ≥ c) in
    e.shift n c. -/
theorem hasFreeVar_shift_bwd (e : Expr) (j : Nat) (h : HasFreeVar e j) (n c : Nat) :
    HasFreeVar (e.shift n c) (if j ≥ c then j + n else j) := by
  induction h generalizing c <;> grind [shift]

/-- If all external free vars of e are below c, shift at cutoff c is a no-op. -/
theorem shift_eq_of_hasFreeVars_lt (e : Expr) (k c : Nat)
    (h : ∀ j, HasFreeVar e j → j < c) : e.shift k c = e := by
  induction e generalizing c with
  | bvar i => have := h i (HasFreeVar.bvar _); grind [shift]
  | app f a ihf iha => grind [shift]
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

/-- Smallest free bvar index; 0 for closed expressions. -/
def fvar_lb_val (e : SExpr) : Nat := FVarList.lb_val e.fvars

/-! ### Link between structural fvars and external fvars on erase -/

theorem mem_fvars_iff_hasFreeVar (e : SExpr) (i : Nat) :
    i ∈ e.fvars ↔ Expr.HasFreeVar e.erase i := by
  induction e generalizing i with
  | bvar j => grind [fvars, erase]
  | const n => grind [fvars, erase]
  | app f a ihf iha => grind [fvars, erase, FVarList.mem_union]
  | lam body ih => grind [fvars, erase, FVarList.mem_unbind]
  | shift k inner ih =>
    simp only [fvars, erase, FVarList.mem_shift]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have := Expr.hasFreeVar_shift_bwd inner.erase j ((ih j).mp hj) k 0
      simpa using this
    · intro h
      rcases Expr.hasFreeVar_shift_extract inner.erase k 0 i h with ⟨hfe, hge⟩ | ⟨_, hlt⟩
      · exact ⟨i - k, (ih (i - k)).mpr hfe, by grind⟩
      · grind

/-- `e.fvars = []` iff the erasure has no external free bvars. -/
theorem fvars_empty_iff_no_hasFreeVar (e : SExpr) :
    e.fvars = [] ↔ ∀ i, ¬ Expr.HasFreeVar e.erase i := by
  constructor
  · intro h i hext
    have := (mem_fvars_iff_hasFreeVar e i).mpr hext
    grind
  · intro h
    match hfv : e.fvars with
    | [] => rfl
    | d :: rest =>
      have : d ∈ e.fvars := by rw [hfv]; exact List.mem_cons_self
      grind [mem_fvars_iff_hasFreeVar]

/-- If fvar_lb_val is 0 and fvars is non-empty, 0 is an external free var. -/
theorem fvar_lb_zero_has_hasFreeVar_zero (e : SExpr)
    (hlb : fvar_lb_val e = 0) (hne : e.fvars ≠ []) :
    Expr.HasFreeVar e.erase 0 := by
  have : FVarList.lb_val e.fvars ∈ e.fvars := FVarList.mem_of_lb_val_eq hne
  rw [show FVarList.lb_val e.fvars = 0 from hlb] at this
  exact (mem_fvars_iff_hasFreeVar e 0).mp this

/-- If fvar_lb_val = k, then all external free vars are ≥ k. -/
theorem hasFreeVar_ge_fvar_lb (e : SExpr) (i : Nat)
    (h : Expr.HasFreeVar e.erase i) :
    i ≥ fvar_lb_val e :=
  FVarList.lb_val_le_of_mem e.fvars i ((mem_fvars_iff_hasFreeVar e i).mpr h)

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

/-! ### BvarsGe: precondition for adjust_child

Defined directly on `fvars`: every free variable of `e` either lies below
`cutoff` or is at least `cutoff + amount`. -/

def BvarsGe (e : SExpr) (amount cutoff : Nat) : Prop :=
  ∀ i ∈ e.fvars, i ≥ cutoff → i ≥ cutoff + amount

/-! ### adjust_child preserves erasure (under BvarsGe) -/

-- Helpers: project / combine `BvarsGe` at app and lam.
private theorem bvarsGe_app_left (f a : SExpr) (amount cutoff : Nat)
    (h : BvarsGe (app f a) amount cutoff) : BvarsGe f amount cutoff := by
  intro i hi; exact h i (by grind [fvars, FVarList.mem_union])

private theorem bvarsGe_app_right (f a : SExpr) (amount cutoff : Nat)
    (h : BvarsGe (app f a) amount cutoff) : BvarsGe a amount cutoff := by
  intro i hi; exact h i (by grind [fvars, FVarList.mem_union])

private theorem bvarsGe_app_of (f a : SExpr) (amount cutoff : Nat)
    (hf : BvarsGe f amount cutoff) (ha : BvarsGe a amount cutoff) :
    BvarsGe (app f a) amount cutoff := by
  intro i hi hic; grind [BvarsGe, fvars, FVarList.mem_union]

private theorem bvarsGe_lam_of (body : SExpr) (amount cutoff : Nat)
    (hb : BvarsGe body amount (cutoff + 1)) :
    BvarsGe (lam body) amount cutoff := by
  intro i hi hic
  have := hb (i + 1) (by grind [fvars, FVarList.mem_unbind]) (by grind); grind

private theorem bvarsGe_lam_body (body : SExpr) (amount cutoff : Nat)
    (h : BvarsGe (lam body) amount cutoff) :
    BvarsGe body amount (cutoff + 1) := by
  intro i hi hic
  have := h (i - 1) (by grind [fvars, FVarList.mem_unbind]) (by grind); grind

-- Derived BvarsGe for shift's inner per branch, matching the old constructor cases.
private theorem bvarsGe_shift_mid (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (h : BvarsGe (shift k inner) amount cutoff) (hge : k ≥ cutoff) :
    BvarsGe inner (amount + cutoff - k) 0 := by
  intro i hi _
  have := h (i + k) (by grind [fvars, FVarList.mem_shift]) (by grind); grind

private theorem bvarsGe_shift_lt (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (h : BvarsGe (shift k inner) amount cutoff) (hlt : k < cutoff) :
    BvarsGe inner amount (cutoff - k) := by
  intro i hi hic
  have := h (i + k) (by grind [fvars, FVarList.mem_shift]) (by grind); grind

theorem adjust_child_erase (e : SExpr) (amount cutoff : Nat)
    (h : BvarsGe e amount cutoff) :
    (adjust_child e amount cutoff).erase.shift amount cutoff = e.erase := by
  induction e generalizing amount cutoff with
  | bvar i =>
    simp only [adjust_child, erase]
    by_cases hic : i ≥ cutoff
    · have := h i (List.mem_cons_self) hic
      simp only [hic, ↓reduceIte, erase, Expr.shift,
        show i - amount ≥ cutoff from by omega]; grind
    · simp only [hic, ↓reduceIte, erase, Expr.shift, hic]
  | app f a ihf iha =>
    simp only [adjust_child, erase, Expr.shift,
      ihf amount cutoff (bvarsGe_app_left f a amount cutoff h),
      iha amount cutoff (bvarsGe_app_right f a amount cutoff h)]
  | lam body ih =>
    simp only [adjust_child, erase, Expr.shift,
      ih amount (cutoff + 1) (bvarsGe_lam_body body amount cutoff h)]
  | const id => rfl
  | shift k inner ih =>
    simp only [adjust_child]
    by_cases hka : k ≥ cutoff + amount
    · simp only [if_pos hka]
      by_cases hk0 : k - amount = 0
      · simp only [hk0, ↓reduceIte, erase]
        have : k = amount := by omega
        have : cutoff = 0 := by omega
        grind [Expr.shift_zero]
      · simp only [hk0, ↓reduceIte, erase]
        rw [Expr.shift_shift_comm inner.erase (k - amount) amount 0 cutoff (by omega) (by omega)]
        grind
    by_cases hkc : k ≥ cutoff
    · simp only [if_neg hka, if_pos hkc]
      have hi := bvarsGe_shift_mid k inner amount cutoff h hkc
      by_cases hc0 : cutoff = 0
      · subst hc0
        simp only [↓reduceIte]
        have : amount = (amount + 0 - k) + k := by omega
        rw [this, ← Expr.shift_shift]; grind [erase, ih (amount + 0 - k) 0 hi]
      · simp only [hc0, ↓reduceIte, erase]
        rw [Expr.shift_shift_comm _ cutoff amount 0 cutoff (by omega) (by omega)]
        have : cutoff + amount = (amount + cutoff - k) + k := by omega
        rw [this, ← Expr.shift_shift]; grind [erase, ih (amount + cutoff - k) 0 hi]
    · simp only [if_neg hka, if_neg hkc, erase]
      have hi := bvarsGe_shift_lt k inner amount cutoff h (by omega)
      rw [Expr.shift_comm_lt _ k amount cutoff (by omega), ih amount (cutoff - k) hi]

/-! ### BvarsGe semantic characterisation -/

/-- From an HasFreeVar-based semantic bound, produce a `BvarsGe`. -/
theorem bvarsGe_of_extSemantic (e : SExpr) (amount cutoff : Nat)
    (h : ∀ i, Expr.HasFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount) :
    BvarsGe e amount cutoff := fun i hi =>
  h i ((mem_fvars_iff_hasFreeVar e i).mp hi)

/-- All external free vars of e.erase are ≥ fvar_lb_val e. -/
theorem bvarsGe_fvar_lb (e : SExpr) : BvarsGe e (fvar_lb_val e) 0 := by
  refine bvarsGe_of_extSemantic e (fvar_lb_val e) 0 ?_
  intro i hi _
  have := hasFreeVar_ge_fvar_lb e i hi; grind

/-! ### Children of compound satisfy BvarsGe -/

theorem bvarsGe_child_app_left (f a : SExpr) :
    BvarsGe f (fvar_lb_val (app f a)) 0 := fun i hi _ => by
  have := hasFreeVar_ge_fvar_lb (app f a) i
    (.app_left ((mem_fvars_iff_hasFreeVar _ _).mp hi)); grind

theorem bvarsGe_child_app_right (f a : SExpr) :
    BvarsGe a (fvar_lb_val (app f a)) 0 := fun i hi _ => by
  have := hasFreeVar_ge_fvar_lb (app f a) i
    (.app_right ((mem_fvars_iff_hasFreeVar _ _).mp hi)); grind

theorem bvarsGe_child_lam (body : SExpr) :
    BvarsGe body (fvar_lb_val (lam body)) 1 := fun i hi hic => by
  have hlam : Expr.HasFreeVar (lam body).erase (i - 1) := by
    have : (i - 1) + 1 = i := by grind
    grind [erase, mem_fvars_iff_hasFreeVar]
  have := hasFreeVar_ge_fvar_lb (lam body) (i - 1) hlam; grind

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
    ∀ i, Expr.HasFreeVar e.erase i → i ≥ cutoff → i ≥ cutoff + amount := fun i hi =>
  h i ((mem_fvars_iff_hasFreeVar e i).mpr hi)

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
    by_cases hkc : k ≥ cutoff <;> simp_all
  · rintro (⟨hkc, h⟩ | ⟨hkc, h⟩)
    · rw [← hadj] at h
      rcases Expr.hasFreeVar_shift_extract _ amount cutoff (k + amount) h with
        ⟨hfe, _⟩ | ⟨_, _⟩
      · have heq : k + amount - amount = k := by omega
        rw [heq] at hfe; exact hfe
      · omega
    · rw [← hadj] at h
      rcases Expr.hasFreeVar_shift_extract _ amount cutoff k h with ⟨_, _⟩ | ⟨hfe, _⟩
      · omega
      · exact hfe

/-- If fvar_lb_val e = 0, then adjust_child preserves this property. -/
theorem adjust_child_preserves_fvar_lb_zero (e : SExpr) (amount cutoff : Nat)
    (h : fvar_lb_val e = 0) (hbv : BvarsGe e amount cutoff) :
    fvar_lb_val (adjust_child e amount cutoff) = 0 := by
  by_cases hfv : e.fvars = []
  · -- e closed ⇒ adj e closed
    have hclosed := (fvars_empty_iff_no_hasFreeVar e).mp hfv
    have hclosed' : ∀ k, ¬ Expr.HasFreeVar (adjust_child e amount cutoff).erase k := by
      intro k hk; rw [adjust_child_hasFreeVar_iff e amount cutoff hbv k] at hk
      rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ <;> exact hclosed _ h'
    have : (adjust_child e amount cutoff).fvars = [] :=
      (fvars_empty_iff_no_hasFreeVar _).mpr hclosed'
    show FVarList.lb_val _ = 0; rw [this]; rfl
  · -- fvar_lb_val e = 0 and fvars nonempty ⇒ 0 ∈ fvars
    have hmem_e : (0 : Nat) ∈ e.fvars := h ▸ FVarList.mem_of_lb_val_eq hfv
    have hext0 : Expr.HasFreeVar e.erase 0 := (mem_fvars_iff_hasFreeVar e 0).mp hmem_e
    -- derive HasFreeVar on adj
    have hadj0 : Expr.HasFreeVar (adjust_child e amount cutoff).erase 0 := by
      rw [adjust_child_hasFreeVar_iff e amount cutoff hbv 0]
      by_cases hc : cutoff = 0
      · left; subst hc
        have := hasFreeVar_of_bvarsGe e amount 0 hbv 0 hext0 (Nat.zero_le _)
        have : amount = 0 := by grind
        subst this; exact ⟨by grind, by simpa using hext0⟩
      · exact Or.inr ⟨by grind, hext0⟩
    have hmem : (0 : Nat) ∈ (adjust_child e amount cutoff).fvars :=
      (mem_fvars_iff_hasFreeVar _ 0).mpr hadj0
    have := FVarList.lb_val_le_of_mem _ 0 hmem
    show FVarList.lb_val _ = 0; grind

/-- adjust_child preserves fvars non-emptiness. -/
theorem adjust_child_fvars_nonempty (e : SExpr) (amount cutoff : Nat)
    (hbv : BvarsGe e amount cutoff) (hne : e.fvars ≠ []) :
    (adjust_child e amount cutoff).fvars ≠ [] := by
  intro habs
  have hclosed := (fvars_empty_iff_no_hasFreeVar _).mp habs
  apply hne
  refine (fvars_empty_iff_no_hasFreeVar _).mpr fun i hi => ?_
  by_cases hic : i ≥ cutoff
  · have := hasFreeVar_of_bvarsGe e amount cutoff hbv i hi hic
    apply hclosed (i - amount)
    rw [adjust_child_hasFreeVar_iff e amount cutoff hbv (i - amount)]
    exact Or.inl ⟨by omega, by rw [show i - amount + amount = i from by omega]; exact hi⟩
  · apply hclosed i
    rw [adjust_child_hasFreeVar_iff e amount cutoff hbv i]
    exact Or.inr ⟨by omega, hi⟩

/-! ### mk_osnf_compound preserves erasure -/

theorem mk_osnf_compound_erase_app (f a : SExpr) :
    (mk_osnf_compound (app f a)).erase = (app f a).erase := by
  show (let lb := (app f a).fvar_lb_val;
        if lb = 0 then app f a
        else shift lb (app (adjust_child f lb 0) (adjust_child a lb 0))).erase = _
  simp only
  split
  · rfl
  · have hf := adjust_child_erase f _ 0 (bvarsGe_child_app_left f a)
    have ha := adjust_child_erase a _ 0 (bvarsGe_child_app_right f a)
    grind [erase, Expr.shift]

theorem mk_osnf_compound_erase_lam (body : SExpr) :
    (mk_osnf_compound (lam body)).erase = (lam body).erase := by
  show (let lb := (lam body).fvar_lb_val;
        if lb = 0 then lam body
        else shift lb (lam (adjust_child body lb 1))).erase = _
  simp only
  split
  · rfl
  · have := adjust_child_erase body _ 1 (bvarsGe_child_lam body)
    grind [erase, Expr.shift]

/-! ### mk_osnf_compound produces OSNF -/

/-- The `adjust_child` of an OSNF expression is still OSNF (structure preserved),
    with fvar_lb_val shifted down. -/
theorem adjust_child_preserves_osnf (e : SExpr) (amount cutoff : Nat)
    (h : IsOSNF e) (hbvars : BvarsGe e amount cutoff) :
    IsOSNF (adjust_child e amount cutoff) := by
  induction h generalizing amount cutoff with
  | bvar0 =>
    show IsOSNF (if 0 ≥ cutoff then bvar (0 - amount) else bvar 0)
    split <;> grind [IsOSNF.bvar0]
  | const id => exact IsOSNF.const id
  | app f a hf ha hlb ihf iha =>
    exact IsOSNF.app _ _
      (ihf amount cutoff (bvarsGe_app_left f a amount cutoff hbvars))
      (iha amount cutoff (bvarsGe_app_right f a amount cutoff hbvars))
      (adjust_child_preserves_fvar_lb_zero (app f a) amount cutoff hlb hbvars)
  | lam body hb hlb ih =>
    exact IsOSNF.lam _
      (ih amount (cutoff + 1) (bvarsGe_lam_body body amount cutoff hbvars))
      (adjust_child_preserves_fvar_lb_zero (lam body) amount cutoff hlb hbvars)
  | shifted n core hn hc hlb_core hfv_core ih_core =>
    show IsOSNF (if n ≥ cutoff + amount then
                  (let k' := n - amount; if k' = 0 then core else shift k' core)
                else if n ≥ cutoff then
                  (let inner' := adjust_child core (amount + cutoff - n) 0
                   if cutoff = 0 then inner' else shift cutoff inner')
                else shift n (adjust_child core amount (cutoff - n)))
    by_cases hka : n ≥ cutoff + amount
    · simp only [if_pos hka]
      by_cases hk0 : n - amount = 0 <;>
        simp only [hk0, ↓reduceIte] <;>
        first | exact hc |
          exact IsOSNF.shifted (n - amount) core (by omega) hc hlb_core hfv_core
    by_cases hkc : n ≥ cutoff
    · simp only [if_neg hka, if_pos hkc]
      have hi := bvarsGe_shift_mid n core amount cutoff hbvars hkc
      by_cases hc0 : cutoff = 0
      · subst hc0; simp only [↓reduceIte]; exact ih_core _ _ hi
      · simp only [hc0, ↓reduceIte]
        exact IsOSNF.shifted cutoff _ (by omega) (ih_core _ _ hi)
          (adjust_child_preserves_fvar_lb_zero core _ 0 hlb_core hi)
          (adjust_child_fvars_nonempty core _ 0 hi hfv_core)
    · simp only [if_neg hka, if_neg hkc]
      have hi := bvarsGe_shift_lt n core amount cutoff hbvars (by omega)
      exact IsOSNF.shifted n _ hn (ih_core amount (cutoff - n) hi)
        (adjust_child_preserves_fvar_lb_zero core amount (cutoff - n) hlb_core hi)
        (adjust_child_fvars_nonempty core amount (cutoff - n) hi hfv_core)

-- Helper: when fvars is non-empty, get HasFreeVar at fvar_lb_val.
private theorem hasFreeVar_at_fvar_lb_val (e : SExpr) (hne : e.fvars ≠ []) :
    Expr.HasFreeVar e.erase (fvar_lb_val e) :=
  (mem_fvars_iff_hasFreeVar _ _).mp (FVarList.mem_of_lb_val_eq hne)

-- Helper: if HasFreeVar e'.erase 0, then e'.fvar_lb_val = 0.
private theorem fvar_lb_val_zero_of_hasFreeVar_zero (e' : SExpr)
    (h : Expr.HasFreeVar e'.erase 0) : fvar_lb_val e' = 0 := by
  have hmem : (0 : Nat) ∈ e'.fvars := (mem_fvars_iff_hasFreeVar _ _).mpr h
  have := FVarList.lb_val_le_of_mem _ 0 hmem
  show FVarList.lb_val _ = 0; grind

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
    have hne : (app f a).fvars ≠ [] := by
      intro habs; unfold fvar_lb_val at hlb; rw [habs] at hlb; exact hlb rfl
    have hbvf := bvarsGe_child_app_left f a
    have hbva := bvarsGe_child_app_right f a
    have hbv_app := bvarsGe_app_of f a _ 0 hbvf hbva
    have h_ext_0 :
        Expr.HasFreeVar (adjust_child (app f a) (fvar_lb_val (app f a)) 0).erase 0 := by
      rw [adjust_child_hasFreeVar_iff (app f a) _ 0 hbv_app 0]
      exact Or.inl ⟨by omega, by simpa using hasFreeVar_at_fvar_lb_val (app f a) hne⟩
    have h_lb := fvar_lb_val_zero_of_hasFreeVar_zero _ h_ext_0
    exact IsOSNF.shifted _ _ (by omega)
      (IsOSNF.app _ _ (adjust_child_preserves_osnf f _ 0 hf hbvf)
        (adjust_child_preserves_osnf a _ 0 ha hbva) h_lb)
      h_lb (fvars_ne_nil_of_hasFreeVar _ _ h_ext_0)

theorem mk_osnf_compound_lam_isOSNF (body : SExpr) (hb : IsOSNF body) :
    IsOSNF (mk_osnf_compound (lam body)) := by
  show IsOSNF (let lb := fvar_lb_val (lam body);
               if lb = 0 then lam body
               else shift lb (lam (adjust_child body lb 1)))
  simp only
  split
  · rename_i hlb; exact IsOSNF.lam _ hb hlb
  · rename_i hlb
    have hne : (lam body).fvars ≠ [] := by
      intro habs; unfold fvar_lb_val at hlb; rw [habs] at hlb; exact hlb rfl
    have hbvb := bvarsGe_child_lam body
    have hbv_lam := bvarsGe_lam_of body _ 0 hbvb
    have h_ext_0 :
        Expr.HasFreeVar (adjust_child (lam body) (fvar_lb_val (lam body)) 0).erase 0 := by
      rw [adjust_child_hasFreeVar_iff (lam body) _ 0 hbv_lam 0]
      exact Or.inl ⟨by omega, by simpa using hasFreeVar_at_fvar_lb_val (lam body) hne⟩
    have h_lb := fvar_lb_val_zero_of_hasFreeVar_zero _ h_ext_0
    exact IsOSNF.shifted _ _ (by omega)
      (IsOSNF.lam _ (adjust_child_preserves_osnf body _ 1 hb hbvb) h_lb)
      h_lb (fvars_ne_nil_of_hasFreeVar _ _ h_ext_0)

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
  fun_induction to_osnf e with
  | case1 => exact IsOSNF.bvar0 -- bvar 0
  | case2 i hi0 => -- bvar i, i ≠ 0
    exact IsOSNF.shifted i (bvar 0) (by omega) IsOSNF.bvar0 rfl (by simp [fvars])
  | case3 => exact IsOSNF.const _ -- const
  | case4 f a ihf iha => exact mk_osnf_compound_app_isOSNF _ _ ihf iha
  | case5 body ih => exact mk_osnf_compound_lam_isOSNF _ ih
  | case6 k inner m core heq hkm ih => -- inner.to_osnf = shift m core, k+m=0
    have hk0 : k = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hk0; subst hm0
    obtain ⟨_, hc, _, _⟩ := isOSNF_shifted_parts (heq ▸ ih)
    exact hc
  | case7 k inner m core heq hkm ih => -- inner.to_osnf = shift m core, k+m ≠ 0
    obtain ⟨_, hc, hlb, hfv⟩ := isOSNF_shifted_parts (heq ▸ ih)
    exact IsOSNF.shifted (k + m) core (by omega) hc hlb hfv
  | case8 inner hnotshift ih => exact ih -- shift 0 inner
  | case9 k inner hk0 hnotshift hclosed ih => exact ih -- fvars = []
  | case10 k inner hk0 hnotshift hne ih => -- fvars ≠ []
    have hlb := isOSNF_not_shift_fvar_lb_val_zero ih
      (fun m c hEq => hnotshift m c (hEq ▸ rfl))
    exact IsOSNF.shifted k _ (by omega) ih hlb hne

/-- `to_osnf` preserves denotation. -/
theorem to_osnf_erase (e : SExpr) : (to_osnf e).erase = e.erase := by
  induction e with
  | bvar i =>
    simp only [to_osnf]
    split <;> grind [erase, Expr.shift]
  | const id => rfl
  | app f a ihf iha =>
    show (mk_osnf_compound (app f.to_osnf a.to_osnf)).erase = Expr.app f.erase a.erase
    rw [mk_osnf_compound_erase_app]; grind [erase]
  | lam body ih =>
    show (mk_osnf_compound (lam body.to_osnf)).erase = Expr.lam body.erase
    rw [mk_osnf_compound_erase_lam]; grind [erase]
  | shift k inner ih =>
    show (match inner.to_osnf with
      | shift m core => if k + m = 0 then core else shift (k + m) core
      | e => if k = 0 then e else match e.fvars with | [] => e | _ => shift k e).erase
         = inner.erase.shift k 0
    split
    · rename_i m core heq
      have ih' : (shift m core).erase = inner.erase := by rw [← heq]; exact ih
      rw [erase] at ih'
      split
      · have hk0 : k = 0 := by omega
        have hm0 : m = 0 := by omega
        subst hk0; subst hm0; grind [erase, Expr.shift_zero]
      · grind [erase, Expr.shift_shift]
    · rename_i e hnotShift
      split
      · rename_i hk0; subst hk0; rw [ih, Expr.shift_zero]
      · have : ∀ (fvs : FVarList), inner.to_osnf.fvars = fvs →
            (match fvs with | [] => inner.to_osnf | _ => shift k (inner.to_osnf)).erase
              = inner.erase.shift k 0 := by
          intro fvs hfvs
          match fvs with
          | [] =>
            have hclosed := (fvars_empty_iff_no_hasFreeVar inner.to_osnf).mp hfvs
            have := Expr.shift_eq_of_no_hasFreeVar inner.to_osnf.erase k hclosed
            grind
          | d :: rest => grind [erase]
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
      have := Expr.hasFreeVar_shift_zero_ge core.erase n 0 h0; grind
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
    | shifted n core hn hc hlb hfv =>
      exact (osnf_nonshift_ne_shifted IsOSNF.bvar0 (Or.inl rfl) hn hc hlb hfv heq).elim
    | _ => first | rfl | simp [erase] at heq
  | const id =>
    cases h₂ with
    | const id' => simp only [erase, Expr.const.injEq] at heq; exact congrArg _ heq
    | shifted n core hn hc hlb hfv =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.const id) (Or.inr rfl) hn hc hlb hfv heq).elim
    | _ => simp [erase] at heq
  | app f₁ a₁ hf₁ ha₁ hlb₁ ihf iha =>
    cases h₂ with
    | app f₂ a₂ hf₂ ha₂ hlb₂ =>
      simp only [erase, Expr.app.injEq] at heq
      have hfe := ihf f₂ hf₂ heq.1
      have hae := iha a₂ ha₂ heq.2
      subst hfe; subst hae; rfl
    | shifted n core hn hc hlb hfv =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.app f₁ a₁ hf₁ ha₁ hlb₁) (Or.inl hlb₁)
        hn hc hlb hfv heq).elim
    | _ => simp [erase] at heq
  | lam body₁ hb₁ hlb₁ ih =>
    cases h₂ with
    | lam body₂ hb₂ hlb₂ =>
      simp only [erase, Expr.lam.injEq] at heq
      have := ih body₂ hb₂ heq; subst this; rfl
    | shifted n core hn hc hlb hfv =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.lam body₁ hb₁ hlb₁) (Or.inl hlb₁)
        hn hc hlb hfv heq).elim
    | _ => simp [erase] at heq
  | shifted n₁ core₁ hn₁ hc₁ hlb₁ hfv₁ ih_core =>
    cases h₂ with
    | bvar0 =>
      exact (osnf_nonshift_ne_shifted IsOSNF.bvar0 (Or.inl rfl) hn₁ hc₁ hlb₁ hfv₁ heq.symm).elim
    | const id =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.const id) (Or.inr rfl) hn₁ hc₁ hlb₁ hfv₁ heq.symm).elim
    | app f a hf ha hlb =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.app f a hf ha hlb) (Or.inl hlb)
        hn₁ hc₁ hlb₁ hfv₁ heq.symm).elim
    | lam body hb hlb =>
      exact (osnf_nonshift_ne_shifted (IsOSNF.lam body hb hlb) (Or.inl hlb)
        hn₁ hc₁ hlb₁ hfv₁ heq.symm).elim
    | shifted n₂ core₂ hn₂ hc₂ hlb₂ hfv₂ =>
      simp only [erase] at heq
      have hs1 := shifted_has_hasFreeVar_n n₁ core₁ hc₁ hlb₁ hfv₁
      have hs2 := shifted_has_hasFreeVar_n n₂ core₂ hc₂ hlb₂ hfv₂
      rw [heq] at hs1; rw [← heq] at hs2
      have h12 := Expr.hasFreeVar_shift_zero_ge core₂.erase n₂ n₁ hs1
      have h21 := Expr.hasFreeVar_shift_zero_ge core₁.erase n₁ n₂ hs2
      have hneq : n₁ = n₂ := by omega
      subst hneq
      have hceq := Expr.shift_injective n₁ 0 _ _ heq
      have := ih_core core₂ hc₂ hceq; subst this; rfl

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
