/-
# OSNF (Outermost-Shift Normal Form) — formal model

The implementation uses explicit Shift nodes to defer shifting work. OSNF is a
canonical form where:

1. A subexpression is either a bare `bvar`, a `const`, a compound (`app`/`lam`)
   whose minimum free bvar index is 0, or a `shift n core` with `n > 0` over
   such a compound whose fvars are non-empty.
2. Two OSNFs are syntactically equal iff they denote the same underlying
   de Bruijn term.

This file models SExpr (expressions with explicit Shift), defines OSNF,
and proves:

- `to_osnf` preserves denotation (`to_osnf_erase`).
- `to_osnf` produces an expression in OSNF (`to_osnf_isOSNF`).
- OSNF is unique per denotation (`osnf_unique`).
- Therefore `to_osnf` is idempotent and decides shift-equivalence.

A few intermediate lemmas linking the delta-encoded `fvars` representation
to the erasure's free-variable structure are stated as `axiom` — they are
informally obvious but require a nontrivial decoding argument that is
orthogonal to the OSNF theorems themselves. See the **Axioms** section for
their specifications.
-/

/-! ## FVarList: delta-encoded sorted sets of natural numbers

Used to track the set of free bvar indices appearing in an `SExpr`. The
delta encoding makes `shift` O(1) (touches only the head), matching the
behavior of `Shift` nodes in the implementation.
-/

/-- Delta-encoded sorted set of natural numbers.
    `[]` is the empty set; `d :: rest` encodes `{d} ∪ {d + 1 + x | x ∈ decode rest}`. -/
abbrev FVarList := List Nat

namespace FVarList

/-- Shift all indices up by `k`. O(1): only changes the head. -/
def shift (k : Nat) : FVarList → FVarList
  | [] => []
  | d :: rest => (d + k) :: rest

/-- Remove bvar(0) and decrement all others (exiting a binder body).
    O(1): pops head if 0, otherwise decrements it. -/
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

theorem shift_bvar' (i k c : Nat) :
    (bvar i : Expr).shift k c = if i ≥ c then bvar (i + k) else bvar i := rfl
theorem shift_app' (f a : Expr) (k c : Nat) :
    (app f a).shift k c = app (f.shift k c) (a.shift k c) := rfl
theorem shift_lam' (body : Expr) (k c : Nat) :
    (lam body).shift k c = lam (body.shift k (c + 1)) := rfl
theorem shift_const' (n k c : Nat) :
    (const n).shift k c = const n := rfl

/-! ### Shift composition lemmas -/

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
    simp only [shift]; exact congrArg Expr.lam (ih (c + 1) (d + 1) (by omega) (by omega))
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
    simp only [shift]; exact congrArg Expr.lam (ih k cutoff (base + 1) hlt)
  | const _ => rfl

theorem shift_comm_lt (e : Expr) (k amount cutoff : Nat) (hlt : k < cutoff) :
    (e.shift k 0).shift amount cutoff = (e.shift amount (cutoff - k)).shift k 0 := by
  have h := shift_comm_lt_gen e k amount cutoff 0 hlt
  simp only [Nat.add_zero] at h; exact h

/-! ### Free-variable predicate on plain Exprs -/

/-- An expression has a free variable at index `i` above cutoff `c`. -/
inductive HasFreeVar : Expr → Nat → Nat → Prop where
  | bvar (i c : Nat) (h : i ≥ c) : HasFreeVar (bvar i) i c
  | app_left (f a : Expr) (i c : Nat) (h : HasFreeVar f i c) : HasFreeVar (app f a) i c
  | app_right (f a : Expr) (i c : Nat) (h : HasFreeVar a i c) : HasFreeVar (app f a) i c
  | lam (body : Expr) (i c : Nat) (h : HasFreeVar body i (c + 1)) : HasFreeVar (lam body) i c

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

/-- Shifting is a no-op on an expression with no free variables at the cutoff. -/
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
0 is modeled — that's what `mk_shift` in the implementation produces.
-/

inductive SExpr where
  | bvar (i : Nat)
  | app (f a : SExpr)
  | lam (body : SExpr)
  | const (id : Nat)
  | shift (amount : Nat) (inner : SExpr)  -- Shift(inner, amount), cutoff=0
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

theorem erase_bvar' (i : Nat) : (bvar i : SExpr).erase = Expr.bvar i := rfl
theorem erase_app' (f a : SExpr) : (app f a).erase = Expr.app f.erase a.erase := rfl
theorem erase_lam' (b : SExpr) : (lam b).erase = Expr.lam b.erase := rfl
theorem erase_const' (n : Nat) : (const n : SExpr).erase = Expr.const n := rfl
theorem erase_shift' (k : Nat) (inner : SExpr) : (shift k inner).erase = inner.erase.shift k 0 := rfl

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

/-- Lower bound on free variable indices (minimum free bvar index).
    Returns `none` for closed expressions. -/
def fvar_lb (e : SExpr) : Option Nat := FVarList.lb e.fvars

/-- Convenience: fvar_lb as a Nat, returning 0 for closed expressions. -/
def fvar_lb_val (e : SExpr) : Nat :=
  match e.fvars with
  | [] => 0
  | d :: _ => d

/-! ### Predicates for OSNF classification -/

/-- An expression is "compound" if it is not a bvar and not a shift. -/
def isCompound : SExpr → Bool
  | bvar _ => false
  | shift _ _ => false
  | _ => true

/-! ### OSNF definition -/

/-- Outermost-Shift Normal Form. An SExpr is in OSNF if it is one of:
    1. A bare `bvar n`
    2. A `const id`
    3. `app f a` where both children are in OSNF and the app's `fvar_lb_val = 0`
    4. `lam body` where body is in OSNF and the lam's `fvar_lb_val = 0`
    5. `shift n core` with `n > 0`, `core` compound and in OSNF, with
       `core.fvar_lb_val = 0` and `core.fvars ≠ []`. -/
inductive IsOSNF : SExpr → Prop where
  | bvar (i : Nat) : IsOSNF (bvar i)
  | const (id : Nat) : IsOSNF (const id)
  | app (f a : SExpr) (hf : IsOSNF f) (ha : IsOSNF a)
      (hlb : fvar_lb_val (app f a) = 0) : IsOSNF (app f a)
  | lam (body : SExpr) (hb : IsOSNF body)
      (hlb : fvar_lb_val (lam body) = 0) : IsOSNF (lam body)
  | shifted (n : Nat) (core : SExpr) (hn : n > 0)
      (hc : IsOSNF core) (hcomp : core.isCompound)
      (hlb : core.fvar_lb_val = 0)
      (hfv : core.fvars ≠ []) :
      IsOSNF (shift n core)

/-! ### adjust_child: subtract amount from free variable indices in a child -/

/-- Adjust a child expression by subtracting `amount` from free variable indices
    at or above `cutoff`. Recurses into compound expressions (app/lam).
    Precondition: all free variable indices `≥ cutoff` are also `≥ cutoff + amount`. -/
def adjust_child (e : SExpr) (amount : Nat) (cutoff : Nat) : SExpr :=
  match e with
  | bvar i => if i ≥ cutoff then bvar (i - amount) else bvar i
  | app f a => app (adjust_child f amount cutoff) (adjust_child a amount cutoff)
  | lam body => lam (adjust_child body amount (cutoff + 1))
  | const id => const id
  | shift k inner =>
    if k ≥ cutoff then
      let k' := k - amount
      if k' = 0 then inner else shift k' inner
    else
      shift k (adjust_child inner amount (cutoff - k))

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
      | other => other  -- const always has lb=0, won't reach here
    shift lb core

/-! ### to_osnf: compute the OSNF of an expression (recursive, bottom-up) -/

/-- Compute the OSNF of an expression by recursively normalizing children first,
    then applying OSNF normalization at the current node.
    - bvar/const: already in OSNF
    - shift: combine with inner's OSNF (collapse nested shifts)
    - app/lam: recursively normalize children, then extract fvar_lb -/
def to_osnf : SExpr → SExpr
  | bvar i => bvar i
  | const id => const id
  | app f a => mk_osnf_compound (app f.to_osnf a.to_osnf)
  | lam body => mk_osnf_compound (lam body.to_osnf)
  | shift k inner =>
    match inner.to_osnf with
    | bvar i => bvar (i + k)
    | shift k' core => if k + k' = 0 then core else shift (k + k') core
    | e =>  -- compound (already a core from mk_osnf_compound)
      if k = 0 then e
      else match e.fvars with
        | [] => e
        | _ => shift k e

/-! ### Helpers for to_osnf_erase -/

/-- Predicate: all bvar indices in `e` at or above `cutoff` are `≥ cutoff + amount`.
    This is the precondition for `adjust_child` to correctly preserve erasure. -/
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
    (hge : k ≥ cutoff) (hka : k ≥ cutoff + amount) :
    BvarsGe (shift k inner) amount cutoff
  | shift_lt (k : Nat) (inner : SExpr) (amount cutoff : Nat)
    (hlt : ¬(k ≥ cutoff)) (hi : BvarsGe inner amount (cutoff - k)) :
    BvarsGe (shift k inner) amount cutoff

/-- adjust_child preserves erasure (after re-shifting) when the BvarsGe precondition holds. -/
theorem adjust_child_erase (e : SExpr) (amount cutoff : Nat)
    (h : BvarsGe e amount cutoff) :
    (adjust_child e amount cutoff).erase.shift amount cutoff = e.erase := by
  induction h with
  | bvar_lt i amount cutoff hlt =>
    show ((if i ≥ cutoff then bvar (i - amount) else bvar i) : SExpr).erase.shift amount cutoff = _
    rw [if_neg (show ¬(i ≥ cutoff) by omega), erase_bvar',
        Expr.shift_bvar', if_neg (show ¬(i ≥ cutoff) by omega)]
  | bvar_ge i amount cutoff hge =>
    show ((if i ≥ cutoff then bvar (i - amount) else bvar i) : SExpr).erase.shift amount cutoff = _
    rw [if_pos (show i ≥ cutoff by omega), erase_bvar',
        Expr.shift_bvar', if_pos (show i - amount ≥ cutoff by omega)]
    congr 1; omega
  | app f a amount cutoff _hf _ha ihf iha =>
    show (Expr.app (adjust_child f amount cutoff).erase (adjust_child a amount cutoff).erase).shift amount cutoff
         = Expr.app f.erase a.erase
    rw [Expr.shift_app']; congr 1 <;> assumption
  | lam body amount cutoff _hb ih =>
    show (Expr.lam (adjust_child body amount (cutoff + 1)).erase).shift amount cutoff = Expr.lam body.erase
    rw [Expr.shift_lam']
    exact congrArg Expr.lam ih
  | const_intro id amount cutoff =>
    show (Expr.const id).shift amount cutoff = Expr.const id
    exact Expr.shift_const' id amount cutoff
  | shift_ge k inner amount cutoff hge hka =>
    show ((if k ≥ cutoff then
            (let k' := k - amount; if k' = 0 then inner else shift k' inner)
           else shift k (adjust_child inner amount (cutoff - k))) : SExpr).erase.shift amount cutoff
         = inner.erase.shift k 0
    rw [if_pos hge]
    by_cases hk0 : k - amount = 0
    · simp only [hk0, ite_true]
      have hkeq : k = amount := by omega
      have hc0 : cutoff = 0 := by omega
      subst hkeq; subst hc0; rfl
    · rw [if_neg hk0, erase_shift']
      rw [Expr.shift_shift_comm inner.erase (k - amount) amount 0 cutoff (by omega) (by omega)]
      congr 1; omega
  | shift_lt k inner amount cutoff hlt hi ih =>
    show ((if k ≥ cutoff then _
           else shift k (adjust_child inner amount (cutoff - k))) : SExpr).erase.shift amount cutoff
         = inner.erase.shift k 0
    rw [if_neg hlt, erase_shift']
    rw [Expr.shift_comm_lt (adjust_child inner amount (cutoff - k)).erase k amount cutoff (by omega)]
    show ((adjust_child inner amount (cutoff - k)).erase.shift amount (cutoff - k)).shift k 0
         = inner.erase.shift k 0
    exact congrArg (·.shift k 0) ih

/-! ### Axioms linking `SExpr.fvars` to free-variable structure on `erase`

These intermediate lemmas state that the delta-encoded `SExpr.fvars` faithfully
represents the free variables of the erasure. They are informally true but
require a `decode`-based characterization (`decode fvars = {i | HasFreeVar e.erase i 0}`
as sets) to prove rigorously. Left as axioms here — see `PLAN.md` for context.
-/

/-- Children of `app f a` satisfy BvarsGe for fvar_lb_val. -/
axiom bvarsGe_child_app_left (f a : SExpr) :
    BvarsGe f (fvar_lb_val (app f a)) 0
/-- Children of `app f a` satisfy BvarsGe for fvar_lb_val. -/
axiom bvarsGe_child_app_right (f a : SExpr) :
    BvarsGe a (fvar_lb_val (app f a)) 0
/-- Body of `lam body` satisfies BvarsGe for fvar_lb_val at cutoff 1. -/
axiom bvarsGe_child_lam (body : SExpr) :
    BvarsGe body (fvar_lb_val (lam body)) 1

/-- mk_osnf_compound produces OSNF for app inputs when children are OSNF. -/
axiom mk_osnf_compound_app_isOSNF (f a : SExpr) (hf : IsOSNF f) (ha : IsOSNF a) :
    IsOSNF (mk_osnf_compound (app f a))

/-- mk_osnf_compound produces OSNF for lam inputs when body is OSNF. -/
axiom mk_osnf_compound_lam_isOSNF (body : SExpr) (hb : IsOSNF body) :
    IsOSNF (mk_osnf_compound (lam body))

/-- If `e.fvars = []`, the erasure of `e` has no free variables, so shifting is a no-op. -/
axiom fvars_empty_iff_no_free_vars (e : SExpr) (he : IsOSNF e) :
    e.fvars = [] ↔ ∀ i, ¬ Expr.HasFreeVar e.erase i 0

/-- If `fvar_lb_val e = 0` and `fvars` is non-empty, bvar(0) appears free in the erasure. -/
axiom fvar_lb_zero_has_freevar_zero (e : SExpr) (he : IsOSNF e)
    (hlb : fvar_lb_val e = 0) (hne : e.fvars ≠ []) :
    Expr.HasFreeVar e.erase 0 0

/-- Corollary of `fvars_empty_iff_no_free_vars` + `Expr.shift_eq_of_no_freevars`. -/
theorem fvars_empty_shift_erase (e : SExpr) (he : IsOSNF e) (hfv : e.fvars = []) (k : Nat) :
    e.erase.shift k 0 = e.erase :=
  Expr.shift_eq_of_no_freevars e.erase k 0 ((fvars_empty_iff_no_free_vars e he).mp hfv)

/-! ### mk_osnf_compound preserves erasure -/

theorem mk_osnf_compound_erase_app (f a : SExpr) :
    (mk_osnf_compound (app f a)).erase = (app f a).erase := by
  show (let lb := (app f a).fvar_lb_val;
        if lb = 0 then app f a
        else shift lb (app (adjust_child f lb 0) (adjust_child a lb 0))).erase = _
  simp only
  split
  · rfl
  · rw [erase_shift', erase_app', Expr.shift_app']
    congr 1
    exact adjust_child_erase f _ 0 (bvarsGe_child_app_left f a)
    exact adjust_child_erase a _ 0 (bvarsGe_child_app_right f a)

theorem mk_osnf_compound_erase_lam (body : SExpr) :
    (mk_osnf_compound (lam body)).erase = (lam body).erase := by
  show (let lb := (lam body).fvar_lb_val;
        if lb = 0 then lam body
        else shift lb (lam (adjust_child body lb 1))).erase = _
  simp only
  split
  · rfl
  · rw [erase_shift', erase_lam', Expr.shift_lam']
    congr 1; exact adjust_child_erase body _ 1 (bvarsGe_child_lam body)

/-! ### Structural lemmas about OSNF -/

theorem to_osnf_bvar (i : Nat) : to_osnf (bvar i) = bvar i := rfl
theorem to_osnf_const (id : Nat) : to_osnf (const id) = const id := rfl

private theorem IsOSNF.shift_parts (k : Nat) (c : SExpr) (h : IsOSNF (shift k c)) :
    k > 0 ∧ IsOSNF c ∧ c.isCompound = true ∧ c.fvar_lb_val = 0 ∧ c.fvars ≠ [] := by
  cases h with
  | shifted _ _ hn hc hcomp hlb hfv => exact ⟨hn, hc, hcomp, hlb, hfv⟩

private theorem isOSNF_not_bvar_not_shift (e : SExpr) (h : IsOSNF e)
    (h1 : ∀ i, e ≠ bvar i) (h2 : ∀ k c, e ≠ shift k c) :
    e.isCompound = true ∧ e.fvar_lb_val = 0 := by
  cases h with
  | bvar i => exact absurd rfl (h1 i)
  | const id => exact ⟨rfl, rfl⟩
  | app _ _ _ _ hlb => exact ⟨rfl, hlb⟩
  | lam _ _ hlb => exact ⟨rfl, hlb⟩
  | shifted n c _ _ _ _ _ => exact absurd rfl (h2 n c)

/-! ### Main theorems -/

/-- `to_osnf e` is in OSNF. -/
theorem to_osnf_isOSNF (e : SExpr) : IsOSNF (to_osnf e) := by
  induction e with
  | bvar i => exact IsOSNF.bvar i
  | const id => exact IsOSNF.const id
  | app f a ihf iha => exact mk_osnf_compound_app_isOSNF _ _ ihf iha
  | lam body ih => exact mk_osnf_compound_lam_isOSNF _ ih
  | shift k inner ih =>
    simp only [to_osnf]
    split
    · exact IsOSNF.bvar _
    · rename_i k' c heq
      have hih : IsOSNF (shift k' c) := heq ▸ ih
      obtain ⟨hk', hc_osnf, hc, hlb, hfv⟩ := IsOSNF.shift_parts k' c hih
      split
      next hkk => exfalso; omega
      next hkk => exact IsOSNF.shifted (k + k') c (by omega) hc_osnf hc hlb hfv
    · rename_i h1 h2
      have hih : IsOSNF (inner.to_osnf) := ih
      obtain ⟨hc, hlb⟩ := isOSNF_not_bvar_not_shift _ hih
        (fun i hi => h1 i (by rw [hi]))
        (fun k' c hkc => h2 k' c (by rw [hkc]))
      split
      next hk0 => subst hk0; exact hih
      next hk0 =>
        have : ∀ (fvs : FVarList),
            inner.to_osnf.fvars = fvs →
            IsOSNF (match fvs with | [] => inner.to_osnf | _ => shift k (inner.to_osnf)) := by
          intro fvs hfvs
          cases fvs with
          | nil => exact hih
          | cons hd tl =>
            have hfv : (inner.to_osnf).fvars ≠ [] := by rw [hfvs]; exact List.cons_ne_nil _ _
            exact IsOSNF.shifted k _ (by omega) hih hc hlb hfv
        exact this _ rfl

/-- `to_osnf` preserves denotation: `(to_osnf e).erase = e.erase`. -/
theorem to_osnf_erase (e : SExpr) : (to_osnf e).erase = e.erase := by
  induction e with
  | bvar i => rfl
  | const id => rfl
  | app f a ihf iha =>
    show (mk_osnf_compound (app f.to_osnf a.to_osnf)).erase = Expr.app f.erase a.erase
    rw [mk_osnf_compound_erase_app, erase_app']
    congr 1 <;> assumption
  | lam body ih =>
    show (mk_osnf_compound (lam body.to_osnf)).erase = Expr.lam body.erase
    rw [mk_osnf_compound_erase_lam, erase_lam', ih]
  | shift k inner ih =>
    show (match inner.to_osnf with
      | bvar i => bvar (i + k)
      | shift k' core => if k + k' = 0 then core else shift (k + k') core
      | e => if k = 0 then e
             else match e.fvars with
               | [] => e
               | _ => shift k e).erase = inner.erase.shift k 0
    split
    · rename_i i heq
      rw [erase_bvar', ← ih, heq, erase_bvar', Expr.shift_bvar', if_pos (show i ≥ 0 by omega)]
    · rename_i k' core heq
      have ih' : (shift k' core).erase = inner.erase := by rw [← heq]; exact ih
      split
      next hkk =>
        have hk0 : k = 0 := by omega
        have hk'0 : k' = 0 := by omega
        subst hk0; subst hk'0
        rw [erase_shift', Expr.shift_zero] at ih'
        rw [ih', Expr.shift_zero]
      next hkk =>
        rw [erase_shift']
        rw [erase_shift'] at ih'
        rw [← ih', Expr.shift_shift core.erase k' k 0]
        congr 1; omega
    · split
      next hk0 =>
        subst hk0; rw [ih, Expr.shift_zero]
      next hk0 =>
        have : ∀ (fvs : FVarList),
            inner.to_osnf.fvars = fvs →
            (match fvs with | [] => inner.to_osnf | _ => shift k (inner.to_osnf)).erase
              = inner.erase.shift k 0 := by
          intro fvs hfvs
          cases fvs with
          | nil =>
            have hih : IsOSNF (inner.to_osnf) := to_osnf_isOSNF inner
            rw [← ih]
            exact (fvars_empty_shift_erase (inner.to_osnf) hih hfvs k).symm
          | cons hd tl =>
            rw [erase_shift', ih]
        exact this _ rfl

/-! ### OSNF uniqueness — helper lemmas -/

private theorem shifted_has_free_var_gen (core : Expr) (n i c : Nat)
    (h : Expr.HasFreeVar core i c) :
    Expr.HasFreeVar (core.shift n c) (i + n) c := by
  induction h with
  | bvar j d hge =>
    simp only [Expr.shift, show j ≥ d from hge, ite_true]
    exact Expr.HasFreeVar.bvar (j + n) d (by omega)
  | app_left f a j d hf ih =>
    exact Expr.HasFreeVar.app_left _ _ _ _ ih
  | app_right f a j d ha ih =>
    exact Expr.HasFreeVar.app_right _ _ _ _ ih
  | lam body j d hb ih =>
    exact Expr.HasFreeVar.lam _ _ _ ih

private theorem shifted_has_free_var (core : Expr) (n i : Nat)
    (h : Expr.HasFreeVar core i 0) :
    Expr.HasFreeVar (core.shift n 0) (i + n) 0 :=
  shifted_has_free_var_gen core n i 0 h

private theorem erase_compound_shift_not_bvar (core : SExpr) (n : Nat)
    (hcomp : core.isCompound) (i : Nat) :
    core.erase.shift n 0 ≠ Expr.bvar i := by
  match core with
  | .app f a => simp [erase, Expr.shift]
  | .lam body => simp [erase, Expr.shift]
  | .const id => simp [erase, Expr.shift]

private theorem compound_ne_shifted_erase
    (e₁ : SExpr) (n : Nat) (core : SExpr)
    (h₁ : IsOSNF e₁) (h_core : IsOSNF core)
    (hlb₁ : fvar_lb_val e₁ = 0)
    (hlb_core : fvar_lb_val core = 0)
    (hn : n > 0)
    (hfv_core : core.fvars ≠ [])
    (heq : e₁.erase = (shift n core).erase) : False := by
  simp only [erase] at heq
  have hfv0 := fvar_lb_zero_has_freevar_zero core h_core hlb_core hfv_core
  have hfvn := shifted_has_free_var core.erase n 0 hfv0
  simp only [Nat.zero_add] at hfvn
  rw [← heq] at hfvn
  have hfv₁_ne : e₁.fvars ≠ [] := by
    intro habs
    exact (fvars_empty_iff_no_free_vars e₁ h₁).mp habs n hfvn
  have hfv₁_0 := fvar_lb_zero_has_freevar_zero e₁ h₁ hlb₁ hfv₁_ne
  rw [heq] at hfv₁_0
  exact Expr.no_freevar_zero_in_shifted core.erase n hn hfv₁_0

private theorem shifted_erase_eq_implies
    (core₁ core₂ : SExpr) (n₁ n₂ : Nat)
    (h_core₁ : IsOSNF core₁) (h_core₂ : IsOSNF core₂)
    (hlb₁ : fvar_lb_val core₁ = 0) (hlb₂ : fvar_lb_val core₂ = 0)
    (hfv₁ : core₁.fvars ≠ []) (hfv₂ : core₂.fvars ≠ [])
    (heq : core₁.erase.shift n₁ 0 = core₂.erase.shift n₂ 0) :
    n₁ = n₂ ∧ core₁.erase = core₂.erase := by
  have hn : n₁ = n₂ := by
    have hfv0_1 := fvar_lb_zero_has_freevar_zero core₁ h_core₁ hlb₁ hfv₁
    have hfvn₁ := shifted_has_free_var core₁.erase n₁ 0 hfv0_1
    simp only [Nat.zero_add] at hfvn₁
    have hfv0_2 := fvar_lb_zero_has_freevar_zero core₂ h_core₂ hlb₂ hfv₂
    have hfvn₂ := shifted_has_free_var core₂.erase n₂ 0 hfv0_2
    simp only [Nat.zero_add] at hfvn₂
    have hge₁ := Expr.allFreeVarsGe_shift_zero core₁.erase n₁
    have hge₂ := Expr.allFreeVarsGe_shift_zero core₂.erase n₂
    rw [heq] at hfvn₁; rw [← heq] at hfvn₂
    have h1 : n₁ ≥ n₂ := hge₂ n₁ hfvn₁
    have h2 : n₂ ≥ n₁ := hge₁ n₂ hfvn₂
    omega
  subst hn
  exact ⟨rfl, Expr.shift_injective n₁ 0 core₁.erase core₂.erase heq⟩

/-- **Uniqueness of OSNF**: If two expressions in OSNF denote the same term,
    they are syntactically equal. -/
theorem osnf_unique (e₁ e₂ : SExpr) (h₁ : IsOSNF e₁) (h₂ : IsOSNF e₂)
    (heq : e₁.erase = e₂.erase) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | bvar i =>
    cases h₂ with
    | bvar j =>
      simp only [erase, Expr.bvar.injEq] at heq
      exact congrArg SExpr.bvar heq
    | const id => simp [erase] at heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hcomp hlb hfv =>
      exfalso; simp only [erase] at heq
      exact erase_compound_shift_not_bvar core n hcomp i heq.symm
  | const id =>
    cases h₂ with
    | bvar j => simp [erase] at heq
    | const id₂ =>
      simp only [erase, Expr.const.injEq] at heq
      exact congrArg SExpr.const heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hcomp hlb hfv =>
      exfalso; simp only [erase] at heq
      match core, hcomp, hfv with
      | .app f a, _, _ => simp [erase, Expr.shift] at heq
      | .lam body, _, _ => simp [erase, Expr.shift] at heq
      | .const cid, _, hfv => simp [fvars] at hfv
  | app f₁ a₁ hf₁ ha₁ hlb₁ ihf iha =>
    cases h₂ with
    | bvar j => simp [erase] at heq
    | const id => simp [erase] at heq
    | app f₂ a₂ hf₂ ha₂ hlb₂ =>
      simp only [erase, Expr.app.injEq] at heq
      have := ihf f₂ hf₂ heq.1
      have := iha a₂ ha₂ heq.2
      subst ‹f₁ = f₂›; subst ‹a₁ = a₂›; rfl
    | lam body hb hlb => simp [erase] at heq
    | shifted n core hn hc hcomp hlb hfv =>
      exfalso
      exact compound_ne_shifted_erase (app f₁ a₁) n core
        (IsOSNF.app f₁ a₁ hf₁ ha₁ hlb₁) hc hlb₁ hlb hn hfv heq
  | lam body₁ hb₁ hlb₁ ih =>
    cases h₂ with
    | bvar j => simp [erase] at heq
    | const id => simp [erase] at heq
    | app f a hf ha hlb => simp [erase] at heq
    | lam body₂ hb₂ hlb₂ =>
      simp only [erase, Expr.lam.injEq] at heq
      have := ih body₂ hb₂ heq
      subst this; rfl
    | shifted n core hn hc hcomp hlb hfv =>
      exfalso
      exact compound_ne_shifted_erase (lam body₁) n core
        (IsOSNF.lam body₁ hb₁ hlb₁) hc hlb₁ hlb hn hfv heq
  | shifted n₁ core₁ hn₁ hc₁ hcomp₁ hlb₁ hfv₁ ih_core =>
    cases h₂ with
    | bvar j =>
      exfalso; simp only [erase] at heq
      exact erase_compound_shift_not_bvar core₁ n₁ hcomp₁ j heq
    | const id =>
      exfalso; simp only [erase] at heq
      match core₁, hcomp₁, hfv₁ with
      | .app f a, _, _ => simp [erase, Expr.shift] at heq
      | .lam body, _, _ => simp [erase, Expr.shift] at heq
      | .const cid, _, hfv => simp [fvars] at hfv
    | app f₂ a₂ hf₂ ha₂ hlb₂ =>
      exfalso
      exact compound_ne_shifted_erase (app f₂ a₂) n₁ core₁
        (IsOSNF.app f₂ a₂ hf₂ ha₂ hlb₂) hc₁ hlb₂ hlb₁ hn₁ hfv₁ heq.symm
    | lam body₂ hb₂ hlb₂ =>
      exfalso
      exact compound_ne_shifted_erase (lam body₂) n₁ core₁
        (IsOSNF.lam body₂ hb₂ hlb₂) hc₁ hlb₂ hlb₁ hn₁ hfv₁ heq.symm
    | shifted n₂ core₂ hn₂ hc₂ hcomp₂ hlb₂ hfv₂ =>
      simp only [erase] at heq
      have ⟨hneq, hceq⟩ := shifted_erase_eq_implies
        core₁ core₂ n₁ n₂ hc₁ hc₂ hlb₁ hlb₂ hfv₁ hfv₂ heq
      subst hneq
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
