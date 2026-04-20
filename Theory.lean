/-
# OSNF (Outermost-Shift Normal Form) — formal model

This file is the **specification** for OSNF. All proofs are `sorry`; the goal
is a clean-slate attempt.

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
      | other => other  -- const/bvar/shift: unchanged (unused by callers)
    shift lb core

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

All proofs are `sorry`. See PLAN.md / the next session for the clean-slate
proof attempt. -/

/-- `to_osnf e` is in OSNF. -/
theorem to_osnf_isOSNF (e : SExpr) : IsOSNF (to_osnf e) := sorry

/-- `to_osnf` preserves denotation. -/
theorem to_osnf_erase (e : SExpr) : (to_osnf e).erase = e.erase := sorry

/-- **Uniqueness of OSNF**: If two expressions in OSNF denote the same term,
    they are syntactically equal. -/
theorem osnf_unique (e₁ e₂ : SExpr) (h₁ : IsOSNF e₁) (h₂ : IsOSNF e₂)
    (heq : e₁.erase = e₂.erase) : e₁ = e₂ := sorry

/-- **Corollary**: `to_osnf` is idempotent. -/
theorem to_osnf_idempotent (e : SExpr) : to_osnf (to_osnf e) = to_osnf e := sorry

/-- **Corollary**: Two expressions are shift-equivalent iff they have the same OSNF. -/
theorem equiv_iff_osnf_eq (e₁ e₂ : SExpr) :
    equiv e₁ e₂ ↔ to_osnf e₁ = to_osnf e₂ := sorry

end SExpr
