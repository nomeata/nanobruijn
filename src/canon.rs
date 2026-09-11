//! Canonical OSNF under binders.
//!
//! `Theory.lean`'s `IsOSNF.lam` requires `fvar_lb_val (lam body) = 0`, where the free
//! variables of `lam body` are `unbind body.fvars`: the bound variable is dropped and the
//! rest decremented. A shift common to the body's *free* variables must therefore be
//! extracted through the binder, which `mk_osnf_compound` does with
//! `adjust_child body lb 1` — a shift with a cutoff. The uniform `osnf_adj` cannot do
//! that (it would underflow on the `V0+0` child), so the binder constructors used to skip
//! it whenever the body mentioned its bound variable, and the same term could then be
//! `Lam(ty, body)+1` or `Lam(ty, body')+0` with the shift baked into `body'`. Pointer
//! equality is only complete for alpha-equivalent terms if this is done; see PLAN.md.
//!
//! The extractable shift is read off a per-core **loose-bvar bitset** (`BvSet`), kept as
//! a side table like `expr_nlbv` and computed at allocation from the children: a `u64`
//! for indices `0..64` plus an out-of-line tail for indices `>= 64`, which most cores do
//! not have. Shift, unbind and union are exact on it, so every binder is decided exactly
//! and the implemented normal form is the theory's throughout. The rebuild (`unshift`)
//! only descends into children whose pointer shift is below the cutoff — the part of the
//! body that mentions a bound variable — and is memoized per core.
use crate::expr::{BinderStyle, Expr};
use crate::util::{new_fx_hash_map, CorePtr, DagMarker, ExprPtr, FxHashMap, NamePtr};

/// The set of loose bvar indices of a term. `head` holds indices `0..64`; `tail[i]` holds
/// indices `64*(i+1) .. 64*(i+2)`. Trailing zero tail words are trimmed, so a term whose
/// indices are all below 64 has an empty tail and never allocates.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BvSet {
    pub head: u64,
    pub tail: Vec<u64>,
}

/// Smallest index `>= cutoff` in a `(head, tail)` bitset, if any.
pub(crate) fn min_ge_words(head: u64, tail: &[u64], cutoff: u16) -> Option<u16> {
    let (q, r) = ((cutoff / 64) as usize, (cutoff % 64) as u32);
    let mut i = q;
    while i <= tail.len() {
        let mut v = if i == 0 { head } else { tail[i - 1] };
        if i == q && r != 0 { v &= u64::MAX << r; }
        if v != 0 { return Some((i as u32 * 64 + v.trailing_zeros()) as u16); }
        i += 1;
    }
    None
}

impl BvSet {
    pub(crate) fn empty() -> Self { Self { head: 0, tail: Vec::new() } }

    pub(crate) fn single(i: u16) -> Self {
        let mut s = Self::empty();
        s.set(i);
        s
    }

    fn set(&mut self, i: u16) {
        let (w, b) = ((i / 64) as usize, i % 64);
        if w == 0 { self.head |= 1u64 << b; return; }
        if self.tail.len() < w { self.tail.resize(w, 0); }
        self.tail[w - 1] |= 1u64 << b;
    }

    fn trim(&mut self) {
        while self.tail.last() == Some(&0) { self.tail.pop(); }
    }

    #[inline]
    fn word_mut(&mut self, i: usize) -> &mut u64 {
        if i == 0 { &mut self.head } else { &mut self.tail[i - 1] }
    }

    /// `self |= (head, tail) << s`. The common case — no tail and the shifted head fits —
    /// touches only `head`.
    pub(crate) fn or_shl(&mut self, head: u64, tail: &[u64], s: u16) {
        if head == 0 && tail.is_empty() { return; }
        let (q, r) = ((s / 64) as usize, (s % 64) as u32);
        if tail.is_empty() && q == 0 && (r == 0 || head >> (64 - r) == 0) {
            self.head |= head << r;
            return;
        }
        let n = 1 + tail.len();
        let need = n + q + (r != 0) as usize; // words, including head
        if self.tail.len() + 1 < need { self.tail.resize(need - 1, 0); }
        for i in 0..n {
            let v = if i == 0 { head } else { tail[i - 1] };
            if v == 0 { continue; }
            *self.word_mut(i + q) |= if r == 0 { v } else { v << r };
            if r != 0 { *self.word_mut(i + q + 1) |= v >> (64 - r); }
        }
    }

    /// `self |= unbind (head, tail)`: index 0 dropped, the rest decremented.
    pub(crate) fn or_unbind(&mut self, head: u64, tail: &[u64]) {
        self.head |= head >> 1;
        if tail.is_empty() { return; }
        if self.tail.len() < tail.len() { self.tail.resize(tail.len(), 0); }
        self.head |= tail[0] << 63;
        for i in 0..tail.len() {
            self.tail[i] |= tail[i] >> 1;
            if i + 1 < tail.len() { self.tail[i] |= tail[i + 1] << 63; }
        }
    }

    /// `self |= (head, tail) << s` with a binder leaving in between: the child pointer's set
    /// is `(head, tail) << s`, and the binder drops index 0 and decrements the rest.
    pub(crate) fn or_shl_unbind(&mut self, head: u64, tail: &[u64], s: u16) {
        if s == 0 { self.or_unbind(head, tail) } else { self.or_shl(head, tail, s - 1) }
    }

    pub(crate) fn shl(&self, s: u16) -> Self {
        let mut out = Self::empty();
        out.or_shl(self.head, &self.tail, s);
        out.trim();
        out
    }

    pub(crate) fn unbind(&self) -> Self {
        let mut out = Self::empty();
        out.or_unbind(self.head, &self.tail);
        out.trim();
        out
    }

    pub(crate) fn or_into(&mut self, o: &Self) {
        self.or_shl(o.head, &o.tail, 0);
    }

    pub(crate) fn min_ge(&self, cutoff: u16) -> Option<u16> { min_ge_words(self.head, &self.tail, cutoff) }
}

/// The bitset of a freshly built node from its children's pointer bitsets. `child` yields
/// the core's `(head, tail)` and the pointer's shift, or `None` for a closed pointer.
#[inline]
pub(crate) fn combine_bvset<'a, 'b>(e: &Expr<'a>, child: impl Fn(ExprPtr<'a>) -> Option<(u64, &'b [u64], u16)>) -> BvSet {
    // Fast path: every child is tail-less and its shifted head fits in the head word.
    #[inline]
    fn small<'a, 'b>(child: &impl Fn(ExprPtr<'a>) -> Option<(u64, &'b [u64], u16)>, p: ExprPtr<'a>, unbind: bool) -> Option<u64> {
        match child(p) {
            None => Some(0),
            Some((h, t, s)) => {
                if !t.is_empty() { return None; }
                let s = if unbind { if s == 0 { return Some(h >> 1); } s - 1 } else { s } as u32;
                if s < 64 && (s == 0 || h >> (64 - s) == 0) { Some(h << s) } else { None }
            }
        }
    }
    let fast = match e {
        Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. }
        | Expr::StringLit { .. } | Expr::NatLit { .. } => Some(0),
        Expr::Var { dbj_idx } => if *dbj_idx < 64 { Some(1u64 << dbj_idx) } else { None },
        Expr::App { fun, arg } => small(&child, *fun, false).and_then(|a| small(&child, *arg, false).map(|b| a | b)),
        Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } =>
            small(&child, *binder_type, false).and_then(|a| small(&child, *body, true).map(|b| a | b)),
        Expr::Let { binder_type, val, body, .. } =>
            small(&child, *binder_type, false).and_then(|a| small(&child, *val, false).and_then(|b| small(&child, *body, true).map(|c| a | b | c))),
        Expr::Proj { structure, .. } => small(&child, *structure, false),
    };
    if let Some(head) = fast { return BvSet { head, tail: Vec::new() }; }
    let mut out = BvSet::empty();
    let add = |out: &mut BvSet, p: ExprPtr<'a>, unbind: bool| {
        if let Some((h, t, s)) = child(p) {
            if unbind { out.or_shl_unbind(h, t, s) } else { out.or_shl(h, t, s) }
        }
    };
    match e {
        Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. }
        | Expr::StringLit { .. } | Expr::NatLit { .. } => {}
        Expr::Var { dbj_idx } => out.set(*dbj_idx),
        Expr::App { fun, arg } => { add(&mut out, *fun, false); add(&mut out, *arg, false); }
        Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
            add(&mut out, *binder_type, false); add(&mut out, *body, true);
        }
        Expr::Let { binder_type, val, body, .. } => {
            add(&mut out, *binder_type, false); add(&mut out, *val, false); add(&mut out, *body, true);
        }
        Expr::Proj { structure, .. } => add(&mut out, *structure, false),
    }
    out.trim();
    out
}

/// Flat storage of the tails of all cores with loose indices `>= 64`. A core has a tail
/// iff `nlbv > 64`, and since the last word holds index `nlbv - 1` the trimmed length is
/// exactly `ceil(nlbv / 64) - 1`; so only the offset needs storing, keyed by core index.
#[derive(Debug, Default)]
pub(crate) struct BvTails {
    words: Vec<u64>,
    offsets: FxHashMap<u32, u32>,
}

impl BvTails {
    pub(crate) fn clear(&mut self) { self.words.clear(); self.offsets.clear(); }
    pub(crate) fn count(&self) -> usize { self.offsets.len() }
    pub(crate) fn total_words(&self) -> usize { self.words.len() }

    /// Number of tail words of a core with `nlbv` loose bvars.
    #[inline]
    pub(crate) fn len_for(nlbv: u16) -> usize { if nlbv <= 64 { 0 } else { (nlbv as usize + 63) / 64 - 1 } }

    /// Store the (non-empty, trimmed) tail of core `idx`.
    pub(crate) fn push(&mut self, idx: usize, nlbv: u16, tail: &[u64]) {
        debug_assert_eq!(tail.len(), Self::len_for(nlbv), "tail length disagrees with nlbv");
        let off = self.words.len();
        assert!(off < u32::MAX as usize && idx < u32::MAX as usize, "too many loose-bvar tail words");
        self.words.extend_from_slice(tail);
        self.offsets.insert(idx as u32, off as u32);
    }

    #[inline]
    pub(crate) fn get(&self, idx: usize, nlbv: u16) -> &[u64] {
        let n = Self::len_for(nlbv);
        if n == 0 { return &[]; }
        let off = self.offsets[&(idx as u32)] as usize;
        &self.words[off..off + n]
    }
}

pub(crate) struct CanonMemo<'a> {
    /// One slot per export-DAG core, `(amount, cutoff, result)` with `amount == 0` meaning
    /// empty; only used when `with_slots` (the parser: one rebuild per core is the rule,
    /// and a `Vec` is half the size of a hash map over millions of cores).
    slots: Vec<(u16, u16, ExprPtr<'a>)>,
    use_slots: bool,
    /// Everything else: `(core, amount, cutoff)` -> `core` with `amount` subtracted from
    /// every loose index `>= cutoff`.
    map: FxHashMap<(CorePtr<'a>, u16, u16), ExprPtr<'a>>,
}

impl<'a> CanonMemo<'a> {
    pub(crate) fn new() -> Self { Self { slots: Vec::new(), use_slots: false, map: new_fx_hash_map() } }
    pub(crate) fn with_slots() -> Self { Self { use_slots: true, ..Self::new() } }

    #[inline]
    fn slot(&self, c: CorePtr<'a>) -> Option<usize> {
        if self.use_slots && c.dag_marker() == DagMarker::ExportFile { Some(c.idx()) } else { None }
    }

    pub(crate) fn get(&self, c: CorePtr<'a>, amount: u16, cutoff: u16) -> Option<ExprPtr<'a>> {
        if let Some(i) = self.slot(c) {
            if let Some(&(a, k, r)) = self.slots.get(i) { if a == amount && k == cutoff { return Some(r); } }
        }
        self.map.get(&(c, amount, cutoff)).copied()
    }

    pub(crate) fn put(&mut self, c: CorePtr<'a>, amount: u16, cutoff: u16, r: ExprPtr<'a>) {
        if let Some(i) = self.slot(c) {
            if i >= self.slots.len() { self.slots.resize(i + 1, (0, 0, r)); }
            if self.slots[i].0 == 0 { self.slots[i] = (amount, cutoff, r); return; }
        }
        self.map.insert((c, amount, cutoff), r);
    }
}

/// What the canonicalization needs from a DAG builder. Implemented by `TcCtx` and by the
/// parser, which builds the export DAG itself; both must produce identical cores.
pub(crate) trait OsnfBuilder<'a> {
    fn c_read(&self, c: CorePtr<'a>) -> Expr<'a>;
    fn c_app(&mut self, f: ExprPtr<'a>, a: ExprPtr<'a>) -> ExprPtr<'a>;
    fn c_lambda(&mut self, n: NamePtr<'a>, s: BinderStyle, ty: ExprPtr<'a>, body: ExprPtr<'a>) -> ExprPtr<'a>;
    fn c_pi(&mut self, n: NamePtr<'a>, s: BinderStyle, ty: ExprPtr<'a>, body: ExprPtr<'a>) -> ExprPtr<'a>;
    fn c_let(&mut self, n: NamePtr<'a>, ty: ExprPtr<'a>, val: ExprPtr<'a>, body: ExprPtr<'a>, nondep: bool) -> ExprPtr<'a>;
    fn c_proj(&mut self, n: NamePtr<'a>, idx: u32, s: ExprPtr<'a>) -> ExprPtr<'a>;
    fn c_memo(&mut self) -> &mut CanonMemo<'a>;
    /// The loose-bvar bitset of a core (`head`, `tail`).
    fn c_core_bvset(&self, c: CorePtr<'a>) -> (u64, &[u64]);
    /// Trace hook: a node rebuilt by `unshift_core`.
    fn c_note_unshift(&mut self) {}

    /// Smallest loose index of `e` that is `>= cutoff`, if any.
    fn min_bvar_ge(&self, e: ExprPtr<'a>, cutoff: u16) -> Option<u16> {
        if e.is_closed() { return None; }
        let (h, t) = self.c_core_bvset(e.core);
        min_ge_words(h, t, cutoff.saturating_sub(e.shift)).map(|m| m + e.shift)
    }

    /// The shift a binder can extract through itself from `body`: one less than the
    /// smallest loose index `>= 1` in the body — `Theory.lean`'s `fvar_lb_val (lam body)`.
    fn body_lb(&mut self, body: ExprPtr<'a>) -> Option<u16> {
        if body.is_closed() { return None; }
        self.min_bvar_ge(body, 1).map(|m| m - 1)
    }

    /// `adjust_child`: subtract `amount` from every loose bvar index `>= cutoff`.
    /// Precondition: every such index is `>= cutoff + amount`.
    fn unshift(&mut self, e: ExprPtr<'a>, amount: u16, cutoff: u16) -> ExprPtr<'a> {
        if amount == 0 || e.is_closed() { return e; }
        #[cfg(debug_assertions)]
        if let Some(i) = self.min_bvar_ge(e, cutoff) {
            assert!(i >= cutoff + amount, "unshift precondition violated: core#{} shift={} cutoff={} amount={} smallest index >= cutoff is {}", e.core.idx(), e.shift, cutoff, amount, i);
        }
        if e.shift >= cutoff {
            // Every loose index of `e` is `>= e.shift >= cutoff`: the whole thing moves.
            if e.shift >= amount {
                return ExprPtr::new(e.core, e.shift - amount);
            }
            // A core that is not canonical (smallest loose index above 0): push the
            // remainder into it.
            return self.unshift_core(e.core, amount - e.shift, 0);
        }
        let r = self.unshift_core(e.core, amount, cutoff - e.shift);
        r.shift_up(e.shift)
    }

    fn unshift_core(&mut self, c: CorePtr<'a>, amount: u16, cutoff: u16) -> ExprPtr<'a> {
        if let Some(r) = self.c_memo().get(c, amount, cutoff) { return r; }
        self.c_note_unshift();
        let r = match self.c_read(c) {
            Expr::Var { dbj_idx } => {
                assert!(dbj_idx < cutoff, "unshift_core: loose index {} >= cutoff {} but < cutoff + amount {}", dbj_idx, cutoff, cutoff + amount);
                ExprPtr::new(c, 0)
            }
            Expr::App { fun, arg } => {
                let f = self.unshift(fun, amount, cutoff);
                let a = self.unshift(arg, amount, cutoff);
                self.c_app(f, a)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body } => {
                let t = self.unshift(binder_type, amount, cutoff);
                let b = self.unshift(body, amount, cutoff + 1);
                self.c_lambda(binder_name, binder_style, t, b)
            }
            Expr::Pi { binder_name, binder_style, binder_type, body } => {
                let t = self.unshift(binder_type, amount, cutoff);
                let b = self.unshift(body, amount, cutoff + 1);
                self.c_pi(binder_name, binder_style, t, b)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep } => {
                let t = self.unshift(binder_type, amount, cutoff);
                let v = self.unshift(val, amount, cutoff);
                let b = self.unshift(body, amount, cutoff + 1);
                self.c_let(binder_name, t, v, b, nondep)
            }
            Expr::Proj { ty_name, idx, structure } => {
                let s = self.unshift(structure, amount, cutoff);
                self.c_proj(ty_name, idx, s)
            }
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. }
            | Expr::NatLit { .. } | Expr::StringLit { .. } => ExprPtr::closed(c),
        };
        self.c_memo().put(c, amount, cutoff, r);
        r
    }
}

#[cfg(test)]
mod tests {
    use super::BvSet;
    use std::collections::BTreeSet;

    fn of(s: &BTreeSet<u16>) -> BvSet {
        let mut b = BvSet::empty();
        for &i in s { b.set(i); }
        b
    }

    /// Bitset operations agree with the naive set semantics across word boundaries.
    #[test]
    fn bvset_matches_naive_sets() {
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for _ in 0..2000 {
            let n = (rnd() % 6) as usize;
            let a: BTreeSet<u16> = (0..n).map(|_| (rnd() % 200) as u16).collect();
            let b: BTreeSet<u16> = (0..n).map(|_| (rnd() % 200) as u16).collect();
            let s = (rnd() % 140) as u16;
            let cut = (rnd() % 200) as u16;
            let (ba, bb) = (of(&a), of(&b));
            assert_eq!(ba.shl(s), of(&a.iter().map(|i| i + s).collect()), "shl {:?} {}", a, s);
            assert_eq!(ba.unbind(), of(&a.iter().filter(|&&i| i > 0).map(|i| i - 1).collect()), "unbind {:?}", a);
            let mut u = ba.clone(); u.or_into(&bb);
            assert_eq!(u, of(&a.union(&b).cloned().collect()));
            assert_eq!(ba.min_ge(cut), a.range(cut..).next().cloned(), "min_ge {:?} {}", a, cut);
        }
    }
}
