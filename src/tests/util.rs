use crate::util::{Config, CowStr, ExportFile, CorePtr, LevelPtr, ExprPtr, TcCtx};
use rand::distr::Alphanumeric;
use rand::rngs::ThreadRng;
use std::error::Error;
use std::path::{Path, PathBuf};

pub(crate) fn test_export_file<A>(
    config_path: Option<&Path>,
    f: impl FnOnce(&ExportFile) -> A,
) -> Result<A, Box<dyn Error>> {
    let (export_file, _) = test_get_export_file(config_path)?;
    Ok(f(&export_file))
}

pub(crate) fn test_get_export_file<'p>(config_path: Option<&Path>) -> Result<(ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let config_file = match config_path {
        None => Config {
            export_file_path: Some(PathBuf::from("test_resources/Empty/export")),
            use_stdin: false,
            permitted_axioms: Some(Vec::new()),
            unpermitted_axiom_hard_error: true,
            nat_extension: false,
            string_extension: false,
            pp_declars: None,
            pp_options: crate::pretty_printer::PpOptions::default(),
            unknown_pp_declar_hard_error: true,
            pp_output_path: None,
            pp_to_stdout: false,
            num_threads: 1,
            print_success_message: true,
            print_axioms: true,
            unsafe_permit_all_axioms: false,
            max_declarations: 0,
            skip_declarations: 0,
            declaration_timeout_secs: 0,
            use_nanoda_tc: false,
            verify_defeq_cache: false,
            declaration_filter: None,
        },
        Some(config_path) => Config::try_from(config_path)?,
    };
    config_file.to_export_file()
}

#[allow(dead_code)]
pub(crate) fn test_export_file_should_panic<A>(config_path: Option<&Path>, f: impl FnOnce(&ExportFile) -> A) {
    // If there's an IO issue with actually getting the export file, we don't want
    // `should_panic` test to succeed, so we actually want to return success in this case.
    match test_get_export_file(config_path) {
        Err(..) => {}
        Ok((export_file, _)) => {
            f(&export_file);
        }
    }
}

pub(crate) fn test_ctx<'p, A>(path: Option<&Path>, f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
    test_export_file(path, |export_file| export_file.with_ctx(f))
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    #[cfg(test)]
    pub(crate) fn level_n(&mut self, mut l: LevelPtr<'t>, n: u64) -> LevelPtr<'t> {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn mk_succ_app(&mut self, n: usize) -> ExprPtr<'t> {
        let mut out = ExprPtr::closed(self.c_nat_zero().unwrap());
        let succ = ExprPtr::closed(self.c_nat_succ().unwrap());
        for _ in 0..n {
            out = self.mk_app(succ, out);
        }
        out
    }

    #[cfg(test)]
    pub(crate) fn param_quick(&mut self, s: &'static str) -> LevelPtr<'t> {
        let n = self.str1(&s);
        self.param(n)
    }
}

#[test]
fn check_empty() -> Result<(), Box<dyn Error>> {
    test_export_file(None, |export| {
        for declar in export.declars.values() {
            export.check_declar(declar);
        }
    })
}

/// The export format assigns each name/level/expression an explicit index. Those
/// indices need not be dense or in increasing order — the exporter only guarantees
/// that an item is emitted after the items it references. `LevelIndexOutOfOrder`
/// defines level index 2 before level index 1 (with 1 referencing 2). The parser
/// must resolve references via the explicit indices, not insertion position.
#[test]
fn check_level_index_out_of_order() -> Result<(), Box<dyn Error>> {
    test_export_file(
        Some(Path::new("test_resources/LevelIndexOutOfOrder/config.json")),
        |export| {
            assert_eq!(export.declars.len(), 1);
            for declar in export.declars.values() {
                export.check_declar(declar);
            }
        },
    )
}

/// `SparseNameIndex` uses name index 2 and expression index 4 with gaps (no name
/// index 1, no expressions 0..=3). The parser must tolerate sparse explicit indices.
#[test]
fn check_sparse_name_index() -> Result<(), Box<dyn Error>> {
    test_export_file(
        Some(Path::new("test_resources/SparseNameIndex/config.json")),
        |export| {
            assert_eq!(export.declars.len(), 1);
            for declar in export.declars.values() {
                export.check_declar(declar);
            }
        },
    )
}

#[test]
#[should_panic(expected = "infer_proj prop")]
fn check_proj_from_prop() {
    test_export_file_should_panic(
        Some(Path::new("test_resources/ProjFromProp/config.json")),
        |export| {
            for declar in export.declars.values() {
                export.check_declar(declar);
            }
        },
    )
}

pub(crate) fn rand_string<'t>(rng: &mut ThreadRng, size: usize) -> CowStr<'t> {
    use rand::RngExt;
    let rand_string: String = rng.sample_iter(&Alphanumeric).take(size).map(char::from).collect();
    CowStr::Owned(rand_string)
}

#[test]
fn hash_test0() -> Result<(), Box<dyn Error>> {
    use crate::hash64;
    use num_bigint::BigRng010;
    test_export_file(None, |export| {
        let mut rng = rand::rng();
        export.with_ctx(|ctx| {
            for size in 0..100 {
                for _ in 0..100 {
                    let s = rand_string(&mut rng, size);
                    let (l, r) = (ctx.mk_string_lit_quick(s.clone()), ctx.mk_string_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
                for _ in 0..100 {
                    let s = rng.random_biguint(size as u64);
                    let (l, r) = (ctx.mk_nat_lit_quick(s.clone()), ctx.mk_nat_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
            }
        })
    })
}

/// The shortest pair that used to have two representations: `λx. x #2` built as the lazily
/// shifted `(λx. x #1) + 1`, or directly with the shift baked into the body. The binder
/// constructors now extract the shift through the binder (`Theory.lean`'s `lam` rule,
/// `canon.rs`), so both routes must yield the same `(core, shift)`.
#[test]
fn osnf_canonical_under_binder() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let zero = ctx.zero();
        let ty = ctx.mk_sort(zero);
        let x = ctx.str1("x");
        let v0 = ctx.mk_var(0);
        // lazy route: build λx. x #1, then shift the whole term by 1
        let v1 = ctx.mk_var(1);
        let body1 = ctx.mk_app(v0, v1);
        let lam1 = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, body1);
        let lazy = lam1.shift_up(1);
        // baked route: build λx. x #2 directly
        let v2 = ctx.mk_var(2);
        let body2 = ctx.mk_app(v0, v2);
        let baked = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, body2);
        assert_eq!(lazy, baked, "lazy = {} +{}, baked = {} +{}", ctx.core_desc(lazy.core, 6), lazy.shift, ctx.core_desc(baked.core, 6), baked.shift);
        // and a binder nested inside a binder: under λx. λy., `#2` is the first free variable,
        // so λx. λy. y x #3 == ((λx. λy. y x #2) + 1)
        let y = ctx.str1("y");
        let (v1, v2, v3) = (ctx.mk_var(1), ctx.mk_var(2), ctx.mk_var(3));
        let inner = ctx.mk_app(v0, v1);
        let inner1 = ctx.mk_app(inner, v3);
        let lam_in = ctx.mk_lambda(y, crate::expr::BinderStyle::Default, ty, inner1);
        let baked2 = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, lam_in);
        let inner2 = ctx.mk_app(inner, v2);
        let lam_in2 = ctx.mk_lambda(y, crate::expr::BinderStyle::Default, ty, inner2);
        let lazy2 = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, lam_in2).shift_up(1);
        assert_eq!(lazy2, baked2, "nested: lazy = {} +{}, baked = {} +{}", ctx.core_desc(lazy2.core, 8), lazy2.shift, ctx.core_desc(baked2.core, 8), baked2.shift);
    })
}

/// Beyond 64 binders the extractable shift comes from the out-of-line bitset tail:
/// `λx. x #61` built directly, or `λx. x #51` built ten binders shallower and lazily
/// shifted by 10, must be one pointer, `(λx. x #1) + 60`.
#[test]
fn osnf_canonical_beyond_the_head_word() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let zero = ctx.zero();
        let ty = ctx.mk_sort(zero);
        let x = ctx.str1("x");
        let v0 = ctx.mk_var(0);
        let (v51, v61, v130) = (ctx.mk_var(51), ctx.mk_var(61), ctx.mk_var(130));
        let b_direct = ctx.mk_app(v0, v61);
        let direct = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, b_direct);
        let b_shallow = ctx.mk_app(v0, v51);
        let lazy = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, b_shallow).shift_up(10);
        assert_eq!(direct, lazy, "direct = {} +{}, lazy = {} +{}", ctx.core_desc(direct.core, 6), direct.shift, ctx.core_desc(lazy.core, 6), lazy.shift);
        assert_eq!(direct.shift, 60);
        // and well into the tail: λx. x #130 == (λx. x #1) + 129
        let b_far = ctx.mk_app(v0, v130);
        let far = ctx.mk_lambda(x, crate::expr::BinderStyle::Default, ty, b_far);
        assert_eq!(far.shift, 129);
        assert_eq!(far.core, direct.core);
    })
}
