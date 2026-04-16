use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecursorData, ReducibilityHint,
};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, BigUintPtr, Config, DagMarker, ExprPtr, FxHashMap, FxIndexMap,
    LeanDag, LevelPtr, LevelsPtr, NamePtr, SPtr, StringPtr,
};
use num_bigint::BigUint;
use serde::{ Deserialize, Deserializer };
use serde::de::{Error as DeError, Visitor};
use std::error::Error;
use std::io::BufRead;
use std::sync::Arc;
use std::borrow::Cow;
use std::fmt;

fn check_semver<'a>(meta: &FileMeta<'a>) -> Result<(), Box<dyn Error>> {
    const MIN_SEMVER : semver::Version = semver::Version::new(3, 1, 0);
    const MAX_SEMVER : semver::Version = semver::Version::new(3, 2, 0);
    let export_file_semver = semver::Version::parse(&meta.format.version)?;
    if export_file_semver < MIN_SEMVER {
        return Err(Box::from(format!(
            "export format version is less than the minimum supported version. Found {}, but min supported is {}",
            export_file_semver, MIN_SEMVER
        )))
    } else if export_file_semver >= MAX_SEMVER {
        return Err(Box::from(format!(
            "export format version is greater than the maximum supported version. Found {}, but max (exclusive) supported is {}",
            export_file_semver, MAX_SEMVER
        )))
    } else {
        Ok(())
    }
}

pub struct Parser<'a, R: BufRead> {
    buf_reader: R,
    line_num: usize,
    dag: LeanDag<'a>,
    declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
    /// Tracks axiom names that were found in the export file, but not white-listed,
    /// for use when `unpermitted_axiom_hard_error: false`
    skipped: Vec<String>,
    mutual_block_sizes: FxHashMap<NamePtr<'a>, (usize, usize)>,
    osnf_count: u32,
    /// Maps parser expression index → (DAG index, shift). Parser indices are sequential
    /// (matching the export file). The SPtr for expression i is
    /// SPtr::new(Ptr::from(ExportFile, remap.0), remap.1).
    expr_remap: Vec<(usize, u16)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct FormatMeta<'a> {
    version: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>,
    format: FormatMeta<'a>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum BackRef {
    #[serde(alias = "in")]
    In(u32),
    #[serde(alias = "il")]
    Il(u32),
    #[serde(alias = "ie")]
    Ie(u32),
}

impl BackRef {
    fn assert_in(self, insert_result: (usize, bool)) {
        assert!(insert_result.1);
        let lhs = u32::try_from(insert_result.0).unwrap();
        assert_eq!(self, BackRef::In(lhs))
    }

    fn assert_il(self, insert_result: (usize, bool)) {
        assert!(insert_result.1);
        let lhs = u32::try_from(insert_result.0).unwrap();
        assert_eq!(self, BackRef::Il(lhs))
    }

    fn assert_ie(self, insert_result: (usize, bool)) {
        assert!(insert_result.1);
        let lhs = u32::try_from(insert_result.0).unwrap();
        assert_eq!(self, BackRef::Ie(lhs))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct ExportJsonObject<'a> {
    #[serde(flatten)]
    val: ExportJsonVal<'a>,
    #[serde(flatten)]
    i: Option<BackRef>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct RecursorRule {
    ctor: u32,
    nfields: u16,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct IndInfo {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    all: Vec<u32>,
    ctors: Vec<u32>,
    #[serde(rename = "isRec")]
    is_rec: bool,
    #[serde(rename = "isReflexive")]
    is_reflexive: bool,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numNested")]
    num_nested: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Constructor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    cidx: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numFields")]
    num_fields: u16,
    induct: u32
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Recursor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numMotives")]
    num_motives: u16,
    #[serde(rename = "numMinors")]
    num_minors: u16,
    rules: Vec<RecursorRule>,
    all: Vec<u32>,
    k: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum ExportJsonVal<'a> {
    // The exporter metadata, incl. info about the lean, exporter, and format versions used
    // to create the export file.
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr {
        pre: u32,
        str: Cow<'a, str>
    },
    #[serde(rename = "num")]
    NameNum {
        pre: u32,
        i: u32
    },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(rename = "natVal", deserialize_with = "deserialize_biguint_from_string")]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData {
        expr: u32,
        data: serde_json::Value
    },
    #[serde(rename = "letE")]
    ExprLet {
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool
    },
    #[serde(rename = "const")]
    ExprConst {
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32 
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle

    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: u32,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort(u32),
    #[serde(rename = "bvar")]
    ExprBVar(u16),
    #[serde(rename = "axiom")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool
    },
    #[serde(rename = "thm")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "def")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool
    },
    #[serde(rename = "quot")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind
    },
    #[serde(rename = "inductive")]
    Inductive {
        #[serde(rename = "types")]
        ind_vals: Vec<IndInfo>,
        #[serde(rename = "ctors")]
        ctor_vals: Vec<Constructor>,
        #[serde(rename = "recs")]
        rec_vals: Vec<Recursor>
    },
}

pub(crate) fn parse_export_file<'p, R: BufRead>(
    buf_reader: R,
    config: Config,
    estimated_exprs: usize,

) -> Result<(crate::util::ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config, estimated_exprs);
    let mut line_buffer = String::new();

    loop {
        let amt = parser.buf_reader.read_line(&mut line_buffer)?;
        if amt == 0 {
            break
        }
        parser.go1(line_buffer.as_str())?;
        parser.line_num += 1;
        line_buffer.clear();
    }
    
    // If the execution config has `unknown_pp_declar_hard_error: true`, and a `pp_declars` 
    // that includes `foo`, then we return early with an error if no `foo` declaration is present 
    // in the export file.
    if parser.config.unknown_pp_declar_hard_error {
        if let Some(pp_declars) = parser.config.pp_declars.as_ref() {
            let mut pp_declar_names = pp_declars.iter().map(|s| s.as_str()).collect::<crate::util::FxHashSet<&str>>();
            for declar_name in parser.declars.keys() {
                let n = parser.name_to_string(*declar_name);
                pp_declar_names.remove(n.as_str());
            }
            if pp_declar_names.len() > 0 {
                let list = pp_declar_names.into_iter().collect::<Vec<&str>>();
                return Err(Box::from(format!("these pp_declars were not found in the exported environment: {:#?}", list)))
            }
        }
    }
    
    let dag_size = parser.dag.exprs.len();
    eprintln!("SPtr parse: {} parser entries → {} DAG entries, {} OSNF-shifted",
        parser.expr_remap.len(), dag_size, parser.osnf_count);
    let name_cache = parser.dag.mk_name_cache();
    let export_file = crate::util::ExportFile {
        dag: parser.dag,
        declars: parser.declars,
        notations: parser.notations,
        name_cache,
        config: parser.config,
        mutual_block_sizes: parser.mutual_block_sizes,
    };
    Ok((export_file, parser.skipped))
}

impl<'a, R: BufRead> Parser<'a, R> {
    pub fn new(buf_reader: R, config: Config, estimated_exprs: usize) -> Self {
        Self {
            buf_reader,
            line_num: 0usize,
            dag: LeanDag::with_capacity(&config, estimated_exprs),
            declars: new_fx_index_map(),
            notations: new_fx_hash_map(),
            config,
            skipped: Vec::new(),
            mutual_block_sizes: new_fx_hash_map(),
            osnf_count: 0,
            expr_remap: Vec::new(),
        }
    }
    
    fn axiom_permitted(&self, n: NamePtr<'a>) -> bool {
        self.config.unsafe_permit_all_axioms ||
            self.config.permitted_axioms.as_ref().map(|v| v.contains(&self.name_to_string(n))).unwrap_or(false)
    }

    fn num_loose_bvars(&self, e: ExprPtr<'a>) -> u16 {
        self.dag.expr_nlbv[e.idx()]
    }

    fn has_fvars_ptr(&self, e: ExprPtr<'a>) -> bool { self.dag.exprs.get_index(e.idx()).unwrap().has_fvars() }

    /// Find or create Var(0) in the DAG. Returns its ExprPtr.
    fn find_or_insert_var0(&mut self) -> ExprPtr<'a> {
        let hash = hash64!(crate::expr::VAR_HASH, 0u16);
        let (dag_idx, _) = self.insert_expr(Expr::Var {
            dbj_idx: 0, hash,
        });
        crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
    }

    fn get_name_ptr(&self, idx: u32) -> NamePtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.dag.names.len());
        out
    }

    fn get_level_ptr(&self, idx: u32) -> LevelPtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.dag.levels.len());
        out
    }
    fn get_names(&self, idxs: &[u32]) -> Vec<NamePtr<'a>> {
        let mut names = Vec::new();
        for idx in idxs.iter().copied() {
            assert!(self.dag.names.get_index(idx as usize).is_some());
            names.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
        }
        names
    }

    fn get_uparams_ptr(&mut self, name_idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for name_idx in name_idxs.iter().copied() {
            let name_ptr = self.get_name_ptr(name_idx);
            let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
            // Has to already exist
            let idx = self.dag.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap();
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_levels_ptr(&mut self, idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for idx in idxs.iter().copied() {
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    /// Insert an expression and track its nlbv in the parallel Vec.
    fn insert_expr(&mut self, e: Expr<'a>) -> (usize, bool) {
        let nlbv = e.num_loose_bvars();
        let result = self.dag.exprs.insert_full(e);
        if result.1 { self.dag.expr_nlbv.push(nlbv); }
        result
    }

    fn get_expr_sptr(&self, idx: u32) -> SPtr<'a> {
        let (dag_idx, shift) = self.expr_remap[idx as usize];
        SPtr::new(crate::util::Ptr::from(DagMarker::ExportFile, dag_idx), shift)
    }

    /// Get the ExprPtr for a declaration type/value (must be closed, shift == CLOSED_SHIFT).
    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        let (dag_idx, shift) = self.expr_remap[idx as usize];
        debug_assert!(shift == SPtr::CLOSED_SHIFT, "get_expr_ptr: expected CLOSED_SHIFT for declaration expr, got shift={}", shift);
        crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
    }

    /// Record the DAG index and shift for a parser expression.
    fn record_expr(&mut self, dag_idx: usize, shift: u16) {
        self.expr_remap.push((dag_idx, shift));
    }

    // Used for the axiom whitelist feature.
    fn name_to_string(&self, n: NamePtr<'a>) -> String {
        match self.dag.names.get_index(n.idx()).copied().unwrap() {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + self.dag.strings.get_index(sfx.idx()).unwrap()
            }
            Name::Num(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + format!("{}", sfx).as_str()
            }
        }
    }

    fn go1(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        use ExportJsonVal::*;
        let ExportJsonObject {val, i: assigned_idx} = serde_json::from_str::<ExportJsonObject>(line)?;
        match val {
            Metadata(json_val) => {
                let _ = check_semver(&json_val)?;
            }
            NameStr {pre, str} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = StringPtr::from(
                    DagMarker::ExportFile, 
                    self.dag.strings.insert_full(std::borrow::Cow::Owned(str.to_string())).0
                );

                let insert_result = {
                    let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Str(pfx, sfx, hash))
                };
                assigned_idx.unwrap().assert_in(insert_result);
            }
            NameNum {pre, i} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = i as u64;
                let insert_result = {
                    let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Num(pfx, sfx, hash))
                };
                assigned_idx.unwrap().assert_in(insert_result);
            }
            NatLit(big_uint) => {
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, but export file contains a nat literal {:?}", line)
                    ))
                }
                let num_ptr = BigUintPtr::from(DagMarker::ExportFile, self.dag.bignums.as_mut().unwrap().insert_full(big_uint).0);
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
                    self.insert_expr(Expr::NatLit { ptr: num_ptr, hash })
                };
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, found {:?}", line)
                    ))
                }
                self.record_expr(dag_idx, SPtr::CLOSED_SHIFT);
            }
            StrLit(cow_str) => {
                if !self.config.string_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("String lit extension disallowed by checker execution config, but export file contains a string literal {:?}", line)
                    ))
                }
                let s = cow_str.to_string();
                let string_ptr = StringPtr::from(
                    DagMarker::ExportFile,
                    self.dag.strings.insert_full(crate::util::CowStr::Owned(s)).0
                );
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
                    self.insert_expr(Expr::StringLit { ptr: string_ptr, hash })
                };
                self.record_expr(dag_idx, SPtr::CLOSED_SHIFT);
            }
            LevelSucc(l) => {
                let l = self.get_level_ptr(l);
                let insert_result = {
                    let hash = hash64!(crate::level::SUCC_HASH, l);
                    self.dag.levels.insert_full(Level::Succ(l, hash))
                };
                assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::MAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::Max(l, r, hash))
                };
                assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelIMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::IMAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::IMax(l, r, hash))
                };
                assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelParam(var_idx) => {
                 let n = self.get_name_ptr(var_idx);
                 let insert_result = {
                     let hash = hash64!(crate::level::PARAM_HASH, n);
                     self.dag.levels.insert_full(Level::Param(n, hash))
                 };
                assigned_idx.unwrap().assert_il(insert_result);
            }
            ExprSort(level) => {
                let level = self.get_level_ptr(level);
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::SORT_HASH, level);
                    self.insert_expr(Expr::Sort { level, hash })
                };
                self.record_expr(dag_idx, SPtr::CLOSED_SHIFT);
            }
            ExprMData {..} => {
                panic!("Expr.mdata not supported");
            }
            ExprConst {name, levels} => {
                let name = self.get_name_ptr(name);
                let levels = self.get_levels_ptr(&levels);
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::CONST_HASH, name, levels);
                    self.insert_expr(Expr::Const { name, levels, hash })
                };
                self.record_expr(dag_idx, SPtr::CLOSED_SHIFT);
            }
            ExprApp {fun, arg} => {
                let fun_sptr = self.get_expr_sptr(fun);
                let arg_sptr = self.get_expr_sptr(arg);
                // Effective nlbv for an SPtr child:
                // if core nlbv == 0 then 0, else core_nlbv + shift
                let fun_core_nlbv = self.num_loose_bvars(fun_sptr.core);
                let arg_core_nlbv = self.num_loose_bvars(arg_sptr.core);
                let fun_eff_nlbv = if fun_core_nlbv == 0 { 0 } else { fun_core_nlbv + fun_sptr.shift };
                let arg_eff_nlbv = if arg_core_nlbv == 0 { 0 } else { arg_core_nlbv + arg_sptr.shift };
                // Compute min_shift from open children for OSNF. CLOSED_SHIFT = all closed.
                let min_shift = if fun_eff_nlbv == 0 && arg_eff_nlbv == 0 { SPtr::CLOSED_SHIFT }
                    else if fun_eff_nlbv == 0 { arg_sptr.shift }
                    else if arg_eff_nlbv == 0 { fun_sptr.shift }
                    else { fun_sptr.shift.min(arg_sptr.shift) };
                if min_shift > 0 && min_shift != SPtr::CLOSED_SHIFT { self.osnf_count += 1; }
                // Build core children with min_shift subtracted (only for open children)
                let core_fun = if fun_eff_nlbv == 0 { fun_sptr } else { SPtr::new(fun_sptr.core, fun_sptr.shift - min_shift) };
                let core_arg = if arg_eff_nlbv == 0 { arg_sptr } else { SPtr::new(arg_sptr.core, arg_sptr.shift - min_shift) };
                let core_fun_nlbv = if fun_core_nlbv == 0 { 0 } else { fun_core_nlbv + core_fun.shift };
                let core_arg_nlbv = if arg_core_nlbv == 0 { 0 } else { arg_core_nlbv + core_arg.shift };
                let core_nlbv = core_fun_nlbv.max(core_arg_nlbv);
                let locals = self.has_fvars_ptr(fun_sptr.core) || self.has_fvars_ptr(arg_sptr.core);
                let hash = hash64!(crate::expr::APP_HASH, core_fun, core_arg);
                let (core_idx, _) = self.insert_expr(Expr::App {
                    fun: core_fun, arg: core_arg, num_loose_bvars: core_nlbv,
                    has_fvars: locals, hash,
                });
                self.record_expr(core_idx, min_shift);
            }
            ExprBVar(dbj_idx) => {
                // Only Var(0) lives in the DAG. BVar(k) is represented as SPtr(var0, k).
                let var0_ptr = self.find_or_insert_var0();
                self.record_expr(var0_ptr.idx(), dbj_idx);
            }
            ExprLambda {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let ty_sptr = self.get_expr_sptr(binder_type);
                let body_sptr = self.get_expr_sptr(body);
                let ty_core_nlbv = self.num_loose_bvars(ty_sptr.core);
                let body_core_nlbv = self.num_loose_bvars(body_sptr.core);
                let ty_eff_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + ty_sptr.shift };
                let body_eff_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + body_sptr.shift };
                // For binder body: outer contribution is body_eff_nlbv.saturating_sub(1)
                // min_shift from open children: ty's shift vs body's shift.saturating_sub(1)
                // But we need to be careful: the body is under a binder, so its shift
                // contributes (shift - 1) to the outer expression's fvar_lb.
                // For OSNF, we want min_shift = min of effective fvar_lb contributions.
                // ty contribution: ty_sptr.shift (if ty is open)
                // body contribution: body_sptr.shift.saturating_sub(1) (if body has nlbv > 1,
                //   or body_sptr.shift > 0 when body has nlbv == 1)
                let body_outer_shift = if body_eff_nlbv <= 1 { None }
                    else { Some(body_sptr.shift.saturating_sub(1)) };
                let min_shift = match (ty_eff_nlbv > 0, body_outer_shift) {
                    (false, None) => SPtr::CLOSED_SHIFT,
                    (true, None) => ty_sptr.shift,
                    (false, Some(bs)) => bs,
                    (true, Some(bs)) => ty_sptr.shift.min(bs),
                };
                if min_shift > 0 && min_shift != SPtr::CLOSED_SHIFT { self.osnf_count += 1; }
                // Build core children: only adjust shifts for open children that contributed
                let core_ty = if ty_eff_nlbv == 0 { ty_sptr } else { SPtr::new(ty_sptr.core, ty_sptr.shift - min_shift) };
                let core_body = if body_eff_nlbv > 1 { SPtr::new(body_sptr.core, body_sptr.shift - min_shift) } else { body_sptr };
                let core_ty_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + core_ty.shift };
                let core_body_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + core_body.shift };
                let core_nlbv = core_ty_nlbv.max(core_body_nlbv.saturating_sub(1));
                let locals = self.has_fvars_ptr(ty_sptr.core) || self.has_fvars_ptr(body_sptr.core);
                let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, core_ty, core_body);
                let (core_idx, _) = self.insert_expr(Expr::Lambda {
                    binder_name, binder_style: binder_info, binder_type: core_ty, body: core_body,
                    num_loose_bvars: core_nlbv, has_fvars: locals, hash,
                });
                self.record_expr(core_idx, min_shift);
            }
            ExprPi {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let ty_sptr = self.get_expr_sptr(binder_type);
                let body_sptr = self.get_expr_sptr(body);
                let ty_core_nlbv = self.num_loose_bvars(ty_sptr.core);
                let body_core_nlbv = self.num_loose_bvars(body_sptr.core);
                let ty_eff_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + ty_sptr.shift };
                let body_eff_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + body_sptr.shift };
                let body_outer_shift = if body_eff_nlbv <= 1 { None }
                    else { Some(body_sptr.shift.saturating_sub(1)) };
                let min_shift = match (ty_eff_nlbv > 0, body_outer_shift) {
                    (false, None) => SPtr::CLOSED_SHIFT,
                    (true, None) => ty_sptr.shift,
                    (false, Some(bs)) => bs,
                    (true, Some(bs)) => ty_sptr.shift.min(bs),
                };
                if min_shift > 0 && min_shift != SPtr::CLOSED_SHIFT { self.osnf_count += 1; }
                let core_ty = if ty_eff_nlbv == 0 { ty_sptr } else { SPtr::new(ty_sptr.core, ty_sptr.shift - min_shift) };
                let core_body = if body_eff_nlbv > 1 { SPtr::new(body_sptr.core, body_sptr.shift - min_shift) } else { body_sptr };
                let core_ty_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + core_ty.shift };
                let core_body_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + core_body.shift };
                let core_nlbv = core_ty_nlbv.max(core_body_nlbv.saturating_sub(1));
                let locals = self.has_fvars_ptr(ty_sptr.core) || self.has_fvars_ptr(body_sptr.core);
                let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, core_ty, core_body);
                let (core_idx, _) = self.insert_expr(Expr::Pi {
                    binder_name, binder_style: binder_info, binder_type: core_ty, body: core_body,
                    num_loose_bvars: core_nlbv, has_fvars: locals, hash,
                });
                self.record_expr(core_idx, min_shift);
            }
            ExprLet {name, ty, value, body, nondep} => {
                let binder_name = self.get_name_ptr(name);
                let ty_sptr = self.get_expr_sptr(ty);
                let val_sptr = self.get_expr_sptr(value);
                let body_sptr = self.get_expr_sptr(body);
                let ty_core_nlbv = self.num_loose_bvars(ty_sptr.core);
                let val_core_nlbv = self.num_loose_bvars(val_sptr.core);
                let body_core_nlbv = self.num_loose_bvars(body_sptr.core);
                let ty_eff_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + ty_sptr.shift };
                let val_eff_nlbv = if val_core_nlbv == 0 { 0 } else { val_core_nlbv + val_sptr.shift };
                let body_eff_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + body_sptr.shift };
                // Body is under a binder; its outer contribution is body_eff_nlbv.saturating_sub(1)
                let body_outer_shift = if body_eff_nlbv <= 1 { None }
                    else { Some(body_sptr.shift.saturating_sub(1)) };
                // min_shift = min of all open children's effective shifts
                let mut min_shift = u16::MAX;
                if ty_eff_nlbv > 0 { min_shift = min_shift.min(ty_sptr.shift); }
                if val_eff_nlbv > 0 { min_shift = min_shift.min(val_sptr.shift); }
                if let Some(bs) = body_outer_shift { min_shift = min_shift.min(bs); }
                // min_shift == CLOSED_SHIFT means all children are closed
                if min_shift > 0 && min_shift != SPtr::CLOSED_SHIFT { self.osnf_count += 1; }
                let core_ty = if ty_eff_nlbv == 0 { ty_sptr } else { SPtr::new(ty_sptr.core, ty_sptr.shift - min_shift) };
                let core_val = if val_eff_nlbv == 0 { val_sptr } else { SPtr::new(val_sptr.core, val_sptr.shift - min_shift) };
                let core_body = if body_eff_nlbv > 1 { SPtr::new(body_sptr.core, body_sptr.shift - min_shift) } else { body_sptr };
                let core_ty_nlbv = if ty_core_nlbv == 0 { 0 } else { ty_core_nlbv + core_ty.shift };
                let core_val_nlbv = if val_core_nlbv == 0 { 0 } else { val_core_nlbv + core_val.shift };
                let core_body_nlbv = if body_core_nlbv == 0 { 0 } else { body_core_nlbv + core_body.shift };
                let core_nlbv = core_ty_nlbv.max(core_val_nlbv.max(core_body_nlbv.saturating_sub(1)));
                let locals = self.has_fvars_ptr(ty_sptr.core) || self.has_fvars_ptr(val_sptr.core) || self.has_fvars_ptr(body_sptr.core);
                let hash = hash64!(crate::expr::LET_HASH, binder_name, core_ty, core_val, core_body, nondep);
                let (core_idx, _) = self.insert_expr(Expr::Let {
                    binder_name,
                    binder_type: core_ty,
                    val: core_val,
                    body: core_body,
                    num_loose_bvars: core_nlbv,
                    has_fvars: locals,
                    hash,
                    nondep,
                });
                self.record_expr(core_idx, min_shift);
            }
            ExprProj {type_name, idx, structure: struct_} => {
                let ty_name = self.get_name_ptr(type_name);
                let struct_sptr = self.get_expr_sptr(struct_);
                let struct_core_nlbv = self.num_loose_bvars(struct_sptr.core);
                let struct_eff_nlbv = if struct_core_nlbv == 0 { 0 } else { struct_core_nlbv + struct_sptr.shift };
                let min_shift = if struct_eff_nlbv == 0 { SPtr::CLOSED_SHIFT } else { struct_sptr.shift };
                if min_shift > 0 && min_shift != SPtr::CLOSED_SHIFT { self.osnf_count += 1; }
                let core_struct = if struct_eff_nlbv == 0 { struct_sptr } else { SPtr::new(struct_sptr.core, struct_sptr.shift - min_shift) };
                let core_struct_nlbv = if struct_core_nlbv == 0 { 0 } else { struct_core_nlbv + core_struct.shift };
                let locals = self.has_fvars_ptr(struct_sptr.core);
                let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, core_struct);
                let (core_idx, _) = self.insert_expr(Expr::Proj {
                    ty_name,
                    idx,
                    structure: core_struct,
                    num_loose_bvars: core_struct_nlbv,
                    has_fvars: locals,
                    hash,
                });
                self.record_expr(core_idx, min_shift);
            }
            Axiom {name, ty, uparams, is_unsafe} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let info = DeclarInfo { name, ty, uparams };
                let axiom = Declar::Axiom { info };
                if self.axiom_permitted(name) {
                    assert!(self.declars.insert(name, axiom).is_none());
                } else {
                    let name_string = self.name_to_string(name);
                    if self.config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!("export file declares unpermitted axiom {:?}", name_string)))
                    } else {
                        self.skipped.push(name_string)
                    }
                }
            }
            Defn {name, ty, uparams, value, hint, safety} => {
                assert!(!matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial));
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Definition { info, val, hint };
                assert!(self.declars.insert(name, definition).is_none());
            }
            Thm {name, ty, uparams, value} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let theorem = Declar::Theorem { info, val };
                assert!(self.declars.insert(name, theorem).is_none());
            }
            Opaque {name, ty, uparams, value, is_unsafe} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Opaque { info, val };
                assert!(self.declars.insert(name, definition).is_none());
            }
            Quot {name, ty, uparams, ..} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let quot = Declar::Quot { info };
                assert!(self.declars.insert(name, quot).is_none());
            }
            Inductive {ind_vals, ctor_vals, rec_vals} => {
                let block_start = self.declars.len();
                let block_size = ind_vals.len() + ctor_vals.len() + rec_vals.len();
                for IndInfo {name, ty, uparams, all, ctors, is_rec, num_nested, num_params, num_indices, is_unsafe, ..} in ind_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    self.mutual_block_sizes.insert(name, (block_start, block_size));
                    let uparams = self.get_uparams_ptr(&uparams);
                    let ty = self.get_expr_ptr(ty);
                    let all_ind_names =  Arc::from(self.get_names(&all)); 
                    let all_ctor_names = Arc::from(self.get_names(&ctors)); 
                    let inductive = Declar::Inductive(InductiveData {
                        info: DeclarInfo { name, uparams, ty },
                        is_recursive: is_rec,
                        is_nested: num_nested > 0,
                        num_params,
                        num_indices,
                        all_ind_names,
                        all_ctor_names,
                    });
                    assert!(self.declars.insert(name, inductive).is_none());
                }
                for Constructor {name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, ..}  in ctor_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let parent_inductive = self.get_name_ptr(induct);
                    let ctor_idx = cidx;
                    let ctor = Declar::Constructor(ConstructorData {
                        info,
                        inductive_name: parent_inductive,
                        ctor_idx,
                        num_params,
                        num_fields,
                    });
                    assert!(self.declars.insert(name, ctor).is_none());
                }
                for Recursor {name, uparams, ty, rules, is_unsafe, num_params, num_indices, num_motives, num_minors, k, all, ..} in rec_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let rules = rules.into_iter().map(|RecursorRule {rhs, ctor, nfields}| 
                        crate::env::RecRule {
                            val: self.get_expr_ptr(rhs),
                            ctor_name: self.get_name_ptr(ctor),
                            ctor_telescope_size_wo_params: nfields
                        }
                    ).collect::<Vec<_>>();
                    let all_inductives = self.get_names(&all);
                    let recursor = Declar::Recursor(RecursorData {
                        info,
                        all_inductives: Arc::from(all_inductives),
                        num_params,
                        num_indices,
                        num_motives,
                        num_minors,
                        rec_rules: Arc::from(rules),
                        is_k: k,
                    });
                    assert!(self.declars.insert(name, recursor).is_none())
                }
            }
        }
        Ok(())
    }
}

/// Needed because the lean4export format serializes nat literals as strings: 
/// https://github.com/leanprover/lean4export/blob/ddeb0869b0b5679b0104e16291ffd929fbaa6a48/format_ndjson.md?plain=1#L186
fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where D: Deserializer<'de> {
    use std::str::FromStr;
    struct BigUintStringVisitor;

    impl<'de> Visitor<'de> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E> where E: DeError {
            BigUint::from_str(v).map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E> where E: DeError {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}

mod semver_tests {
    use super::*;
    #[allow(dead_code)]
    fn mk_meta(s: &'static str) -> FileMeta<'static> {
        FileMeta {
            lean: LeanMeta { version: Cow::Borrowed(""), githash: Cow::Borrowed("") },
            exporter: ExporterMeta { version: Cow::Borrowed(""), name: Cow::Borrowed("") },
            format :FormatMeta { version: Cow::Borrowed(s) }
        }
    }

    #[test]
    fn test_ng() {
        let too_small = [
            "2.9.9",
            "2.9.99",
        ];
        let too_big = [
            "4.0.0",
            "4.1.0",
            "3.2.0",
            "3.2.1",
        ];

        for v in too_small {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
        for v in too_big {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
    }

    #[test]
    fn test_ok() {
        let ok = [
            "3.1.0",
            "3.1.9",
        ];
        for v in ok {
            assert!(check_semver(&mk_meta(v)).is_ok())
        }
    }
}
