use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecursorData, ReducibilityHint,
};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, BigUintPtr, Config, DagMarker, ExprPtr, FxHashMap, FxIndexMap,
    LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
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
    /// Maps parser expression index → DAG index. Parser indices are sequential
    /// (matching the export file), but DAG indices may differ due to OSNF core
    /// inserts and deduplication.
    expr_remap: Vec<usize>,
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
    
    let total_inserted = parser.expr_remap.len() + parser.osnf_count as usize;
    let dag_size = parser.dag.exprs.len();
    let dedup_pct = if total_inserted > 0 && dag_size <= total_inserted {
        100 - (100 * dag_size / total_inserted)
    } else { 0 };
    eprintln!("OSNF: {} expressions normalized, {} parser entries → {} DAG entries ({}% dedup from core sharing)",
        parser.osnf_count, parser.expr_remap.len(), dag_size, dedup_pct);
    let name_cache = parser.dag.mk_name_cache();
    let export_file = crate::util::ExportFile {
        dag: parser.dag,
        declars: parser.declars,
        notations: parser.notations,
        name_cache,
        config: parser.config,
        mutual_block_sizes: parser.mutual_block_sizes,
        osnf_core: None,
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

    fn has_fvars(&self, e: ExprPtr<'a>) -> bool { self.dag.exprs.get_index(e.idx()).unwrap().has_fvars() }

    fn struct_hash(&self, e: ExprPtr<'a>) -> u64 {
        self.dag.exprs.get_index(e.idx()).unwrap().get_struct_hash()
    }

    fn bloom(&self, e: ExprPtr<'a>) -> u32 {
        self.dag.exprs.get_index(e.idx()).unwrap().get_fvar_bloom()
    }

    fn expr_fvar_lb(&self, e: ExprPtr<'a>) -> u16 {
        self.dag.exprs.get_index(e.idx()).unwrap().get_fvar_lb()
    }

    /// Find or create BVar(idx) in the DAG. Returns its ExprPtr.
    fn find_or_insert_bvar(&mut self, idx: u16) -> ExprPtr<'a> {
        let hash = hash64!(crate::expr::VAR_HASH, idx);
        let fvar_bloom = crate::expr::bloom_single(idx);
        let (dag_idx, _) = self.insert_expr(Expr::Var {
            dbj_idx: idx, hash, struct_hash: crate::expr::VAR_HASH, fvar_bloom, fvar_lb: idx,
        });
        crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
    }

    /// Adjust a child expression for OSNF core extraction.
    /// The child is already in OSNF in the DAG. We need to reduce its shift by `amount`.
    /// - Shift(k, core) → Shift(k - amount, core) or core if k == amount
    /// - BVar(n) → BVar(n - amount)
    /// - Compound with fvar_lb=0 → use as-is (already a core)
    /// - nlbv <= cutoff → use as-is (bound var, not affected by outer shift)
    fn adjust_child(&mut self, child: ExprPtr<'a>, amount: u16, cutoff: u16) -> ExprPtr<'a> {
        let child_nlbv = self.dag.expr_nlbv[child.idx()];
        if child_nlbv <= cutoff { return child; }
        let child_expr = *self.dag.exprs.get_index(child.idx()).unwrap();
        match child_expr {
            Expr::Var { dbj_idx, .. } => {
                self.find_or_insert_bvar(dbj_idx - amount)
            }
            Expr::Shift { inner, amount: child_amount, cutoff: 0, .. } => {
                debug_assert!(child_amount as u16 >= amount);
                let new_amount = child_amount as u16 - amount;
                if new_amount == 0 {
                    inner
                } else {
                    let dag_idx = self.insert_shift(inner, new_amount);
                    crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
                }
            }
            _ => {
                // Compound with fvar_lb=0 (already a core). Use as-is.
                debug_assert!(child_expr.get_fvar_lb() == 0, "adjust_child: expected fvar_lb=0 for non-Shift compound, got {}", child_expr.get_fvar_lb());
                child
            }
        }
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

    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        let dag_idx = self.expr_remap[idx as usize];
        crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
    }

    /// Record the DAG index for a parser expression. Returns the ExprPtr.
    fn record_expr(&mut self, dag_idx: usize) -> ExprPtr<'a> {
        self.expr_remap.push(dag_idx);
        crate::util::Ptr::from(DagMarker::ExportFile, dag_idx)
    }

    /// Insert a Shift(amount, inner, cutoff=0) into the DAG. For OSNF wrapping during parse.
    fn insert_shift(&mut self, inner: ExprPtr<'a>, amount: u16) -> usize {
        let inner_expr = *self.dag.exprs.get_index(inner.idx()).unwrap();
        let inner_nlbv = inner_expr.num_loose_bvars();
        let inner_lb = inner_expr.get_fvar_lb();
        let inner_bloom = inner_expr.get_fvar_bloom();
        let has_fvars = inner_expr.has_fvars();
        let hash = hash64!(crate::expr::SHIFT_HASH, inner, amount, 0u16);
        let struct_hash = inner_expr.get_struct_hash();
        let new_nlbv = inner_nlbv + amount;
        let fvar_lb = inner_lb + amount;
        let fvar_bloom = inner_bloom.checked_shl(amount as u32).unwrap_or(0)
            | (if inner_bloom & 0x80000000 != 0 { 0x80000000 } else { 0 });
        self.insert_expr(Expr::Shift {
            hash, struct_hash, fvar_bloom, fvar_lb, inner, amount: amount as i16,
            cutoff: 0, num_loose_bvars: new_nlbv, has_fvars,
        }).0
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
                    self.insert_expr(Expr::NatLit { ptr: num_ptr, hash, struct_hash: hash, fvar_bloom: 0, fvar_lb: 0 })
                };
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, found {:?}", line)
                    ))
                }
                self.record_expr(dag_idx);
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
                    self.insert_expr(Expr::StringLit { ptr: string_ptr, hash, struct_hash: hash, fvar_bloom: 0, fvar_lb: 0 })
                };
                self.record_expr(dag_idx);
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
                    self.insert_expr(Expr::Sort { level, hash, struct_hash: hash, fvar_bloom: 0, fvar_lb: 0 })
                };
                self.record_expr(dag_idx);
            }
            ExprMData {..} => {
                panic!("Expr.mdata not supported");
            }
            ExprConst {name, levels} => {
                let name = self.get_name_ptr(name);
                let levels = self.get_levels_ptr(&levels);
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::CONST_HASH, name, levels);
                    self.insert_expr(Expr::Const { name, levels, hash, struct_hash: hash, fvar_bloom: 0, fvar_lb: 0 })
                };
                self.record_expr(dag_idx);
            }
            ExprApp {fun, arg} => {
                let fun = self.get_expr_ptr(fun);
                let arg = self.get_expr_ptr(arg);
                let num_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
                let fvar_lb = if num_bvars == 0 { 0 } else {
                    if self.num_loose_bvars(fun) == 0 { self.expr_fvar_lb(arg) }
                    else if self.num_loose_bvars(arg) == 0 { self.expr_fvar_lb(fun) }
                    else { self.expr_fvar_lb(fun).min(self.expr_fvar_lb(arg)) }
                };
                let (core_fun, core_arg) = if fvar_lb > 0 {
                    self.osnf_count += 1;
                    (self.adjust_child(fun, fvar_lb, 0), self.adjust_child(arg, fvar_lb, 0))
                } else { (fun, arg) };
                let core_idx = {
                    let hash = hash64!(crate::expr::APP_HASH, core_fun, core_arg);
                    let locals = self.has_fvars(core_fun) || self.has_fvars(core_arg);
                    let struct_hash = hash64!(crate::expr::APP_HASH, self.struct_hash(core_fun), self.struct_hash(core_arg));
                    let fvar_bloom = crate::expr::bloom_union(self.bloom(core_fun), self.bloom(core_arg));
                    let core_nlbv = self.num_loose_bvars(core_fun).max(self.num_loose_bvars(core_arg));
                    let core_fvar_lb = if core_nlbv == 0 { 0 } else {
                        if self.num_loose_bvars(core_fun) == 0 { self.expr_fvar_lb(core_arg) }
                        else if self.num_loose_bvars(core_arg) == 0 { self.expr_fvar_lb(core_fun) }
                        else { self.expr_fvar_lb(core_fun).min(self.expr_fvar_lb(core_arg)) }
                    };
                    self.insert_expr(Expr::App { fun: core_fun, arg: core_arg, num_loose_bvars: core_nlbv, has_fvars: locals, hash, struct_hash, fvar_bloom, fvar_lb: core_fvar_lb }).0
                };
                if fvar_lb > 0 {
                    let core_ptr = crate::util::Ptr::from(DagMarker::ExportFile, core_idx);
                    let shift_idx = self.insert_shift(core_ptr, fvar_lb);
                    self.record_expr(shift_idx);
                } else {
                    self.record_expr(core_idx);
                }
            }
            ExprBVar(dbj_idx) => {
                let (dag_idx, _) = {
                    let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
                    let fvar_bloom = crate::expr::bloom_single(dbj_idx);
                    let fvar_lb = dbj_idx;
                    self.insert_expr(Expr::Var { dbj_idx, hash, struct_hash: crate::expr::VAR_HASH, fvar_bloom, fvar_lb })
                };
                self.record_expr(dag_idx);
            }
            ExprLambda {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                let fvar_lb = if num_bvars == 0 { 0 } else {
                    let t_nlbv = self.num_loose_bvars(binder_type);
                    let b_nlbv = self.num_loose_bvars(body);
                    let b_lb = self.expr_fvar_lb(body).saturating_sub(1);
                    if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                    else if t_nlbv == 0 { b_lb }
                    else if b_nlbv <= 1 { self.expr_fvar_lb(binder_type) }
                    else { self.expr_fvar_lb(binder_type).min(b_lb) }
                };
                let (core_type, core_body) = if fvar_lb > 0 {
                    self.osnf_count += 1;
                    (self.adjust_child(binder_type, fvar_lb, 0), self.adjust_child(body, fvar_lb, 1))
                } else { (binder_type, body) };
                let core_idx = {
                    let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, core_type, core_body);
                    let core_nlbv = self.num_loose_bvars(core_type).max(self.num_loose_bvars(core_body).saturating_sub(1));
                    let locals = self.has_fvars(core_type) || self.has_fvars(core_body);
                    let struct_hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, self.struct_hash(core_type), self.struct_hash(core_body));
                    let body_bloom = crate::expr::bloom_unbind(self.bloom(core_body));
                    let fvar_bloom = crate::expr::bloom_union(self.bloom(core_type), body_bloom);
                    let core_fvar_lb = if core_nlbv == 0 { 0 } else {
                        let t_nlbv = self.num_loose_bvars(core_type);
                        let b_nlbv = self.num_loose_bvars(core_body);
                        let b_lb = self.expr_fvar_lb(core_body).saturating_sub(1);
                        if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                        else if t_nlbv == 0 { b_lb }
                        else if b_nlbv <= 1 { self.expr_fvar_lb(core_type) }
                        else { self.expr_fvar_lb(core_type).min(b_lb) }
                    };
                    self.insert_expr(Expr::Lambda {
                        binder_name, binder_style: binder_info, binder_type: core_type, body: core_body,
                        num_loose_bvars: core_nlbv, has_fvars: locals, hash, struct_hash, fvar_bloom, fvar_lb: core_fvar_lb,
                    }).0
                };
                if fvar_lb > 0 {
                    let core_ptr = crate::util::Ptr::from(DagMarker::ExportFile, core_idx);
                    let shift_idx = self.insert_shift(core_ptr, fvar_lb);
                    self.record_expr(shift_idx);
                } else {
                    self.record_expr(core_idx);
                }
            }
            ExprPi {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                let fvar_lb = if num_bvars == 0 { 0 } else {
                    let t_nlbv = self.num_loose_bvars(binder_type);
                    let b_nlbv = self.num_loose_bvars(body);
                    let b_lb = self.expr_fvar_lb(body).saturating_sub(1);
                    if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                    else if t_nlbv == 0 { b_lb }
                    else if b_nlbv <= 1 { self.expr_fvar_lb(binder_type) }
                    else { self.expr_fvar_lb(binder_type).min(b_lb) }
                };
                let (core_type, core_body) = if fvar_lb > 0 {
                    self.osnf_count += 1;
                    (self.adjust_child(binder_type, fvar_lb, 0), self.adjust_child(body, fvar_lb, 1))
                } else { (binder_type, body) };
                let core_idx = {
                    let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, core_type, core_body);
                    let core_nlbv = self.num_loose_bvars(core_type).max(self.num_loose_bvars(core_body).saturating_sub(1));
                    let locals = self.has_fvars(core_type) || self.has_fvars(core_body);
                    let struct_hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, self.struct_hash(core_type), self.struct_hash(core_body));
                    let body_bloom = crate::expr::bloom_unbind(self.bloom(core_body));
                    let fvar_bloom = crate::expr::bloom_union(self.bloom(core_type), body_bloom);
                    let core_fvar_lb = if core_nlbv == 0 { 0 } else {
                        let t_nlbv = self.num_loose_bvars(core_type);
                        let b_nlbv = self.num_loose_bvars(core_body);
                        let b_lb = self.expr_fvar_lb(core_body).saturating_sub(1);
                        if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                        else if t_nlbv == 0 { b_lb }
                        else if b_nlbv <= 1 { self.expr_fvar_lb(core_type) }
                        else { self.expr_fvar_lb(core_type).min(b_lb) }
                    };
                    self.insert_expr(Expr::Pi {
                        binder_name, binder_style: binder_info, binder_type: core_type, body: core_body,
                        num_loose_bvars: core_nlbv, has_fvars: locals, hash, struct_hash, fvar_bloom, fvar_lb: core_fvar_lb,
                    }).0
                };
                if fvar_lb > 0 {
                    let core_ptr = crate::util::Ptr::from(DagMarker::ExportFile, core_idx);
                    let shift_idx = self.insert_shift(core_ptr, fvar_lb);
                    self.record_expr(shift_idx);
                } else {
                    self.record_expr(core_idx);
                }
            }
            ExprLet {name, ty, value, body, nondep} => {
                let binder_name = self.get_name_ptr(name);
                let binder_type = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let body = self.get_expr_ptr(body);
                let num_bvars = self
                    .num_loose_bvars(binder_type)
                    .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
                let fvar_lb = if num_bvars == 0 { 0 } else {
                    let mut lb = u16::MAX;
                    if self.num_loose_bvars(binder_type) > 0 { lb = lb.min(self.expr_fvar_lb(binder_type)); }
                    if self.num_loose_bvars(val) > 0 { lb = lb.min(self.expr_fvar_lb(val)); }
                    let b_nlbv = self.num_loose_bvars(body);
                    let b_lb = self.expr_fvar_lb(body).saturating_sub(1);
                    if b_nlbv > 1 || (b_nlbv == 1 && self.expr_fvar_lb(body) > 0) { lb = lb.min(b_lb); }
                    if lb == u16::MAX { 0 } else { lb }
                };
                let (core_type, core_val, core_body) = if fvar_lb > 0 {
                    self.osnf_count += 1;
                    (self.adjust_child(binder_type, fvar_lb, 0), self.adjust_child(val, fvar_lb, 0), self.adjust_child(body, fvar_lb, 1))
                } else { (binder_type, val, body) };
                let core_idx = {
                    let hash = hash64!(crate::expr::LET_HASH, binder_name, core_type, core_val, core_body, nondep);
                    let core_nlbv = self
                        .num_loose_bvars(core_type)
                        .max(self.num_loose_bvars(core_val).max(self.num_loose_bvars(core_body).saturating_sub(1)));
                    let locals = self.has_fvars(core_type) || self.has_fvars(core_val) || self.has_fvars(core_body);
                    let struct_hash = hash64!(crate::expr::LET_HASH, binder_name, self.struct_hash(core_type), self.struct_hash(core_val), self.struct_hash(core_body), nondep);
                    let body_bloom = crate::expr::bloom_unbind(self.bloom(core_body));
                    let fvar_bloom = crate::expr::bloom_union(
                        crate::expr::bloom_union(self.bloom(core_type), self.bloom(core_val)),
                        body_bloom
                    );
                    let core_fvar_lb = if core_nlbv == 0 { 0 } else {
                        let mut lb = u16::MAX;
                        if self.num_loose_bvars(core_type) > 0 { lb = lb.min(self.expr_fvar_lb(core_type)); }
                        if self.num_loose_bvars(core_val) > 0 { lb = lb.min(self.expr_fvar_lb(core_val)); }
                        let b_nlbv = self.num_loose_bvars(core_body);
                        let b_lb = self.expr_fvar_lb(core_body).saturating_sub(1);
                        if b_nlbv > 1 || (b_nlbv == 1 && self.expr_fvar_lb(core_body) > 0) { lb = lb.min(b_lb); }
                        if lb == u16::MAX { 0 } else { lb }
                    };
                    self.insert_expr(Expr::Let {
                        binder_name,
                        binder_type: core_type,
                        val: core_val,
                        body: core_body,
                        num_loose_bvars: core_nlbv,
                        has_fvars: locals,
                        hash,
                        nondep,
                        struct_hash,
                        fvar_bloom,
                        fvar_lb: core_fvar_lb,
                    }).0
                };
                if fvar_lb > 0 {
                    let core_ptr = crate::util::Ptr::from(DagMarker::ExportFile, core_idx);
                    let shift_idx = self.insert_shift(core_ptr, fvar_lb);
                    self.record_expr(shift_idx);
                } else {
                    self.record_expr(core_idx);
                }
            }
            ExprProj {type_name, idx, structure: struct_} => {
                let ty_name = self.get_name_ptr(type_name);
                let structure = self.get_expr_ptr(struct_);
                let num_bvars = self.num_loose_bvars(structure);
                let fvar_lb = if num_bvars == 0 { 0 } else { self.expr_fvar_lb(structure) };
                let core_structure = if fvar_lb > 0 {
                    self.osnf_count += 1;
                    self.adjust_child(structure, fvar_lb, 0)
                } else { structure };
                let core_idx = {
                    let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, core_structure);
                    let core_nlbv = self.num_loose_bvars(core_structure);
                    let locals = self.has_fvars(core_structure);
                    let struct_hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, self.struct_hash(core_structure));
                    let fvar_bloom = self.bloom(core_structure);
                    let core_fvar_lb = self.expr_fvar_lb(core_structure);
                    self.insert_expr(Expr::Proj {
                        ty_name,
                        idx,
                        structure: core_structure,
                        num_loose_bvars: core_nlbv,
                        has_fvars: locals,
                        hash,
                        struct_hash,
                        fvar_bloom,
                        fvar_lb: core_fvar_lb,
                    }).0
                };
                if fvar_lb > 0 {
                    let core_ptr = crate::util::Ptr::from(DagMarker::ExportFile, core_idx);
                    let shift_idx = self.insert_shift(core_ptr, fvar_lb);
                    self.record_expr(shift_idx);
                } else {
                    self.record_expr(core_idx);
                }
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
