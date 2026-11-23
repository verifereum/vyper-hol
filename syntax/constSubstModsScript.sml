(* Module-constant inlining over a linked unit of modules (the source's
   (source id, toplevels) list).  As constSubst, but a constant is keyed by
   its module and name, so a reference TopLevelName (src, id) is replaced for
   every module src, not only the main module (NONE).  At the single module
   [(NONE, tops)] these are constSubst's module_consts_env and
   subst_consts_* (the singleton theorems in compileUnit). *)
Theory constSubstMods
Ancestors
  vyperAST alist list option pair vyperContext constSubst

Definition subst_consts_expr_mods_def:
  subst_consts_expr_mods env (Name ty id) = Name ty id /\
  subst_consts_expr_mods env (TopLevelName ty (ns,id)) =
    (case ALOOKUP env (ns,id) of
       NONE => TopLevelName ty (ns,id) | SOME e => e) /\
  subst_consts_expr_mods env (FlagMember ty ns id) = FlagMember ty ns id /\
  subst_consts_expr_mods env (Literal ty l) = Literal ty l /\
  subst_consts_expr_mods env (IfExp ty a b c) =
    IfExp ty (subst_consts_expr_mods env a) (subst_consts_expr_mods env b)
             (subst_consts_expr_mods env c) /\
  subst_consts_expr_mods env (StructLit ty ns fs) =
    StructLit ty ns (subst_consts_fields_mods env fs) /\
  subst_consts_expr_mods env (Subscript ty a b) =
    Subscript ty (subst_consts_expr_mods env a) (subst_consts_expr_mods env b) /\
  subst_consts_expr_mods env (Attribute ty a id) =
    Attribute ty (subst_consts_expr_mods env a) id /\
  subst_consts_expr_mods env (Builtin ty bi es) =
    Builtin ty bi (subst_consts_exprs_mods env es) /\
  subst_consts_expr_mods env (TypeBuiltin ty bi t es) =
    TypeBuiltin ty bi t (subst_consts_exprs_mods env es) /\
  subst_consts_expr_mods env (Pop ty tgt) = Pop ty (subst_consts_btarget_mods env tgt) /\
  subst_consts_expr_mods env (Call ty ct es d) =
    Call ty ct (subst_consts_exprs_mods env es) (subst_consts_opt_mods env d) /\
  subst_consts_btarget_mods env (NameTarget id) = NameTarget id /\
  subst_consts_btarget_mods env (TopLevelNameTarget ns) = TopLevelNameTarget ns /\
  subst_consts_btarget_mods env (SubscriptTarget tgt e) =
    SubscriptTarget (subst_consts_btarget_mods env tgt) (subst_consts_expr_mods env e) /\
  subst_consts_btarget_mods env (AttributeTarget tgt id) =
    AttributeTarget (subst_consts_btarget_mods env tgt) id /\
  subst_consts_exprs_mods env [] = [] /\
  subst_consts_exprs_mods env (e::es) =
    subst_consts_expr_mods env e :: subst_consts_exprs_mods env es /\
  subst_consts_opt_mods env NONE = NONE /\
  subst_consts_opt_mods env (SOME e) = SOME (subst_consts_expr_mods env e) /\
  subst_consts_fields_mods env [] = [] /\
  subst_consts_fields_mods env ((id,e)::fs) =
    (id,subst_consts_expr_mods env e)::subst_consts_fields_mods env fs
Termination
  qexists_tac `measure (\(x : ((num option # identifier) # expr) list # expr +
      ((num option # identifier) # expr) list # base_assignment_target +
      ((num option # identifier) # expr) list # expr list +
      ((num option # identifier) # expr) list # expr option +
      ((num option # identifier) # expr) list # (identifier # expr) list).
    case x of
      INL (_,e) => expr_size e
    | INR (INL (_,t)) => base_assignment_target_size t
    | INR (INR (INL (_,es))) => list_size expr_size es
    | INR (INR (INR (INL (_,opt)))) => option_size expr_size opt
    | INR (INR (INR (INR (_,fs)))) =>
        list_size (pair_size (list_size char_size) expr_size) fs)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def,
       basicSizeTheory.option_size_def, bnfPrelimsTheory.option_size_map,
       bnfPrelimsTheory.pair_size_map, list_size_map, SF ETA_ss]
End

Definition subst_consts_target_mods_def:
  subst_consts_target_mods env (BaseTarget tgt) =
    BaseTarget (subst_consts_btarget_mods env tgt) /\
  subst_consts_target_mods env (TupleTarget ts) =
    TupleTarget (subst_consts_targets_mods env ts) /\
  subst_consts_targets_mods env [] = [] /\
  subst_consts_targets_mods env (t::ts) =
    subst_consts_target_mods env t :: subst_consts_targets_mods env ts
End

Definition subst_consts_iter_mods_def:
  subst_consts_iter_mods env (Array e) = Array (subst_consts_expr_mods env e) /\
  subst_consts_iter_mods env (Range a b) =
    Range (subst_consts_expr_mods env a) (subst_consts_expr_mods env b)
End

Definition subst_consts_error_mods_def:
  subst_consts_error_mods env (CustomError ns es fs) =
    CustomError ns (subst_consts_exprs_mods env es) (subst_consts_fields_mods env fs)
End

Definition subst_consts_areason_mods_def:
  subst_consts_areason_mods env AssertBare = AssertBare /\
  subst_consts_areason_mods env AssertUnreachable = AssertUnreachable /\
  subst_consts_areason_mods env (AssertReason e) = AssertReason (subst_consts_expr_mods env e) /\
  subst_consts_areason_mods env (AssertCustomError e) =
    AssertCustomError (subst_consts_error_mods env e)
End

Definition subst_consts_rreason_mods_def:
  subst_consts_rreason_mods env RaiseBare = RaiseBare /\
  subst_consts_rreason_mods env RaiseUnreachable = RaiseUnreachable /\
  subst_consts_rreason_mods env (RaiseReason e) = RaiseReason (subst_consts_expr_mods env e) /\
  subst_consts_rreason_mods env (RaiseCustomError e) =
    RaiseCustomError (subst_consts_error_mods env e)
End

Definition subst_consts_stmt_mods_def:
  subst_consts_stmt_mods env Pass = Pass /\
  subst_consts_stmt_mods env Continue = Continue /\
  subst_consts_stmt_mods env Break = Break /\
  subst_consts_stmt_mods env (Expr e) = Expr (subst_consts_expr_mods env e) /\
  subst_consts_stmt_mods env (For id ty it n body) =
    For id ty (subst_consts_iter_mods env it) n (subst_consts_stmts_mods env body) /\
  subst_consts_stmt_mods env (If e a b) =
    If (subst_consts_expr_mods env e) (subst_consts_stmts_mods env a) (subst_consts_stmts_mods env b) /\
  subst_consts_stmt_mods env (Assert e r) =
    Assert (subst_consts_expr_mods env e) (subst_consts_areason_mods env r) /\
  subst_consts_stmt_mods env (Log ns es) = Log ns (subst_consts_exprs_mods env es) /\
  subst_consts_stmt_mods env (Raise r) = Raise (subst_consts_rreason_mods env r) /\
  subst_consts_stmt_mods env (Return e) = Return (subst_consts_opt_mods env e) /\
  subst_consts_stmt_mods env (Assign t e) =
    Assign (subst_consts_target_mods env t) (subst_consts_expr_mods env e) /\
  subst_consts_stmt_mods env (AugAssign ty t bi e) =
    AugAssign ty (subst_consts_btarget_mods env t) bi (subst_consts_expr_mods env e) /\
  subst_consts_stmt_mods env (Append t e) =
    Append (subst_consts_btarget_mods env t) (subst_consts_expr_mods env e) /\
  subst_consts_stmt_mods env (AnnAssign id ty e) = AnnAssign id ty (subst_consts_expr_mods env e) /\
  subst_consts_stmts_mods env [] = [] /\
  subst_consts_stmts_mods env (s::ss) =
    subst_consts_stmt_mods env s :: subst_consts_stmts_mods env ss
End

(* The unit's constants, keyed (src, id), in constants_order: imported
   modules first, the main module last, each module's in declaration order.
   A constant's value is substituted with the constants before it. *)
Definition module_consts_env_mods_def:
  module_consts_env_mods src [] acc = acc /\
  module_consts_env_mods src (VariableDecl vis (Constant e) id ty slot :: rest)
      acc =
    module_consts_env_mods src rest
      (acc ++ [((src,id),fold_const_expr (subst_consts_expr_mods acc e))]) /\
  module_consts_env_mods src (_::rest) acc = module_consts_env_mods src rest acc
End

Definition consts_env_mods_acc_def:
  consts_env_mods_acc [] acc = acc /\
  consts_env_mods_acc ((src, tops) :: rest) acc =
    consts_env_mods_acc rest (module_consts_env_mods src tops acc)
End

(* Match the interpreter's constant installation order. *)
Definition consts_env_modules_order_def:
  consts_env_modules_order [] = [] /\
  consts_env_modules_order ((src,tops)::rest) =
    if IS_SOME src then (src,tops)::consts_env_modules_order rest
    else consts_env_modules_order rest ++ [(src,tops)]
End

Definition consts_env_mods_def:
  consts_env_mods (mods : (num option # toplevel list) list) =
    consts_env_mods_acc (consts_env_modules_order mods) []
End

Definition subst_consts_fn_mods_def:
  subst_consts_fn_mods env (mut,nr,rr,id,args,dflts,ret,body) =
    (mut,nr,rr,id,args,subst_consts_exprs_mods env dflts,ret,
     subst_consts_stmts_mods env body)
End

(* ===== At one module: constSubst's definitions ===== *)

Theorem alookup_main_consts[local]:
  ALOOKUP (MAP (λ(id,v). ((NONE,id),v)) env) (ns,id) =
  case ns of NONE => ALOOKUP env id | SOME _ => NONE
Proof
  Cases_on `ns` >> Induct_on `env` >> simp[ALOOKUP_def] >>
  Cases_on `h` >> simp[ALOOKUP_def]
QED

Theorem subst_consts_expr_mods_singleton[local]:
  (∀env e. subst_consts_expr_mods (MAP (λ(id,v). ((NONE,id),v)) env) e =
           subst_consts_expr env e) ∧
  (∀env t. subst_consts_btarget_mods (MAP (λ(id,v). ((NONE,id),v)) env) t =
           subst_consts_btarget env t) ∧
  (∀env es. subst_consts_exprs_mods (MAP (λ(id,v). ((NONE,id),v)) env) es =
            subst_consts_exprs env es) ∧
  (∀env opt. subst_consts_opt_mods (MAP (λ(id,v). ((NONE,id),v)) env) opt =
             subst_consts_opt env opt) ∧
  (∀env fs. subst_consts_fields_mods (MAP (λ(id,v). ((NONE,id),v)) env) fs =
            subst_consts_fields env fs)
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_mods_def, subst_consts_expr_def, alookup_main_consts] >>
  rpt gen_tac >> Cases_on `ns` >> simp[]
QED

Theorem subst_consts_target_mods_singleton[local]:
  (∀env t. subst_consts_target_mods (MAP (λ(id,v). ((NONE,id),v)) env) t =
           subst_consts_target env t) ∧
  (∀env ts. subst_consts_targets_mods (MAP (λ(id,v). ((NONE,id),v)) env) ts =
            subst_consts_targets env ts)
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_mods_def, subst_consts_target_def,
       subst_consts_expr_mods_singleton]
QED

Theorem subst_consts_iter_mods_singleton[local]:
  subst_consts_iter_mods (MAP (λ(id,v). ((NONE,id),v)) env) it =
  subst_consts_iter env it
Proof
  Cases_on `it` >>
  simp[subst_consts_iter_mods_def, subst_consts_iter_def,
       subst_consts_expr_mods_singleton]
QED

Theorem subst_consts_error_mods_singleton[local]:
  subst_consts_error_mods (MAP (λ(id,v). ((NONE,id),v)) env) err =
  subst_consts_error env err
Proof
  Cases_on `err` >>
  simp[subst_consts_error_mods_def, subst_consts_error_def,
       subst_consts_expr_mods_singleton]
QED

Theorem subst_consts_areason_mods_singleton[local]:
  subst_consts_areason_mods (MAP (λ(id,v). ((NONE,id),v)) env) r =
  subst_consts_areason env r
Proof
  Cases_on `r` >>
  simp[subst_consts_areason_mods_def, subst_consts_areason_def,
       subst_consts_expr_mods_singleton, subst_consts_error_mods_singleton]
QED

Theorem subst_consts_rreason_mods_singleton[local]:
  subst_consts_rreason_mods (MAP (λ(id,v). ((NONE,id),v)) env) r =
  subst_consts_rreason env r
Proof
  Cases_on `r` >>
  simp[subst_consts_rreason_mods_def, subst_consts_rreason_def,
       subst_consts_expr_mods_singleton, subst_consts_error_mods_singleton]
QED

Theorem subst_consts_stmt_mods_singleton[local]:
  (∀env s. subst_consts_stmt_mods (MAP (λ(id,v). ((NONE,id),v)) env) s =
           subst_consts_stmt env s) ∧
  (∀env ss. subst_consts_stmts_mods (MAP (λ(id,v). ((NONE,id),v)) env) ss =
            subst_consts_stmts env ss)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_mods_def, subst_consts_stmt_def,
       subst_consts_expr_mods_singleton, subst_consts_target_mods_singleton,
       subst_consts_iter_mods_singleton, subst_consts_areason_mods_singleton,
       subst_consts_rreason_mods_singleton]
QED

Theorem subst_consts_mods_singleton:
  (∀e. subst_consts_expr_mods (MAP (λ(id,v). ((NONE,id),v)) env) e =
       subst_consts_expr env e) ∧
  (∀es. subst_consts_exprs_mods (MAP (λ(id,v). ((NONE,id),v)) env) es =
        subst_consts_exprs env es) ∧
  (∀ss. subst_consts_stmts_mods (MAP (λ(id,v). ((NONE,id),v)) env) ss =
        subst_consts_stmts env ss)
Proof
  simp[subst_consts_expr_mods_singleton, subst_consts_stmt_mods_singleton]
QED

Theorem module_consts_env_mods_singleton:
  ∀tops acc.
    module_consts_env_mods NONE tops (MAP (λ(id,v). ((NONE,id),v)) acc) =
    MAP (λ(id,v). ((NONE,id),v)) (module_consts_env tops acc)
Proof
  ho_match_mp_tac module_consts_env_ind >>
  rw[module_consts_env_def, module_consts_env_mods_def,
     subst_consts_mods_singleton]
QED

Theorem consts_env_mods_singleton:
  consts_env_mods [(NONE, tops)] =
  MAP (λ(id,v). ((NONE,id),v)) (module_consts_env tops [])
Proof
  simp[consts_env_mods_def, consts_env_modules_order_def,
       consts_env_mods_acc_def] >>
  qspecl_then [`tops`, `[]`] mp_tac module_consts_env_mods_singleton >>
  simp[]
QED

Theorem subst_consts_fn_mods_singleton:
  subst_consts_fn_mods (MAP (λ(id,v). ((NONE,id),v)) env) f =
  subst_consts_fn env f
Proof
  PairCases_on `f` >>
  simp[subst_consts_fn_mods_def, subst_consts_fn_def,
       subst_consts_mods_singleton]
QED
