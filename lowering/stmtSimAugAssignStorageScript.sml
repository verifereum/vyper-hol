(*
 * Statement simulation: an augmented assignment to a word storage or
 * transient variable (#637)
 *
 * self.x op= e for a module variable x in storage or transient storage of
 * a word type.  As for a local (stmtSimAugAssign), self.x op= e is
 * self.x = self.x op e on both sides: the source looks x up (a
 * StoragePlace at x's layout slot), reads it, evaluates e, runs the
 * operator and writes the slot, as evaluating self.x op e and then
 * assigning it would; the lowering is an SLOAD or TLOAD of x's slot, e
 * lowered at x's type, compile_binop and an SSTORE or TSTORE at the slot,
 * which is the code of that assignment, since the lowered read of self.x is
 * the same load.  So the statement is stmtSimAssignStorage's
 * compile_assign_storage_typed_stmt_frag for self.x op e, whose simulation
 * is compile_bop_word_case's (exprSimOperators): the checked operators'
 * aborts are among its exits, and ** and the narrow or negative shifts rest
 * on exprSimBinopFrag's cheats (#572).  The read of self.x is exprSimLeaves'
 * storage read, lifted to expr_sim by exprSimUnwrap's expr_sim_of_vv_sim,
 * which carries that theory's cheats for copies and constructor immutables.
 *
 * TOP-LEVEL:
 *   compile_augassign_toplevel_case — self.x op= e on a word storage or
 *                                     transient x, for every outcome,
 *                                     given e's expr_sim_case
 *   eval_augassign_toplevel_assign  — self.x op= e runs as
 *                                     self.x = self.x op e
 *   stmt_env_augassign_toplevel     — and has its code
 *   expr_body_pre_augassign_toplevel — self.x op e meets expr_body_pre
 *                                     where e does
 *
 * Helpers: eval_target_place_toplevel, eval_augassign_toplevel,
 *   eval_assign_pure_target, augassign_toplevel_code_parts,
 *   lower_value_toplevel_word, augassign_toplevel_code_bop,
 *   assign_toplevel_code_parts, toplevel_storage_name_case
 *)

Theory stmtSimAugAssignStorage
Ancestors
  allocLimits list finite_map
  fragExec exprSim exprSimHyps exprSimOps exprSimOperators exprSimLeaves
  stmtSim stmtSimAssign stmtSimAssignMem stmtSimAssignStorage
  stmtSimAugAssign
  exprLowering exprBopLowering exprLoweringProps stmtLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  vyperTypeCallGraph vyperAST
Libs
  monadsyntax

(* ===== The source ===== *)

(* A storage or transient variable's target place is a StoragePlace at its
   layout slot, at its declared type. *)
Theorem eval_target_place_toplevel:
  !cx src id es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_target_place cx (TopLevelNameTarget (src, id)) es =
      (INL (StoragePlace tr (n2w slot) tvt), es) /\
    place_type_value cx (StoragePlace tr (n2w slot) tvt) es = (INL tvt, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, get_place_def, place_type_value_def]
QED

(* self.x op= e on a storage or transient x whose slot decodes to v0: x's
   place and type are read without changing the state, e is evaluated,
   then the operator runs on v0 and e's value, and the result is written
   to x's slot. *)
Theorem eval_augassign_toplevel:
  !cx ty src id bop e es res es' ts tr typ id_str slot tvt v0.
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 tvt bop v0 v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r =>
              write_place cx (StoragePlace tr (n2w slot) tvt) r es1 =
                (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_target_place_toplevel >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       read_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r0, st0)` >>
  Cases_on `r0` >> simp[] >>
  rename1 `eval_expr cx e es = (INL raw, st0)` >>
  Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  qmatch_goalsub_abbrev_tac `evaluate_binop u tvt bop v0 v1` >>
  Cases_on `evaluate_binop u tvt bop v0 v1` >>
  simp[lift_sum_def, return_def, raise_def]
QED

(* An assignment to a target whose place is p wherever it is evaluated:
   e's forced value, then the write of it at p. *)
Theorem eval_assign_pure_target:
  !cx t e p es.
    (!s. eval_target_place cx t s = (INL p, s)) ==>
    eval_stmt cx (Assign (BaseTarget t) e) es =
      case (do tv <- eval_expr cx e; read_result cx tv od) es of
        (INL v, es1) => write_place cx p v es1
      | (INR ex, es1) => (INR ex, es1)
Proof
  rpt strip_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (r0, st0)` >>
  Cases_on `r0` >> simp[] >>
  rename1 `eval_expr cx e es = (INL raw, st0)` >>
  Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, st1)` >>
  Cases_on `r1` >> simp[]
QED

(* self.x op= e runs as self.x = self.x op e, the read annotated with the
   statement's type. *)
Theorem eval_augassign_toplevel_assign:
  !cx ty src id bop e es res es' ts tr typ id_str slot tvt v0.
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
    bop <> In /\ bop <> NotIn ==>
    eval_stmt cx
      (Assign (BaseTarget (TopLevelNameTarget (src, id)))
         (Builtin ty (Bop bop) [TopLevelName ty (src, id); e])) es =
      (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_augassign_toplevel >> strip_tac >>
  `!s. eval_target_place cx (TopLevelNameTarget (src, id)) s =
         (INL (StoragePlace tr (n2w slot) tvt), s)` by
    metis_tac[eval_target_place_toplevel] >>
  drule eval_assign_pure_target >> simp[] >> disch_then kall_tac >>
  `(do r0 <- eval_expr cx (TopLevelName ty (src, id)); read_result cx r0 od)
     es = (INL v0, es)` by
    (Cases_on `eval_expr cx (TopLevelName ty (src, id)) es` >>
     drule_all eval_expr_toplevel_storage >> strip_tac >>
     gvs[bind_def]) >>
  Cases_on `(do tv <- eval_expr cx (Builtin ty (Bop bop)
                                     [TopLevelName ty (src, id); e]);
                read_result cx tv od) es` >>
  rename1 `_ = (rr, es2)` >>
  drule eval_expr_bop_cases >> simp[] >> strip_tac >>
  `!w st. bop_result cx ty bop [ty; expr_type e] v0 w st =
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 tvt bop v0 w of
            INL v => INL v
          | INR err => INR (Error err)` by
    (rpt gen_tac >> irule bop_result_augassign >> simp[]) >>
  gvs[vyperASTTheory.expr_type_def] >>
  Cases_on `evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              tvt bop v0 v2` >> gvs[write_place_def]
QED

(* ===== The code ===== *)

(* self.x op= e on a storage or transient x: no declaration, x's target is
   its slot with no code, then the load of the slot, e lowered at x's type,
   the operator and the store at the slot. *)
Theorem augassign_toplevel_code_parts:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `sa` assume_tac) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `tr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_op ld [Lit slot] sa` >>
  Cases_on `emit_op ld [Lit slot] sa` >> rename1 `_ = (cur_op, s1)` >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs_op, s2)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  rename1 `_ = (res_op, s3)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_void st [Lit slot; res_op] s3` >>
  Cases_on `emit_void st [Lit slot; res_op] s3` >> simp[oneTheory.one]
QED

(* The lowered value of a word storage or transient variable is one load
   of its slot. *)
Theorem lower_value_toplevel_word:
  !cenv ty ann nsid tr slot sa op sb.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    is_word_type ann /\
    lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op, sb) ==>
    emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, unwrap_value_def,
       contextTheory.compile_ptr_load_def, contextTheory.mk_ptr_def,
       vyperASTTheory.expr_type_def]
QED

(* The code of self.x op= e is the lowering of self.x op e at x's type,
   then the store of its result at x's slot. *)
Theorem augassign_toplevel_code_bop:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    c = cenv /\
    ?s3 res_op.
      lower_value compile_expr cenv ty
        (Builtin ty (Bop bop) [TopLevelName ty nsid; e]) sa = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all augassign_toplevel_code_parts >> strip_tac >> simp[] >>
  `is_word_type ty /\ ~is_bytestring_type ty` by
    metis_tac[word_value_type_word] >>
  Cases_on `lower_value compile_expr cenv ty
              (Builtin ty (Bop bop) [TopLevelName ty nsid; e]) sa` >>
  rename1 `_ = (op', s')` >>
  drule lower_value_bop >> simp[vyperASTTheory.expr_type_def] >>
  strip_tac >>
  drule_all lower_value_toplevel_word >> strip_tac >>
  gvs[expr_int_literal_def]
QED

(* The code of self.x = e for a storage or transient x the lowering holds
   in one word and word-typed e: e's value, then the store at x's slot
   (assign_storage_word_code_parts without its fn_has_code facts). *)
Theorem assign_toplevel_code_parts[local]:
  !cenv lctx ty nsid e sa c sf tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) ==>
    c = cenv /\
    ?sb op.
      lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] sb = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >> simp[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [compile_stmt_def, compile_assign_value_def, comp_bind_def,
     comp_ignore_bind_def, comp_return_def, LET_THM, lower_value_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (src_vv, st2)` >>
  Cases_on `unwrap_value cenv src_vv st2` >>
  rename1 `unwrap_value _ _ _ = (op, sb)` >>
  Cases_on `tr` >> simp[]
QED

(* The code of self.x op= e is the code of self.x = self.x op e. *)
Theorem stmt_env_augassign_toplevel:
  !cenv lctx ty0 ty nsid bop e tr slot vtyp.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\ is_word_type vtyp /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) =
    stmt_env cenv lctx ty0
      (Assign (BaseTarget (TopLevelNameTarget nsid))
         (Builtin ty (Bop bop) [TopLevelName ty nsid; e]))
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `sa` >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  Cases_on `stmt_env cenv lctx ty0
              (AugAssign ty (TopLevelNameTarget nsid) bop e) sa` >>
  rename1 `_ = (c1, sf1)` >>
  Cases_on `stmt_env cenv lctx ty0
              (Assign (BaseTarget (TopLevelNameTarget nsid))
                 (Builtin ty (Bop bop) [TopLevelName ty nsid; e])) sa` >>
  rename1 `_ = (c2, sf2)` >>
  drule_all augassign_toplevel_code_bop >> strip_tac >>
  drule assign_toplevel_code_parts >>
  disch_then (qspecl_then [`tr`, `slot`, `vtyp`] mp_tac) >>
  simp[vyperASTTheory.expr_type_def] >> strip_tac >> gvs[]
QED

(* ===== The operator ===== *)

(* The existing augmented-RHS gate supplies the ordinary builtin gate
   for a storage load as the left operand, just as for a local name. *)
Theorem augassign_toplevel_builtin_operands[local]:
  augassign_operand_ok ty bop e ==>
  builtin_operands_ok ty (Bop bop) [TopLevelName ty nsid; e]
Proof
  Cases_on `bop` >>
  simp[augassign_operand_ok_def, builtin_operands_ok_def,
       power_operands_ok_def, integer_literal_expr_def] >>
  Cases_on `e` >> simp[power_exponent_ok_def] >>
  rename1 `Literal ann lit` >> Cases_on `lit` >> simp[power_exponent_ok_def]
QED

(* The typing side: self.x op e meets expr_body_pre where e does, x is a
   module variable of type ty and the type checker accepts self.x op= e. *)
Theorem expr_body_pre_augassign_toplevel:
  !cenv cx env ty nsid bop e es.
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.toplevel_vtypes nsid = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    well_typed_binop ty bop ty (expr_type e) /\ augassign_operand_ok ty bop e /\
    bop <> In /\ bop <> NotIn ==>
    expr_body_pre cenv cx env (Builtin ty (Bop bop) [TopLevelName ty nsid; e])
      es
Proof
  rpt strip_tac >>
  drule well_formed_type_bits >> strip_tac >>
  `ty <> NoneT` by
    (strip_tac >> drule_all well_typed_binop_augassign_word >>
     simp[word_value_type_def]) >>
  drule augassign_toplevel_builtin_operands >> strip_tac >>
  PairCases_on `nsid` >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      vyperASTTheory.expr_type_def]
QED

(* A storage or transient variable's read simulates: exprSimLeaves' read
   of its slot, or its undecodable read's type error. *)
Theorem toplevel_storage_name_case[local]:
  !nocalls ctx func cenv cx ann src id ts tr typ id_str.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
    expr_sim_case nocalls ctx func cenv cx (TopLevelName ann (src, id))
Proof
  rpt strip_tac >> irule expr_sim_case_of_vv >>
  rw[expr_vv_case_def] >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  Cases_on `?slot tvt v.
              lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
              evaluate_type (get_tenv cx) typ = SOME tvt /\
              read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)`
  >- (gvs[] >> irule compile_toplevel_storage_vv_sim >> metis_tac[]) >>
  irule compile_toplevel_storage_undecodable_sim >> metis_tac[]
QED

(* ===== The statement ===== *)

(* self.x op= e on a word storage or transient variable x, for every
   outcome, given e's expr_sim_case (so e may make internal calls unless
   nocalls).  The statement's type ty is x's declared type, and the
   typing gives x that type (toplevel_vtypes). *)
(* Why it holds.  x's slot decodes wherever expr_sim_inv holds
   (toplevel_storage_read_decodes), so the source runs as
   self.x = self.x op e (eval_augassign_toplevel_assign), and the code is
   that assignment's (stmt_env_augassign_toplevel) once stmt_state_rel
   gives cenv's view of x's slot.  self.x op e meets expr_body_pre, its
   operands simulate, so it does (compile_bop_word_case), and its values
   are of x's type: compile_assign_storage_typed_stmt_frag applies. *)
Theorem compile_augassign_toplevel_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty src id bop e es res es'
   ts tr id_str slot tvt vtyp.
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') /\
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    FLOOKUP env.toplevel_vtypes (src, id) = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\ is_word_type vtyp /\
    well_typed_binop ty bop ty (expr_type e) /\ augassign_operand_ok ty bop e /\
    bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `?v0. read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es)` by
    (irule toplevel_storage_read_decodes >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all eval_augassign_toplevel_assign >> strip_tac >>
  `expr_body_pre cenv cx env
     (Builtin ty (Bop bop) [TopLevelName ty (src, id); e]) es` by
    (irule expr_body_pre_augassign_toplevel >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx
     (Builtin ty (Bop bop) [TopLevelName ty (src, id); e])` by
    (irule compile_bop_word_case >>
     simp[vyperASTTheory.expr_type_def] >>
     metis_tac[toplevel_storage_name_case]) >>
  `expr_sim ctx func cenv cx ty
     (Builtin ty (Bop bop) [TopLevelName ty (src, id); e]) es` by
    (irule expr_sim_case_apply >> simp[int_calls_expr_def] >> metis_tac[]) >>
  `stmt_frag ctx func cx lctx RetQ cenv
     (stmt_env cenv lctx ty0
        (Assign (BaseTarget (TopLevelNameTarget (src, id)))
           (Builtin ty (Bop bop) [TopLevelName ty (src, id); e])))
     es res es'` by
    (qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty0`, `src`,
                  `id`, `Builtin ty (Bop bop) [TopLevelName ty (src, id); e]`,
                  `es`, `res`, `es'`, `ts`, `tr`, `ty`, `id_str`, `slot`,
                  `tvt`, `vtyp`] mp_tac
       compile_assign_storage_typed_stmt_frag >>
     simp[vyperASTTheory.expr_type_def] >> disch_then irule >>
     rpt strip_tac >>
     qspecl_then [`cenv`, `cx`, `env`,
                  `Builtin ty (Bop bop) [TopLevelName ty (src, id); e]`,
                  `es`, `INL v`, `es1`] mp_tac expr_body_pre_word_result >>
     simp[vyperASTTheory.expr_type_def] >> strip_tac >> gvs[]) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
   stmt_env cenv lctx ty0
     (Assign (BaseTarget (TopLevelNameTarget (src, id)))
        (Builtin ty (Bop bop) [TopLevelName ty (src, id); e]))` by
    (irule stmt_env_augassign_toplevel >> simp[] >> metis_tac[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def]) >>
  gvs[] >> disch_then drule_all >> simp[]
QED

(* Integrity gate: the source and code sides carry no admission; the
   statement itself inherits exprSimBinopFrag's (#572) and exprSimUnwrap's. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "AUGASSIGN_STORAGE_AUDIT OK\n"
     else raise Fail "storage augmented assignment inherited admission"
  end) [eval_augassign_toplevel_assign, stmt_env_augassign_toplevel,
        expr_body_pre_augassign_toplevel];
