(* Semantic boundaries for widened aggregate declarations. *)
Theory widenedDeclarationIntegrationMem
Ancestors
  assignValueMemoryOpen exprOpenTerminals bodyMemoryPreds
  widenedLocalContinuationMem widenedLocalOutcomeMem widenedAssignValueParts
  widenedLocalRuntimeMem widenedDeclareContinuationMem widenedValueReadOutcomeMem
  bodyExprPreFacts supportedStmtTraverse supportedStmts vyperTypeInvariants
  vyperTypeSystem vyperTypeExprResult vyperTyping bodySim exprSimHypsDefs
  gasContext supportedTypes vyperInterpreter vyperTypeCallGraph vyperState
  bodyDeclMemoryCounted bodyDeclCopyMemory stmtSimDeclCompose stmtSimDecl
  stmtSimDeclMem exprLoweringProps exprSimProps stmtSimProps stmtSimDefs
  bodySimDeclCases exprSimIfExpCompat exprSimSource compileEnv fragExec
  stmtSimDeclSource exprSimMemorySource exprSimMemDefs
Libs monadsyntax

Theorem widened_declaration_rhs_classify[local]:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  supported_expr tops e /\ supported_copy_types typ (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?fid args drv. e = Call typ (IntCall fid) args drv /\
    ~is_bytestring_type typ /\ arg_type_fits (lowered_value_type ce e) typ
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  `arg_type_fits (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty` by
    metis_tac[exprSimHypsTheory.ifexp_body_pre_intcall_physical] >>
  `~is_bytestring_type ty` by
    (fs[vyperASTTheory.expr_type_def] >>
     metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
  `typ = ty` by
    (fs[vyperASTTheory.expr_type_def] >>
     metis_tac[exprOpenCopiesTheory.supported_copy_types_store_path,
               typedMemoryCopyTheory.typed_copy_bytestring_source]) >>
  gvs[]
QED

Theorem widened_declaration_endpoint[local]:
  body_inv tops ctx ce cx /\
  declare_local old id ann sa = (ce,st) /\ old.ce_alloca_locals /\
  (!l. FLOOKUP old.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sA = (vv,sV) /\
  unwrap_value ce vv sV = (op,sB) /\
  compile_assign_value ce dst LocMemory op F loc ann sty info bytes sB = ((),sb) /\
  sa.cs_next_var <= sA.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x salloc = lookup_var x s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP salloc.vs_allocas aid = SOME b) /\
  s0.vs_alloca_next <= salloc.vs_alloca_next /\
  gas_marked_exec T (ctx,func) (new_variable id dtv v)
    (ee,t) right (INL ()) ff (OK u) /\
  ee.scopes = sc::rest /\ ff.scopes =
    (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest /\
  stmt_state_rel ctx func ce cx (ff with gas_obs := []) u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\ return_buf_frame d ce sb u /\
  alloca_history func u /\ salloc.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sA x /\ lookup_var x salloc = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) ==>
  ?ce'. stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
    ((INL () : unit + exception) = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
    cenv_top_ext old ce' (ff with gas_obs := []).scopes /\
    stmt_state_rel ctx func ce' cx (ff with gas_obs := []) u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    return_buf_frame d ce' sb u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> qexists_tac `ce` >>
  simp[loweringPostsTheory.stmt_lands_def] >>
  conj_tac
  >- (`acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
      `~block_is_terminated sB` by
        (`~block_is_terminated sV` by
           (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
            simp[Once exprLoweringTheory.compile_expr_def] >>
            metis_tac[compile_intcall_open]) >> metis_tac[unwrap_value_open]) >>
      drule_all compile_assign_value_memory_open >> simp[]) >>
  conj_tac
  >- (irule cenv_top_ext_declare_local >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[new_variable_def, get_scopes_def, type_check_def,
        vyperStateTheory.bind_def, ignore_bind_def, assert_def,
        return_def, raise_def, lookup_scopes_def, AllCaseEqs()] >>
      strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at sA x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED

Theorem widened_declaration_callback[local]:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sA = (vv,sV) /\
  unwrap_value ce vv sV = (op,sB) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ann
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sB = ((),sb) /\
  fn_has_code sB sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sA /\ not_fresh_at sA p /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p salloc = SOME dw /\
  FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  inst.inst_id < sA.cs_next_id /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  type_memory_bytes ce ann <= sz /\ return_buf_frame d ce sA salloc /\
  gas_admissible (eval_stmt cx (AnnAssign id ann (Call ann (IntCall fid) args drv)))
    (stmt_res_ok lctx) es /\ evaluate_type (get_tenv cx) ann = SOME dtv /\
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,salloc) marks (INL v) ee (OK t) /\
  vv_post ctx func ce cx (Call ann (IntCall fid) args drv) es sA sV salloc
    (ee with gas_obs := []) raw vv t /\
  vv_store_bound cx ann (lowered_value_type ce (Call ann (IntCall fid) args drv))
    (ee with gas_obs := []) raw vv t /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
  t.vs_current_bb = sV.cs_current_bb /\ t.vs_inst_idx = LENGTH sV.cs_current_insts /\
  alloca_history func t /\ salloc.vs_alloca_next <= t.vs_alloca_next /\
  declare_local old id ann sa = (ce,st) /\ old.ce_alloca_locals /\
  (!l. FLOOKUP old.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
  sa.cs_next_var <= sA.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x salloc = lookup_var x s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP salloc.vs_allocas aid = SOME b) /\
  s0.vs_alloca_next <= salloc.vs_alloca_next ==>
  ?right ff u.
    gas_marked_exec T (ctx,func) (new_variable id dtv v)
      (ee with gas_obs := [],t) right (INL ()) ff (OK u) /\
    ?ce'. stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
      ((INL () : unit + exception) = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
      cenv_top_ext old ce' (ff with gas_obs := []).scopes /\
      stmt_state_rel ctx func ce' cx (ff with gas_obs := []) u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d ce' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule_all widened_declare_retained_continuation_mem >> strip_tac >>
  qexistsl_tac [`right`, `ff`, `u`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule widened_declaration_endpoint >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexists_tac `salloc` >> simp[]
QED

Theorem widened_declaration_allocated_outcome[local]:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  declare_local old id ann sa = (ce,st) /\ old.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP old.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes old ann))] [p] st = ((),sA) /\
  type_memory_bytes old ann < dimword (:256) /\
  type_memory_bytes ce ann = type_memory_bytes old ann /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sA = (vv,sV) /\
  unwrap_value ce vv sV = (op,sB) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ann
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sB = ((),sb) /\
  fn_has_code sa sA func /\ fn_has_code sA sV func /\ fn_has_code sB sb func /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes old ann))] [p])
    (fn_insts func) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved old sa /\
  stmt_state_rel ctx func old cx es s0 /\ alloca_history func s0 /\
  return_buf_frame d old sa s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_stmt cx (AnnAssign id ann (Call ann (IntCall fid) args drv)))
    (stmt_res_ok lctx) es /\ evaluate_type (get_tenv cx) ann = SOME dtv /\
  expr_vv_sim_mem ctx func ce cx ann (Call ann (IntCall fid) args drv) es ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_stmt cx (AnnAssign id ann (Call ann (IntCall fid) args drv))) (es,s0)
    (\res ff u. ?ce'. stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
      cenv_top_ext old ce' ff.scopes /\ stmt_state_rel ctx func ce' cx ff u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d ce' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  `gas_admissible
     (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
     expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_admissible (eval_expr cx (Call ann (IntCall fid) args drv))
     expr_vv_res_ok es` by metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sA`, `sV`, `vv`, `salloc`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule value_read_outcome_mem >>
  (impl_tac >- (rpt strip_tac >> gvs[] >>
    metis_tac[stmtReasonVvMemoryTheory.vv_post_read_ok])) >> strip_tac >>
  irule annassign_rhs_counted_outcome_mem >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule (SRULE [] widened_declaration_callback) >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  fs[venomInstTheory.mk_inst_def, vyperASTTheory.expr_type_def] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  drule_all declare_local_ptr >> simp[] >> metis_tac[]
QED

Theorem widened_declaration_code[local]:
  declare_local old id ann sa = (ce,st) /\ old.ce_alloca_locals /\
  local_ptrs_reserved old sa /\ fn_has_code sa sb func /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes old ann))]
    [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
  compile_expr ce ann e sA = (vv,sV) /\
  unwrap_value ce vv sV = (op,sB) /\
  lower_value compile_expr ce ann e sA = (op,sB) /\
  compile_assign_value ce dst LocMemory op F loc ann sty info bytes sB = ((),sb) ==>
  fn_has_code sa sA func /\ fn_has_code sA sV func /\ fn_has_code sB sb func /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes old ann))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  `cs_extends sA sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     metis_tac[externalEntryShapeTheory.compile_assign_value_labels,
               pairTheory.SND]) >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `cs_extends sA sV` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sV sB` by metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `fn_has_code sA sV func` by (drule_all fn_has_code_split >> simp[]) >>
  gvs[fn_has_code_def, emitted_blocks_def]
QED

Theorem widened_declaration_integration_mem:
  body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AnnAssign id typ e) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  expr_body_pre cenv cx env e es /\ body_expr_mem_ok cx e /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  ~(lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  strip_tac >>
  `supported_expr tops e /\ supported_copy_types typ (expr_type e)` by
    fs[supported_stmt_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (rpt strip_tac >> `FLOOKUP cenv.ce_vars id = NONE` by
       (irule declared_name_unbound >> metis_tac[]) >> gvs[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  drule_all widened_declaration_rhs_classify >> strip_tac >> gvs[] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id typ sa = (c, st)` >>
  `same_frame cenv c` by (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ (Call typ (IntCall fid) args drv))` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `expr_body_pre c cx env (Call typ (IntCall fid) args drv) es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_mem ctx func c cx typ (Call typ (IntCall fid) args drv) es` by
    metis_tac[body_expr_mem_ok_def, vyperASTTheory.expr_type_def] >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `~(has_length_word typ /\ is_empty_value_expr (Call typ (IntCall fid) args drv))` by
    simp[stmtLoweringTheory.is_empty_value_expr_def] >>
  drule_all annassign_copy_parts_mem >> strip_tac >>
  `fn_has_code sa sA func /\ fn_has_code sA sV func /\ fn_has_code sB sb func /\
   MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule widened_declaration_code >> simp[] >> metis_tac[vyperASTTheory.expr_type_def]) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
        wordsTheory.dimword_def] >> decide_tac) >>
  irule widened_declaration_allocated_outcome >>
  gvs[vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED
