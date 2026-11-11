(* Retained internal-call outcomes for assignments to memory locals. *)
Theory widenedAssignmentIntegrationMem
Ancestors
  widenedAssignContinuationMem widenedValueReadOutcomeMem widenedLocalOutcomeMem
  assignValueMemoryOpen exprOpenTerminals bodyMemoryPreds stmtSimAssignMem
  stmtSimAssignCompose stmtSimAssignSource stmtSimDeclCompose stmtSimAssignStore
  exprLoweringProps exprSimProps stmtSimProps stmtSimDefs exprSimHypsDefs
  exprSimMemDefs exprSimMemorySource bodySim compileEnv fragExec externalEntryShape
Libs monadsyntax

Theorem widened_assignment_code[local]:
  stmt_env ce lctx rty (Assign (BaseTarget (NameTarget id)) e) sa = (c,sf) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME ty /\ ~is_word_type ty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  fn_has_code sa sf fn ==>
  c = ce /\ ?vv sm sb op.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,sb) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ty
      (lowered_value_type ce e)
      (case ty of ArrayT elem (Dynamic _) =>
        SOME ((type_memory_bytes ce elem + 31) DIV 32,type_memory_bytes ce elem)
        | _ => NONE) (type_memory_bytes ce ty) sb = ((),sf) /\
    fn_has_code sa sm fn /\ fn_has_code sb sf fn
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once stmtLoweringTheory.compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  Cases_on `unwrap_value ce vv sm` >>
  rename1 `unwrap_value _ _ _ = (op,sb)` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sb sf` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     metis_tac[compile_assign_value_labels, pairTheory.SND]) >>
  `cs_extends sm sb` by metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sf fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code sa sm fn` by metis_tac[fn_has_code_split] >> gvs[]
QED

Theorem widened_assignment_endpoint[local]:
  body_inv tops ctx ce cx /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sB) /\
  compile_assign_value ce dst LocMemory op F loc ty sty info bytes sB = ((),sf) /\
  stmt_state_rel ctx func ce cx (ff with gas_obs := []) u /\
  ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
  u.vs_inst_idx = LENGTH sf.cs_current_insts /\ return_buf_frame d ce sf u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) ==>
  ?ce'. stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
    ((INL () : unit + exception) = INL () ==> ~block_is_terminated sf /\ ce' = ce) /\
    cenv_top_ext ce ce' (ff with gas_obs := []).scopes /\
    stmt_state_rel ctx func ce' cx (ff with gas_obs := []) u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    return_buf_frame d ce' sf u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> qexists_tac `ce` >>
  simp[loweringPostsTheory.stmt_lands_def, cenv_top_ext_refl] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  `~block_is_terminated sm` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[Once exprLoweringTheory.compile_expr_def] >>
     metis_tac[compile_intcall_open]) >>
  `~block_is_terminated sB` by metis_tac[unwrap_value_open] >>
  drule_all compile_assign_value_memory_open >> simp[]
QED

Theorem widened_assignment_outcome[local]:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  type_widens_to env.type_defs ann ty /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ty /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sB) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ty
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sB = ((),sf) /\
  fn_has_code sa sm func /\ fn_has_code sB sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  FLOOKUP env.var_types id = SOME ty /\ return_buf_frame d ce sa s0 /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id))
    (Call ann (IntCall fid) args drv))) (stmt_res_ok lctx) es /\
  expr_vv_sim_mem ctx func ce cx ann (Call ann (IntCall fid) args drv) es ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id))
      (Call ann (IntCall fid) args drv))) (es,s0)
    (\res ff u. ?ce'. stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce' = ce) /\
      cenv_top_ext ce ce' ff.scopes /\ stmt_state_rel ctx func ce' cx ff u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d ce' sf u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_admissible
     (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
     expr_res_ok es` by metis_tac[assign_local_admissible_rhs] >>
  `gas_admissible (eval_expr cx (Call ann (IntCall fid) args drv))
     expr_vv_res_ok es` by metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule value_read_outcome_mem >>
  (impl_tac >- (rpt strip_tac >> gvs[] >>
    metis_tac[stmtReasonVvMemoryTheory.vv_post_read_ok])) >> strip_tac >>
  irule assign_local_rhs_counted_outcome_mem >>
  (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[vyperASTTheory.expr_type_def] >>
  drule_all widened_assign_retained_continuation_mem >> strip_tac >>
  qexistsl_tac [`right`, `ff`, `u`] >> conj_tac >- first_assum ACCEPT_TAC >>
  drule_all widened_assignment_endpoint >>
  disch_then (qspec_then `lctx` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[stmt_state_rel_def, state_rel_gas_obs]
QED

Theorem widened_assignment_integration_mem:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  body_expr_mem_ok cx (Call ann (IntCall fid) args drv) /\
  type_widens_to env.type_defs ann ty /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ty /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME ty /\ FLOOKUP env.var_types id = SOME ty ==>
  stmt_frag_mem d ctx func cx lctx RetQ ce
    (stmt_env ce lctx ret_ty (Assign (BaseTarget (NameTarget id))
      (Call ann (IntCall fid) args drv)))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id))
      (Call ann (IntCall fid) args drv))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `~(has_length_word (expr_type (Call ann (IntCall fid) args drv)) /\
     is_empty_value_expr (Call ann (IntCall fid) args drv))` by
    simp[stmtLoweringTheory.is_empty_value_expr_def] >>
  drule_all widened_assignment_code >> strip_tac >> gvs[] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func ce cx ann (Call ann (IntCall fid) args drv) es` by
    metis_tac[body_expr_mem_ok_def, vyperASTTheory.expr_type_def] >>
  irule widened_assignment_outcome >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> gvs[vyperASTTheory.expr_type_def] >> metis_tac[]
QED
