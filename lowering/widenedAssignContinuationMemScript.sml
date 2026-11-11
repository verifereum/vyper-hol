(* Counted updates of existing memory locals after a widened physical copy. *)
Theory widenedAssignContinuationMem
Ancestors
  vyperTypeInvariants exprOperandVar typeWideningComposition
  widenedAssignmentPreparationMem widenedLocalContinuationMem
  widenedLocalEndpointMem widenedDeclareContinuationMem stmtSimAssignSource
  gasSummary fragGasMode vyperState finite_map exprLoweringProps exprSimSource venomState compileEnv bodyMemoryDefs
Libs monadsyntax

Theorem typed_copy_assign_marked_mem[local]:
  stmt_state_rel ctx fn ce cx es u /\
  find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p u = SOME dw /\ local_ptrs_reserved ce sa /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u) /\
  (!b n. b+n <= w2n dw \/ w2n dw+type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory /\
  gas_path_mem ctx fn s g (OK t) /\
  (!tail. write_place cx (MemoryPlace id []) v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  let ff = es with scopes :=
    pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest in
  gas_marked_exec T (ctx,fn) (write_place cx (MemoryPlace id []) v) (es,s)
    (REPLICATE g F) (INL ()) ff (OK t) /\
  stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac
  >- (irule gas_marked_exec_no_source_read >> simp[gas_marked_path_def]) >>
  `stmt_state_rel ctx fn ce cx
    (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest) t` by
    (irule typed_copy_assign_state >> metis_tac[]) >>
  gvs[stmt_state_rel_def, compileEnvTheory.state_rel_gas_obs] >> gvs[]
QED

Theorem widened_assign_copy_continuation_mem:
  compile_assign_value ce (Var p) LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\ entry.type = dtv /\
  local_region ce es.scopes s id (w2n dw) sz /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. write_place cx (MemoryPlace id []) v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  ?marks ff t.
    gas_marked_exec T (ctx,fn) (write_place cx (MemoryPlace id []) v) (es,s)
      marks (INL ()) ff (OK t) /\
    ff = es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest /\
    stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ return_buf_frame d ce sb t /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `(!x. src = Var x \/ Var p = Var x ==> not_fresh_at sa x)` by
    (rpt strip_tac >> gvs[]) >>
  Q.SUBGOAL_THEN
    `(?aid. FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id) \/
      (?name. local_region ce es.scopes s name (w2n dw) sz)` assume_tac
  >- metis_tac[] >>
  drule_all widened_local_copy_endpoint_mem >> strip_tac >>
  `lookup_var p u = SOME dw` by
    (first_x_assum (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     simp[eval_operand_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u` by metis_tac[] >>
  `val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory` by simp[] >>
  `!b n. b+n <= w2n dw \/ w2n dw+type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory` by metis_tac[] >>
  drule_all typed_copy_assign_marked_mem >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qexistsl_tac [`REPLICATE g F`, `es with scopes :=
    pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest`, `t`] >>
  simp[] >> gvs[]
QED

Theorem retained_assignment_source_ready[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec T (ctx,fn) (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) ==>
  ?pre scope entry rest.
    find_containing_scope id ee.scopes = SOME (pre,scope,entry,rest) /\
    find_containing_scope id (ee with gas_obs := []).scopes =
      SOME (pre,scope,entry,rest) /\
    !tail. write_place cx (MemoryPlace id []) v
      ((ee with gas_obs := []) with gas_obs := tail) =
      (INL (), ((ee with gas_obs := []) with scopes :=
        pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `?pre scope entry rest.
    find_containing_scope id ee.scopes = SOME (pre,scope,entry,rest) /\
    entry.assignable /\
    !tail. write_place cx (MemoryPlace id []) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
        with gas_obs := tail)` by
    (irule assign_local_continuation_all_tails >>
     goal_assum (drule_at (Pat `gas_admissible _ _ _`)) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     fs[gas_marked_exec_def, vyperStateTheory.bind_def]) >>
  qexistsl_tac [`pre`, `scope`, `entry`, `rest`] >> gvs[]
QED

Theorem retained_assignment_runtime_frame[local]:
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv t /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  gas_marked_exec T (ctx,fn) action (es,s0) marks (INL (v:value)) marked (OK t) /\
  return_buf_frame d ce sa s0 /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  local_ptrs_reserved ce sb /\ not_fresh_at sb p /\
  return_buf_frame d ce sb t /\ stmt_state_rel ctx fn ce cx ee t /\ ~t.vs_halted
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee t /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)` by
    fs[loweringPostsTheory.vv_post_def] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- (irule return_buf_frame_frame >> metis_tac[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  strip_tac >> drule fragGasPathMemTheory.gas_path_mem_exec >>
  simp[fragExecTheory.exit_result_def]
QED

Theorem widened_assign_retained_continuation_mem:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  type_widens_to env.type_defs ann ty /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ty /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ty
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sb = ((),sf) /\
  fn_has_code sb sf fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  FLOOKUP env.var_types id = SOME ty /\ return_buf_frame d ce sa s0 /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id))
    (Call ann (IntCall fid) args drv))) (stmt_res_ok lctx) es /\
  gas_marked_exec T (ctx,fn)
    (vyperState$bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) /\
  vv_post ctx fn ce cx (Call ann (IntCall fid) args drv) es sa sm s0
    (ee with gas_obs := []) raw vv t /\
  vv_store_bound cx ann (lowered_value_type ce (Call ann (IntCall fid) args drv))
    (ee with gas_obs := []) raw vv t /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?right ff u.
    gas_marked_exec T (ctx,fn) (write_place cx (MemoryPlace id []) v)
      (ee with gas_obs := [],t) right (INL ()) ff (OK u) /\
    stmt_state_rel ctx fn ce cx (ff with gas_obs := []) u /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\ return_buf_frame d ce sf u /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  drule_all widened_internal_call_retained_layout >> strip_tac >> gvs[] >>
  drule_all exprSimHypsTheory.ifexp_intcall_copy_source >> strip_tac >>
  `~is_word_type (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def,
      exprSimLayoutTransportTheory.compatible_word_type] >>
  gvs[exprSimMemoryPathTheory.unwrap_memory_compile, comp_return_def] >>
  drule_all retained_assignment_source_ready >> strip_tac >>
  `local_ptrs_reserved ce sb /\ not_fresh_at sb p /\
   return_buf_frame d ce sb t /\
   stmt_state_rel ctx fn ce cx (ee with gas_obs := []) t /\ ~t.vs_halted` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) retained_assignment_runtime_frame >>
     disch_then irule >> simp[vyperASTTheory.expr_type_def] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[vyperASTTheory.expr_type_def]) >>
  drule_all widened_assignment_live_destination >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
        env_consistent_def, env_context_consistent_def] >>
  `type_widens_to (get_tenv cx)
     (lowered_value_type ce (Call ann (IntCall fid) args drv)) ty` by
    metis_tac[type_widens_to_trans] >>
  `!x. p'.ptr_operand = Var x ==> not_fresh_at sb x` by
    (drule (CONJUNCT1 compiler_compile_var) >> simp[contextTheory.vv_operand_def]) >>
  `type_memory_size stv < dimword(:256)` by
    (`t.vs_alloca_next < dimword(:256)` by
       metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac) >>
  drule_all retained_copy_type_metadata >> strip_tac >>
  `compile_assign_value ce (Var p) LocMemory p'.ptr_operand F (SOME LocMemory) ty
     (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sb = ((),sf)` by
    fs[contextTheory.vv_location_def] >>
  `ty <> lowered_value_type ce (Call ann (IntCall fid) args drv) /\
   w2n w + type_memory_size stv <= t.vs_alloca_next` by simp[] >>
  `local_region ce (ee with gas_obs := []).scopes t id (w2n dw) sz` by simp[] >>
  drule_all widened_assign_copy_continuation_mem >> strip_tac >>
  qexistsl_tac [`marks'`, `ff`, `t'`] >> simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.vv_post_def] >> strip_tac >> gvs[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
