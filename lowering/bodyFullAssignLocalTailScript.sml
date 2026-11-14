(* Direct joint scalar instruction of a local Assign. *)
Theory bodyFullAssignLocalTail
Ancestors
  stmtSimAssign stmtSimAssignStore fragGasSeqPtr fragGasOriginPtr
  exprPtrUnwrapCopyEdges instMemFrontier
  wordLoadStorePtr emitHelperProps exprLowering stmtLowering compileEnv
  fragExec memSafeRun exprLoweringProps bodyFullMemoryFrames
  assignBasePtrLocalStore bodyPtrDefs localPtrsProps valueEncodingProps exprSimProps
  vyperLookup loweringStateRelDefs stmtSimDeclStore ptrDiscipline
  venomExecProofs venomState venomInst bodyFullUnwrapRun bodyMemoryDefs
  stmtSimDefs vyperStorageFootprint vyperStorageBackend emitHelper list rich_list
  loweringPosts stmtSimProps

Theorem body_assign_local_word_full_edge:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  lookup_var p s = SOME dst /\ eval_operand op s = SOME w /\
  w2n dst + 32 <= s.vs_alloca_next ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((mstore (w2n dst) w s) with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sm.cs_next_id MSTORE [Var p;op] [])
       (mstore (w2n dst) w s),
     step_taint (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s
       (mstore (w2n dst) w s) tn)
Proof
  strip_tac >> drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `emit_void MSTORE [Var p;op] sm = ((),sb)` >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id MSTORE [Var p;op] [])` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s =
     OK (mstore (w2n dst) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `inst_mem_below_frontier (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s /\
   inst_dload_in_section (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s /\
   (mk_inst sm.cs_next_id MSTORE [Var p;op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst sm.cs_next_id MSTORE [Var p;op] []).inst_opcode` by
    simp[mk_inst_def,is_terminator_def,below_frontier_MSTORE,
         eval_operand_def,inst_dload_in_section_def] >>
  drule_all straight_line_origin_ptr_edge >> simp[mk_inst_def]
QED

Theorem body_assign_local_word_full_store:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env0 es0 /\
  stmt_state_rel H ctx func cenv cx es s /\ dead_lo_ok H D lo cenv cx /\
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  lookup_var p s = SOME dst /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\ store_lays_out etv entry.type v ==>
  ?t tf.
    t = (mstore (w2n dst) (typed_val_to_w256 etv v) s) with
      vs_inst_idx := SUC s.vs_inst_idx /\
    tf = step_taint (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s
      (mstore (w2n dst) (typed_val_to_w256 etv v) s) tn /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf) /\
    stmt_state_rel H ctx func cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
    ghost_inv_at D lo d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G tf t
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `local_region cenv es.scopes s id (w2n dst) sz` by simp[local_region_def] >>
  `type_memory_size entry.type = 32 /\ val_wf entry.type v /\
   val_footprint entry.type v <= 32` by
    (fs[store_lays_out_def] >> metis_tac[val_footprint_le]) >>
  `32 <= sz /\ w2n dst + sz <= s.vs_alloca_next` by
    (fs[local_ptrs_rel_def] >>
     first_x_assum (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  `0 < sz` by decide_tac >>
  `lo <= w2n dst` by (drule_all body_full_local_region_lower_bound >> simp[]) >>
  `ptr_covers G tn p s 32 /\ allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_def,ptr_covers_def] >>
     first_x_assum (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >>
     simp[] >> strip_tac >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `w2n dst + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`sm.cs_next_id`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK ((mstore (w2n dst) (typed_val_to_w256 etv v) s) with
       vs_inst_idx := SUC s.vs_inst_idx),G,tf)` by
    (drule_all body_assign_local_word_full_edge >>
     disch_then (qspecl_then [`explicit`,`PG`,`D`] mp_tac) >> simp[Abbr `tf`]) >>
  qexistsl_tac [`(mstore (w2n dst) (typed_val_to_w256 etv v) s) with
    vs_inst_idx := SUC s.vs_inst_idx`,`tf`] >> simp[Abbr `tf`] >>
  conj_tac >- (simp[stmt_state_rel_inst_idx] >>
    irule stmt_state_rel_write_local_store >> metis_tac[]) >>
  suspend "ghost"
QED

Resume body_assign_local_word_full_store[ghost]:
  qmatch_goalsub_abbrev_tac `ghost_inv_at D lo d cenv cx ee G tf t` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = (mstore (w2n dst) (typed_val_to_w256 etv v) s).vs_memory /\
   (!x. lookup_var x t = lookup_var x s)` by
    simp[Abbr `t`,mstore_def,lookup_var_def] >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  `stor_taint_ok_at D tf t` by
    (fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
     simp[Abbr `tf`,Abbr `t`,mstore_def,contract_storage_def,contract_transient_def,
          step_taint_def,imm_taint_def,mk_inst_def]) >>
  unabbrev_all_tac >>
  irule (body_full_local_scope_ghost_post |> Q.INST [`n` |-> `32`]) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`,`func`,`sa`,`tn`] >> simp[op_taint_def] >>
  conj_tac >- (rpt strip_tac >>
    irule assign_base_ptr_clean_window_robust_value >> simp[] >>
    qexistsl_tac [`(mstore (w2n dst) (typed_val_to_w256 etv v) s).vs_memory`,
                  `32`,`tn.t_mem`] >> simp[arithmeticTheory.ADD_COMM] >>
    fs[store_lays_out_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Finalise body_assign_local_word_full_store

Theorem body_assign_local_word_full_post:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\
  expr_post H ctx func cenv cx e es sa sm s0 ee v op s /\
  return_buf_frame d cenv sa s0 /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest) /\
  ef = ee with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest /\
  t = (mstore (w2n (dst:256 word)) (typed_val_to_w256 etv v) s) with vs_inst_idx := SUC s.vs_inst_idx /\
  tf.t_var = tn.t_var /\ alloca_history func t /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx ef t /\ ghost_inv_at D lo d cenv cx ef G tf t ==>
  ?ce.
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
    (~block_is_terminated sb /\ ce = cenv) /\
    cenv_top_ext cenv ce (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) /\
    stmt_state_rel H ctx func ce cx ef t /\
    storage_well_formed_on cx ef (FST H) /\
    return_buf_frame d ce sb t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at D lo d ce cx ef G tf t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> drule_all assign_local_word_code_parts >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
   ~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,fresh_id_def,
          emit_def,comp_return_def] >> strip_tac >>
     Cases_on `sm.cs_current_insts` >>
     gvs[block_is_terminated_def,LAST_APPEND,LAST_CONS_cond,mk_inst_def,is_terminator_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `sm.cs_next_var = sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >> gvs[] >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,fresh_id_def,emit_def,comp_return_def] >>
     strip_tac >> gvs[]) >>
  `!x. lookup_var x t = lookup_var x s` by simp[lookup_var_def,mstore_def] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by simp[mstore_def] >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
     fs[expr_post_def] >> metis_tac[]) >>
  qexists_tac `cenv` >>
  fs[stmt_lands_def,cenv_top_ext_refl,expr_post_def,ghost_kept_at_def,
     op_taint_def,storage_well_formed_on_def,get_storage_scopes,mstore_def]
QED

Theorem body_assign_local_word_full_history:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var p s = SOME dst /\ eval_operand op s = SOME w ==>
  alloca_history func ((mstore (w2n dst) w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sb'.cs_current_bb /\
   sb.cs_current_insts = sb'.cs_current_insts ++ [mk_inst sb'.cs_next_id MSTORE [Var p;op] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,fresh_id_def,emit_def,comp_return_def] >>
     strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sb'.cs_next_id MSTORE [Var p;op] []) s = OK (mstore (w2n dst) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst sb'.cs_next_id MSTORE [Var p;op] []] s = OK (mstore (w2n dst) w s)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) [mk_inst sb'.cs_next_id MSTORE [Var p;op] []]` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all emitted_alloca_history >> simp[arithmeticTheory.ADD1]
QED

Theorem body_assign_local_word_full_tail:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env0 es /\
  expr_post H ctx func cenv cx e es sa sm s0 ee v op s /\
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s0 /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest) /\
  lookup_var p s = SOME dst /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\ store_lays_out etv entry.type v ==>
  ?t tf.
    t = (mstore (w2n dst) (typed_val_to_w256 etv v) s) with vs_inst_idx := SUC s.vs_inst_idx /\
    tf = step_taint (mk_inst sm.cs_next_id MSTORE [Var p;op] []) s
      (mstore (w2n dst) (typed_val_to_w256 etv v) s) tn /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf) /\
    ?ce.
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
      (~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce
        (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) /\
      stmt_state_rel H ctx func ce cx
        (ee with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
      storage_well_formed_on cx
        (ee with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) (FST H) /\
      return_buf_frame d ce sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at D lo d ce cx
        (ee with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G tf t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[expr_post_def] >>
  `alloca_inv s` by fs[stmt_state_rel_def,state_rel_def] >>
  drule_all body_assign_local_word_full_store >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`tf`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `alloca_history func t` by (gvs[] >> drule_all body_assign_local_word_full_history >> simp[]) >>
  `tf.t_var = tn.t_var` by
    (gvs[] >> drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`,`G`,`sm.cs_next_id`] strip_assume_tac) >> simp[]) >>
  irule body_assign_local_word_full_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`dst`,`e`,`ee`,`es`,`etv`,`op`,`ret_ty`,`s`,`sm`,`tn`] >> simp[]
QED
