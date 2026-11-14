(* A joint local AugAssign write: one endpoint shared by all horizons. *)
Theory augAssignFullLocalWriteOutcome
Ancestors
  augAssignFullLocalStorePost fragGasOriginPtr fragGasSeqPtr
  gasOutcomeFullCompose instMemFrontier memSafeRun venomExecSemantics
  emitHelperProps codegenRel contextCodegenRel unitTransformDefs
  stmtSimAugAssign stmtSimAssignStore vyperStorageFootprint
  exprLoweringProps fragExec wordLoadStorePtr venomInst venomState exprPtrUnwrapCopyEdges
  exprSimWordArgs stmtSimDefs bodyPtrDefs

Theorem augassign_local_write_step_full[local]:
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\ fn_has_code sc sf func /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ cs_extends sa sc /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME aw /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\
  write_place cx (MemoryPlace id []) v es = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) /\
  (!entry. lookup_scopes id es.scopes = SOME entry ==> store_lays_out etv entry.type v) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv es s) /\
  MAP FDOM es.scopes = MAP FDOM es0.scopes /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sc s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  storage_trace_domain cx st0 es.storage_trace /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\ lo <= w2n aw /\
  w2n aw + 32 <= s.vs_alloca_next ==>
  ?t Gf tf.
    t = (mstore (w2n aw) (typed_val_to_w256 etv v) s with
      vs_inst_idx := LENGTH sf.cs_current_insts) /\
    Gf = step_prov PG G (mk_inst sc.cs_next_id MSTORE [Var p;op] [])
      (mstore (w2n aw) (typed_val_to_w256 etv v) s) /\
    tf = step_taint (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s
      (mstore (w2n aw) (typed_val_to_w256 etv v) s) tn /\
    res = INL () /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
      ?cenv'. stmt_lands lctx sf res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
        cenv_top_ext cenv cenv' ee.scopes /\
        stmt_state_rel H ctx func cenv' cx ee t /\
        storage_well_formed_on cx ee (FST H) /\
        return_buf_frame d cenv' sf t /\ alloca_history func t /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv' cx ee Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
          op_taint tf (Var x) = op_taint tn0 (Var x)))
Proof
  strip_tac >>
  qabbrev_tac `t = mstore (w2n aw) (typed_val_to_w256 etv v) s with vs_inst_idx := LENGTH sf.cs_current_insts` >>
  qabbrev_tac `Gf = step_prov PG G (mk_inst sc.cs_next_id MSTORE [Var p;op] []) (mstore (w2n aw) (typed_val_to_w256 etv v) s)` >>
  qabbrev_tac `tf = step_taint (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s (mstore (w2n aw) (typed_val_to_w256 etv v) s) tn` >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  `res = INL ()` by (drule_all write_place_local >> strip_tac >> simp[]) >>
  conj_tac >- simp[] >> gen_tac >> strip_tac >>
  reverse conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `Abbrev (t = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qpat_assum `Abbrev (Gf = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qpat_assum `Abbrev (tf = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      drule_all augassign_local_store_post_full >>
      simp[Abbr `t`, Abbr `Gf`, Abbr `tf`]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >> fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sc.cs_next_id MSTORE [Var p;op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn
    (mk_inst sc.cs_next_id MSTORE [Var p;op] []) s` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n aw) (typed_val_to_w256 etv v) s with vs_inst_idx := SUC s.vs_inst_idx),Gf,tf)` by
    (simp[Abbr `Gf`, Abbr `tf`] >>
     mp_tac (Q.INST [`D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`, `i` |-> `mk_inst sc.cs_next_id MSTORE [Var p;op] []`,
       `u` |-> `mstore (w2n (aw:bytes32)) (typed_val_to_w256 etv v) s`] straight_line_origin_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, step_inst_base_opcode_eqs,
       exec_write2_def, eval_operand_def, fixed_source_write_range_def]) >>
  `LENGTH sf.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `~t.vs_halted` by simp[Abbr `t`, mstore_def] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    (qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
     simp[Abbr `t`, GSYM arithmeticTheory.ADD1]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem augassign_local_write_outcome_full:
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\ fn_has_code sc sf func /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ cs_extends sa sc /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME aw /\ eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  op_taint tn op = {} /\
  write_place cx (MemoryPlace id []) v (mid with gas_obs := []) = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) /\
  (!entry. lookup_scopes id mid.scopes = SOME entry ==> store_lays_out etv entry.type v) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv mid s) /\
  MAP FDOM mid.scopes = MAP FDOM es0.scopes /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sc s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\ lo <= w2n aw /\
  w2n aw + 32 <= s.vs_alloca_next ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (write_place cx (MemoryPlace id []) v) (mid,s,G,tn)
    (\H res ee Gf tf t. ?cenv'.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv' sf t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee Gf tf t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
    stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) s /\
    storage_well_formed_on cx (mid with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G tn s /\
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv (mid with gas_obs := []) s` by
    (gen_tac >> strip_tac >> fs[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_gas_obs, ghost_inv_at_def,
       storage_well_formed_on_def, alloca_frame_def] >>
     conj_tac
     >- (rpt gen_tac >>
         qpat_x_assum `!b slot tv. MEM _ _ ==> slots_in_range _ _ _`
           (qspecl_then [`b`,`slot`,`tv`] mp_tac) >>
         Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es0.scopes /\
   storage_trace_domain cx st0 (mid with gas_obs := []).storage_trace /\
   (!entry. lookup_scopes id (mid with gas_obs := []).scopes = SOME entry ==>
     store_lays_out etv entry.type v)` by simp[] >>
  drule_all augassign_local_write_step_full >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `ee.storage_trace = mid.storage_trace /\ ee.gas_obs = []` by
    (drule_all write_place_local >> strip_tac >> simp[]) >>
  `ee with gas_obs := [] = ee` by (simp[vyperStateTheory.evaluation_state_component_equality]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`res`,`t`,`tf`] >> simp[] >>
  conj_tac
  >- (gen_tac >> drule_all write_place_local_gas_obs >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED
