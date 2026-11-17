(* Joint write continuations.  Every store endpoint is fixed before H. *)
Theory augAssignFullWriteback
Ancestors
  augAssignFullMemoryWriteSource augAssignFullMemoryLocalResources
  augAssignFullMemoryStorePath augAssignFullMstoreSafety
  augAssignFullMstoreGhostTransport augAssignFullImmutableWriteSource
  augAssignFullImmutableLocalResources augAssignFullImmutableDeadMask
  augAssignFullStorageEndpoint gasOutcomeFullCompose bodySimFull
  stateRelProj bodyMemoryDefs bodyFullTargetDefs loweringShapeRules
  bodyBinopFragMemory stmtSimAugAssignPlaceMemory exprOpenPrimitives
  vyperScopePreservation tuplePlaceStep wordLoadStorePtr
  bodySimAugPlaceLoad loweringStateRelDefs exprLoweringProps
  bodyPtrDefs ptrDiscipline valueEncodingProps stmtSimDefs
  memoryValueEncoding compileEnv venomState venomInst
  loweringPosts exprSimProps stmtSimDeclStore
  finite_map pred_set list words

Theorem augassign_memory_write_machine_resources[local]:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (dst,loc,pty) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ store_lays_out etv ptv v /\
  write_place cx (MemoryPlace id path) v es = (INL (),es') /\
  eval_operand dst s = SOME a /\ eval_operand op s = SOME w /\
  op_taint tn op = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_frame c0 es0 sa0 s0 cenv es s /\
  u = (mstore (w2n a) w s with vs_inst_idx := pc) ==>
  w2n a + 32 <= s.vs_alloca_next /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid MSTORE [dst;op] []) s /\
  alloca_frame c0 es0 sa0 s0 cenv es' u
Proof
  strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `k + type_memory_size ptv <= type_memory_size entry.type` by
    metis_tac[mem_path_offset_sound] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  conj_tac >- decide_tac >>
  `ptr_covers G tn p s sz /\ allocas_from lo s` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac >- suspend "pointer" >>
  suspend "allocation"
QED

Resume augassign_memory_write_machine_resources[pointer]:
  `op_taint tn dst = {}` by fs[target_ptr_ok_def] >>
  `?q. dst = Var q /\ ptr_covers G tn q s 32` by
    (fs[target_ptr_ok_def, ptr_covers_def] >>
     `?q. dst = Var q` by
       (Cases_on `dst` >> gvs[op_prov_def] >> metis_tac[]) >>
     gvs[ptr_covers_def, op_prov_def, eval_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  irule augassign_mstore_ptr_check >> simp[]
QED

Resume augassign_memory_write_machine_resources[allocation]:
  `local_region cenv es.scopes s id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `MAP FDOM es'.scopes = MAP FDOM es.scopes` by
    metis_tac[write_place_scopes_dom] >>
  irule alloca_frame_region_write >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  simp[] >> conj_tac >- simp[lookup_var_def, mstore_def] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Finalise augassign_memory_write_machine_resources

Theorem augassign_memory_writeback_full:
  body_inv tops ctx cenv cx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path))
    (dst,loc,pty) G tn s /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (res,es') /\ stmt_res_ok lctx res /\
  emit_void MSTORE [dst;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  eval_operand dst s = SOME a /\
  eval_operand op s = SOME (typed_val_to_w256 etv v) /\ op_taint tn op = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  un = (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a + 32}) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 es0 sa0 s0 cenv es s /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!n b sz'. local_region c0 es0.scopes s0 n b sz' ==>
        off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (write_place cx (MemoryPlace id path) v) (es,s,G,tn)
    (\H r ee G' tn' t.
      stmt_lands lctx sb r t /\ ~t.vs_halted /\
      (r = INL () ==> ~block_is_terminated sb) /\
      cenv_top_ext cenv cenv ee.scopes /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==> FLOOKUP G' x = FLOOKUP G0 x /\
        op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c0 es0 sa0 s0 cenv ee t /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!n b sz'. local_region c0 es0.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s` by metis_tac[] >>
  drule_all augassign_memory_write_source_joint >> strip_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G`, `es'`, `res`, `u`, `un`] >> simp[] >>
  conj_tac >- metis_tac[aug_place_memory_write_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  suspend "memory_horizon"
QED

Resume augassign_memory_writeback_full[memory_horizon]:
  `w2n a + 32 <= s.vs_alloca_next /\
   ptr_inst_ok (DF H) lo 0 ctx func G tn
     (mk_inst sa.cs_next_id MSTORE [dst;op] []) s /\
   alloca_frame c0 es0 sa0 s0 cenv es' u` by
    (irule augassign_memory_write_machine_resources >> simp[] >>
     conj_tac >- (qexists_tac `LENGTH sb.cs_current_insts` >> simp[]) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `target_ptr_ok _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `store_lays_out _ _ _`)) >>
     qexists_tac `H` >> simp[]) >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn
      (mk_inst sa.cs_next_id MSTORE [dst;op] []) s` by
    (rpt strip_tac >>
     qpat_assum `!H. _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     irule (cj 2 augassign_memory_write_machine_resources) >> simp[] >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `target_ptr_ok _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `store_lays_out _ _ _`)) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`H'`, `ty`] >> simp[]) >>
  `step_prov PG G (mk_inst sa.cs_next_id MSTORE [dst;op] [])
      (mstore (w2n a) (typed_val_to_w256 etv v) s) = G /\
   step_taint (mk_inst sa.cs_next_id MSTORE [dst;op] []) s
      (mstore (w2n a) (typed_val_to_w256 etv v) s) tn = un` by
    (simp[] >> irule augassign_mstore_clean_transition >> simp[]) >>
  conj_tac
  >- (irule (cj 1 augassign_mstore_endpoint_path) >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[] >>
      qexistsl_tac [`cx`, `es'`, `st0`] >> simp[]) >>
  suspend "memory_post"
QED

Resume augassign_memory_writeback_full[memory_post]:
  `!name ee p sz.
     lookup_scopes name es'.scopes = SOME ee /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     ptr_covers G tn p s sz /\
     !w mem. lookup_var p s = SOME w /\
       mem_agree_outside un.t_mem u.vs_memory mem ==>
       val_in_memory ee.type ee.value (w2n w) mem` by
    (rpt gen_tac >> strip_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] augassign_memory_store_local_resources) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `store_lays_out _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `lookup_scopes _ es'.scopes = SOME ee`)) >>
     simp[] >> qexists_tac `LENGTH sb.cs_current_insts` >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx es' G un u` by
    (irule augassign_mstore_ghost_transport >> reverse conj_tac
     >- (goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
         qexistsl_tac [`w2n a`, `LENGTH sb.cs_current_insts`, `typed_val_to_w256 etv v`] >>
         qpat_x_assum `!name ee p sz. _` mp_tac >> simp[]) >>
     `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
       (irule (INST_TYPE [alpha |-> ``:256``] augassign_memory_store_prefix_preserved) >>
        goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
        goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
        goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
        goal_assum (drule_at (Pat `store_lays_out _ _ _`)) >>
        goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
        simp[] >> qexistsl_tac [`DF H`, `LENGTH sb.cs_current_insts`] >> simp[]) >>
     fs[ghost_inv_at_def] >> metis_tac[]) >>
  `es'.accounts = es.accounts /\ es'.tStorage = es.tStorage` by
    (drule vyperPlaceFramesTheory.write_memory_place_frame >> strip_tac >> simp[]) >>
  `storage_well_formed_on cx (es' with gas_obs := []) (FST H)` by
    fs[vyperStorageFootprintTheory.storage_well_formed_on_def,
       boolTheory.FORALL_BOOL, vyperStorageBackendTheory.get_storage_def] >>
  `ghost_inv_at (DF H) lo d cenv cx (es' with gas_obs := []) G un u` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ es' _ _ _` mp_tac >>
     simp[NoAsms, ghost_inv_at_def] >> strip_tac >> simp[]) >>
  `~block_is_terminated sb` by
    (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `sa.cs_next_var = sb.cs_next_var /\ sa.cs_current_bb = sb.cs_current_bb` by
    (gvs[emit_void_eq]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[lookup_var_def, mstore_def]) >>
  `alloca_history func u` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`alloca_history func s`, `fn_has_code sa sb func`,
        `emit_void _ _ _ = _`, `u = _`,
        `s.vs_current_bb = _`, `s.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[emit_void_eq] >>
     qpat_assum `s.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
     irule (SRULE [] (Q.INST
       [`insts` |-> `[mk_inst sa.cs_next_id MSTORE [dst;op] []]`]
       (SPEC_ALL alloca_history_no_alloca_slice))) >>
     simp[mstore_def] >>
     qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> goal_assum (drule_at Any) >>
     simp[DROP_APPEND, mk_inst_def] >> metis_tac[]) >>
  fs[stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl,
       lookup_var_def, mstore_def, op_taint_def, allocas_below_fmp_def] >>
  metis_tac[]
QED

Finalise augassign_memory_writeback_full
