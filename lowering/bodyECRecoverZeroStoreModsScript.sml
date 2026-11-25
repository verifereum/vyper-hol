(* The output word is initialized by one covered, clean MSTORE. *)
Theory bodyECRecoverZeroStoreMods
Ancestors
  calldataOverwritePtr bodyFullUnwrapRun bodyFullUnwrapSlotFrame
  bodyFullShadowBodyInv exprSimAlloc exprSimPrecompiles exprSimProps
  bodyMemoryDefs bodyPtrDefs stateRelProj ghostPcTransportPtr
  emitHelperProps exprLoweringProps emitHelper loweringPosts loweringStateRelDefs
  fragExec venomExecSemantics venomState venomMemProps valueEncodingProps
  vyperStorageTrace vyperStorageFootprint ptrDiscipline bodyFullHashKeccakFixed
  venomInst finite_map list pred_set words arithmetic pair

Theorem ecrecover_zero_store_physical_mods:
  emit_void MSTORE [Var qo; Lit 0w] cm = ((),cz) /\
  fn_has_code cm cz func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = cm.cs_current_bb /\
  s.vs_inst_idx = LENGTH cm.cs_current_insts /\ alloca_history func s /\
  lookup_var qo s = SOME wo /\ ptr_covers G tn qo s 32 /\
  lo <= w2n wo /\ w2n wo + 32 <= s.vs_alloca_next /\
  MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas site.inst_id = SOME (w2n wo,32) /\
  (!name b n. local_region ce es.scopes s name b n ==>
     loweringStateRelDefs$regions_disjoint (w2n wo) 32 b n) /\
  local_ptrs_reserved ce cm /\ return_buf_frame d ce cm s /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at cm x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at cm x) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s /\ storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx es G tn s) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = cz.cs_current_bb /\
    t.vs_inst_idx = LENGTH cz.cs_current_insts /\ alloca_history func t /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!x n. ptr_covers G tn x s n ==> ptr_covers G' tn' x t n) /\
    mem_word_at (w2n wo) t.vs_memory = 0w /\
    (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn'.t_mem) /\
    (!b n. loweringStateRelDefs$regions_disjoint (w2n wo) 32 b n ==>
       mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    tn'.t_mem SUBSET tn.t_mem /\ (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
    ci_mono cm cz /\ return_buf_frame d ce cz t /\
    (!sk. sk.cs_next_id <= site.inst_id ==>
          wb_frame ce es es sk s t /\ pure_frame ce func es sk s t) /\
    (!es0 sk s0 G0 tn0. ghost_kept_at lo ce es0 sk G0 tn0 s0 G tn ==>
         ghost_kept_at lo ce es0 sk G0 tn0 s0 G' tn') /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es t /\ storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) 0 d ce cx es G' tn' t)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `eval_operand (Var qo) s = SOME wo` by simp[eval_operand_def] >>
  drule_all (SRULE [eval_operand_def, op_taint_def] (Q.INST [`v` |-> `Lit 0w`, `w` |-> `0w`]
    clean_mstore_overwrite_prefix_uniform_origin_joint)) >>
  disch_then (qspecl_then [`PG`] (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  `!x. FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    simp[op_taint_def] >>
  suspend "raw"
QED

Resume ecrecover_zero_store_physical_mods[raw]:
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `step_inst_base (mk_inst cm.cs_next_id MSTORE [Var qo; Lit 0w] []) s =
       OK (mstore (w2n wo) 0w s)` by (irule step_MSTORE >> simp[eval_operand_def]) >>
  `t = mstore (w2n wo) 0w s with vs_inst_idx := LENGTH cz.cs_current_insts` by
    (`t with vs_inst_idx := LENGTH cm.cs_current_insts = mstore (w2n wo) 0w s` by
       (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]) >>
     pop_assum (mp_tac o AP_TERM ``\u. u with vs_inst_idx := LENGTH cz.cs_current_insts``) >>
     simp[venom_state_component_equality]) >>
  `!x. lookup_var x t = lookup_var x s` by simp[mstore_def,lookup_var_def] >>
  `!b n. loweringStateRelDefs$regions_disjoint (w2n wo) 32 b n ==>
       mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `alloca_history func t` by
    (qpat_assum `t = _` SUBST1_TAC >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts cm cz`,`s`,`cm`] >>
     fs[run_inst_seq_def,mk_inst_def,is_terminator_def,same_blocks_def] >>
     simp[venom_state_component_equality,mstore_def]) >>
  suspend "frames"
QED

Resume ecrecover_zero_store_physical_mods[frames]:
  `ci_mono cm cz` by metis_tac[ci_mono_emit_void,SND] >>
  `return_buf_frame d ce cz t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`cm`] >>
     simp[]) >>
  `!name b n. local_region ce es.scopes s name b n ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by metis_tac[] >>
  `locals_kept ce es es s t` by (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `!sk. sk.cs_next_id <= site.inst_id ==>
      wb_frame ce es es sk s t /\ pure_frame ce func es sk s t` by
    (gen_tac >> strip_tac >> conj_tac
     >- (rewrite_tac[wb_frame_def] >> rpt conj_tac
         >- (rpt strip_tac >> metis_tac[])
         >- (rpt strip_tac >> metis_tac[])
         >- (rpt strip_tac >>
             qpat_assum `!b n. loweringStateRelDefs$regions_disjoint _ _ b n ==> _` irule >>
             `site.inst_id <> aid` by decide_tac >>
             drule_all state_allocations_disjoint >> simp[])
         >- first_assum ACCEPT_TAC)
     >- (rewrite_tac[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
         rpt strip_tac >>
         `loweringStateRelDefs$regions_disjoint off len (w2n wo) 32` by metis_tac[] >>
         qpat_assum `!b n. loweringStateRelDefs$regions_disjoint _ _ b n ==> _` irule >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) 0 d ce cx es G' tn' t` by suspend "horizon" >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by simp[mstore_memory_nondecreasing] >>
  `t.vs_data_section = s.vs_data_section` by simp[mstore_def] >>
  qpat_x_assum `t = _` kall_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by simp[] >>
  `!x. lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by simp[] >>
  `!x n. ptr_covers G tn x s n ==> ptr_covers G' tn' x t n` by simp[ptr_covers_def] >>
  `!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem` by fs[SUBSET_DEF] >>
  `!es0 sk s0 G0 tn0. ghost_kept_at lo ce es0 sk G0 tn0 s0 G tn ==>
       ghost_kept_at lo ce es0 sk G0 tn0 s0 G' tn'` by
    (rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ecrecover_zero_store_physical_mods[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`w2n wo`,`site`,`32`] >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `ghost_inv_at (DF H) 0 d ce cx es G tn s` by
    (qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp[ghost_inv_at_def,allocas_from_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at (DF H) tn' t` by
    (qpat_assum `ghost_inv_at (DF H) 0 _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     fs[stor_taint_ok_at_def,mstore_def]) >>
  qpat_x_assum `t = _` kall_tac >>
  irule unwrap_slot_copy_ghost_inv_at_mono >> simp[allocas_from_def] >>
  qexistsl_tac [`G`,`func`,`32`,`s`,`cm`,`w2n wo`,`tn`] >>
  simp[] >> fs[loweringStateRelDefsTheory.regions_disjoint_def,SUBSET_DEF] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _` irule >>
  simp[]
QED

Finalise ecrecover_zero_store_physical_mods
