Theory createCtorEncoderPhaseMods
Ancestors freshWrites[qualified,ignore_grammar]
  createExprSizeExitDefsMods bodyFullExtCallDirectState bodyFullExtCallDirectPhase
  abiEncodeValuesPhases abiEncoderWindowPhase createCtorEncoderWindowImmMods
  createCtorEncoderWindowCallerMods
  bodyFullHashKeccakFixed exprSimWordArgs exprSimAbiEncodeExecFrame stateRelProj
  loweringPosts loweringStateRelDefs fragGasOriginPtr fragExec exprLowering exprLoweringProps
  compileEnv context contractABI venomState venomInst finite_map pred_set list arithmetic pair words
Libs horizonTypeLib

(* A registered encoder phase preserves the linked saved-state contract.  The
   phase starts at the saved state's actual input cut; its output may contain
   arbitrary payload writes and registered scratch allocations. *)
Theorem ctor_encoder_saved_phase_mods:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  (pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_x_assum `abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee u /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func ce ee.scopes u /\ alloca_inv u` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_room ctx func u` by metis_tac[stmt_state_rel_alloca_room] >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `fmp_room ctx func u` by metis_tac[stmt_state_rel_fmp_room] >>
  `EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs /\
    EVERY (\(p,n). pbase+dst_offset <= p) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     res_tac >> decide_tac) >>
  mp_tac (Q.INST [`front` |-> `se`,`st` |-> `a`,`en` |-> `c`,`s` |-> `u`,`t` |-> `v`,
    `b` |-> `pbase`,`cap` |-> `capacity`,`G` |-> `Gu`,`G'` |-> `Gv`,
    `tn` |-> `tu`,`tn'` |-> `tv`] ctor_encoder_window_caller_mods) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  mp_tac (Q.INST [`st` |-> `a`,`en` |-> `c`,`s` |-> `u`,`t` |-> `v`,
    `b` |-> `pbase`,`cap` |-> `capacity`,`G` |-> `Gu`,`G'` |-> `Gv`,
    `tn` |-> `tu`,`tn'` |-> `tv`]
    abi_encode_saved_prefix_frame) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `!x w n. not_fresh_at a x /\ eval_operand (Var x) u = SOME w /\
    ptr_covers Gu tu x u n ==> eval_operand (Var x) v = SOME w /\ ptr_covers Gv tv x v n` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func a c ids outs u v` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!x w n. not_fresh_at a x /\ _ ==> eval_operand (Var x) v = _ /\ _`
    (fn th => MAP_EVERY (fn args => mp_tac (Q.SPECL args th) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac)
       [[`root`,`n2w pbase`,`capacity`],[`dst`,`n2w (pbase+dst_offset)`,`capacity-dst_offset`]]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s`
    (qspec_then `hz` (drule_then assume_tac)) >>
  `wb_frame ce ee ee se s v /\ ghost_kept_at lo ce ee se G tn s Gv tv` by
    (conj_tac
     >- (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
         qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se u v` (irule_at Any) >> simp[])
     >- (irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
         qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
         qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
         qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
         qpat_assum `ghost_kept_at lo ce ee se Gu tu u Gv tv` (irule_at Any) >> simp[])) >>
  `immutable_frame_mods func ce cx ee v` by
    (irule ctor_encoder_window_immutable_mods >>
     qpat_assum `window_phase ctx func a c ids outs u v` (irule_at Any) >>
     qpat_assum `abi_encode_exec_frame func u v` (irule_at Any) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee u` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved ce se` (irule_at Any) >>
     qexistsl_tac [`shared`,`capacity`,`pbase`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ci_mono a c` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `s.vs_alloca_next <= v.vs_alloca_next /\
   se.cs_next_var <= c.cs_next_var /\ shared < c.cs_next_id` by
    (conj_tac >- (irule LESS_EQ_TRANS >> qexists `u.vs_alloca_next` >> asm_rewrite_tac[]) >>
     conj_tac >- (irule LESS_EQ_TRANS >> qexists `a.cs_next_var` >> asm_rewrite_tac[]) >>
     irule LESS_LESS_EQ_TRANS >> qexists `a.cs_next_id` >> asm_rewrite_tac[]) >>
  conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC [abi_encode_saved_state_mods_def] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee v /\ _`
        (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
