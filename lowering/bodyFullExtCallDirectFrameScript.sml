Theory bodyFullExtCallDirectFrame
Ancestors
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderRegisteredEffect
  bodyFullExtCallEncoderStmtFrame bodyFullExtCallEncoderCallerFrames
  bodyFullAbiEncodeOriginFloor bodyFullPathHistory
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  allocationGrowth stateRelProj bodyPtrDefs loweringStateRelDefs
  fragGasOriginPtr fragGasOrigin fragGasMode freshWrites
  ctorDeployMemoryRunMemEntryLiteralPath[qualified,ignore_grammar]
  compileEnv ptrDiscipline vyperContext vyperValue valueEncodingDefs venomState venomInst
  finite_map pred_set list alist words

(* Bridge a pure encoder phase to the external-call argument row package.
   Materialization uses its own source-semantic frame at the unwrap cut. *)
Theorem extcall_direct_encode_phase_frame:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  ghost_inv_at D lo d ce cx ee G tn s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ local_ptrs_reserved ce cut /\
  cut.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x) /\
  (!x. not_fresh_at st x ==>
     FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!b n.
     ((b = 0 /\ n = lo) \/
      (?name. local_region ce ee.scopes s name b n) \/
      (?site. FLOOKUP s.vs_allocas site = SOME (b,n) /\ site < cut.cs_next_id)) ==>
     mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)) /\
  (ce.ce_is_ctor ==> !src name tv v off.
    (src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src)) /\
    FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
  stmt_state_rel H ctx func ce cx ee t /\ ghost_inv_at D lo d ce cx ee G' tn' t /\
  wb_frame ce ee ee cut s t /\ ghost_kept_at lo ce ee cut G tn s G' tn' /\
  alloca_history func t
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_phase_effect >>
  drule_then assume_tac window_phase_labels >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `allocation_growth s t` by
    (fs[allocation_growth_def, window_alloca_growth_def] >> metis_tac[]) >>
  `!x w. not_fresh_at cut x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    metis_tac[window_phase_vars, not_fresh_at_mono] >>
  `!x. not_fresh_at cut x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all abi_encode_origin_path_allocas_from >> strip_tac >>
  `stor_taint_ok_at D tn' t` by
    (qpat_assum `ghost_inv_at D _ _ _ _ _ _ _ _`
       (mp_tac o cj 4 o REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `abi_encode_exec_frame func s t`
       (strip_assume_tac o REWRITE_RULE [abi_encode_exec_frame_def, abi_encode_semantic_obs_fields]) >>
     qpat_assum `abi_encoder_registered_effect ids outs s t`
       (strip_assume_tac o REWRITE_RULE [abi_encoder_registered_effect_def]) >>
     simp[stor_taint_ok_at_def]) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,G',tn')`
       (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP gas_origin_path_erase o cj 1) >>
     simp[gas_marked_path_def]) >>
  `!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = w2n n` by
    (drule_then assume_tac stmt_state_rel_alloca_size >>
     drule ctorDeployMemoryRunMemEntryLiteralPathTheory.ctor_path_literal_sizes >>
     disch_then (qspec_then `t` mp_tac) >> asm_rewrite_tac[]) >>
  `!name b n. local_region ce ee.scopes s name b n ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`b`,`n`] mp_tac) >> metis_tac[]) >>
  `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < cut.cs_next_id ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`b`,`n`] mp_tac) >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee t` by
    (match_mp_tac (Q.INST [`q` |-> `s`,`st` |-> `cut`,
        `ids` |-> `ids`,`outs` |-> `outs`] extcall_encoder_stmt_frame) >>
     asm_rewrite_tac[] >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >> metis_tac[]) >>
  `wb_frame ce ee ee cut s t /\ ghost_kept_at lo ce ee cut G tn s G' tn' /\
   ghost_inv_at D lo d ce cx ee G' tn' t` by
    (match_mp_tac (Q.INST [`cenv` |-> `ce`,`q` |-> `s`,`se` |-> `cut`,
       `Gq` |-> `G`,`tq` |-> `tn`,`Gf` |-> `G'`,`tf` |-> `tn'`]
       extcall_encoder_caller_frames) >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> metis_tac[body_full_path_alloca_history]
QED
