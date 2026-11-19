(* The allocated Bytes/String post at the endpoint of the actual raw run. *)
Theory abiValidAllocatedBytesRunPost
Ancestors
  abiValidAllocatedLeaves abiValidAllocatedContract abiValidAllocatedResource
  abiValidBytesReentry abiDecoderBytesFrame abiDecoderBytesPhases
  abiDecoderSequenceReach abiDecoderContract abiDecoderReentry abiDecoderLoop
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiDecoderTypedCompose
  abiValidAllocatedObservations ctorAbiActualWorld exprLoweringProps
  compileEnv loweringStateRelDefs instIdxIndep venomExecSemantics venomInst
  venomState list

Theorem abi_valid_allocated_bytes_run_post:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s /\
  run_inst_seq (emitted_insts st en) s = OK actual ==>
  abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s (actual with vs_inst_idx := LENGTH en.cs_current_insts) /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_accounts = s.vs_accounts /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_transient = s.vs_transient /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_call_ctx = s.vs_call_ctx /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_immutables = s.vs_immutables /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_allocas = s.vs_allocas /\
    (actual with vs_inst_idx := LENGTH en.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op (actual with vs_inst_idx := LENGTH en.cs_current_insts) = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp_tac bool_ss [LET_THM] >>
  drule_all abi_valid_allocated_bytes_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en)` by
    metis_tac[] >>
  drule_at (Pat `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decoder_valid_bytes_reentry >>
  disch_then (qspecl_then [`en`, `ceiling`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u = actual` by
    (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >> simp[]) >>
  qpat_x_assum `u = actual` SUBST_ALL_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st en)` by fs[EVERY_MEM] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA)
      (emitted_insts st en)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac
     >- (qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _) _`
           (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
     qpat_assum `EVERY (\i. _ /\ ~is_alloca_op _) _`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[is_alloca_op_def]) >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `reached` strip_assume_tac)) >>
  qpat_x_assum `reached = _` SUBST_ALL_TAC >>
  `val_in_memory tv v d actual.vs_memory` by (first_x_assum irule >> simp[]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s actual` by
    (irule abi_valid_allocated_scratch_free_resource >> metis_tac[]) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce ty) s actual` by
    (irule abi_valid_allocated_frame_scratch_free >> simp[]) >>
  qhdtm_assum `abi_malformed_resource_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  qhdtm_assum `abi_valid_allocated_frame`
    (assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_frame_def, abi_malformed_site_range_def]) >>
  simp[abi_valid_allocated_post_def, fresh_vars_wrt_def,
    abi_malformed_resource_post_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
    abi_valid_allocated_frame_def, abi_malformed_site_range_def] >>
  qhdtm_x_assum `abi_valid_allocated_entry` kall_tac >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE fs[fresh_vars_wrt_def])
QED
