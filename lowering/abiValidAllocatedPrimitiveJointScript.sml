(* Primitive allocated decoding at the actual execution endpoint. *)
Theory abiValidAllocatedPrimitiveJoint
Ancestors
  abiValidAllocatedLeaves abiValidAllocatedContract abiValidDecodedMetadata
  abiValidAllocatedResource abiDecoderPrimitiveMemory abiDecoderReentryPointer
  abiDecoderClampedWord abiDecoderSequenceReach abiDecoderTypedCompose
  abiDecoderContract abiDecoderLoop abiMalformedRecursiveInterface
  abiMalformedSiteFrame exprLoweringProps emitHelperProps compileEnv loweringStateRelDefs
  instIdxIndep fragExec venomExecSemantics venomState venomInst list words
  vyperABIValid contractABI abiDecoderCoherence
  abiDecodePtrWordJoint abiDecodePtrMemberFrame decoderGhostFramePtr
  abiValidAllocatedObservations ctorAbiActualWorld abiCallerAllocation
  stateRelProj bodyFullPathHistory calldataTypedRobustPtr valueEncodingTyping
  exprSimProps abiMalformedConstructorInduction abiDecoderTypedContract
  abiDecoderReentry bodyPtrDefs freshWrites fragGasOriginPtr ptrDiscipline
  finite_map pred_set arithmetic

Theorem abi_valid_allocated_primitive_run[local]:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    run_inst_seq (emitted_insts st en) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_primitive_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en)` by
    metis_tac[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `mem_bytes_at (B+p) 32 (abi_decode_source MLOAD s) =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP p xs))` by
    simp[abi_decode_source_def] >>
  qhdtm_assum `EVERY` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  drule_all abi_decoder_primitive_memory_reentry >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by fs[EVERY_MEM] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA)
      (emitted_insts st en)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac
     >- (qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
         simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
     qpat_assum `EVERY (\i. _ /\ _ /\ ~is_alloca_op _) _`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[is_alloca_op_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s actual` by
    (irule abi_valid_allocated_scratch_free_resource >> metis_tac[]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
      d (type_memory_bytes ce ty) s actual` by
    (irule abi_valid_allocated_frame_scratch_free >> simp[]) >>
  `run_inst_seq (emitted_insts st en) s =
     OK (actual with vs_inst_idx := s.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by
       fs[EVERY_MEM] >>
     qspecl_then [`emitted_insts st en`, `s`, `s.vs_inst_idx`]
       mp_tac run_inst_seq_inst_idx >> simp[exec_result_map_def]) >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists_tac `t` >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
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

Theorem abi_valid_allocated_primitive_joint_observations:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  !PG. ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ptr_covers G' tn' output t (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s t a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  drule_all abi_valid_allocated_primitive_run >> strip_tac >>
  drule_all abi_valid_allocated_primitive_input >> strip_tac >>
  qhdtm_x_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  `p+32 <= L` by
    (drule abi_malformed_constructor_primitive_metadata >>
     disch_then (qspec_then `DecPrimWord clamp` mp_tac) >> simp[] >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> gvs[]) >>
  qhdtm_x_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_x_assum `EVERY` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qhdtm_x_assum `abi_malformed_allocated_window`
    (strip_assume_tac o REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  qhdtm_x_assum `abi_malformed_destination`
    (strip_assume_tac o REWRITE_RULE [abi_malformed_destination_def]) >>
  `B+L <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next` by
    (conj_tac
     >- (irule abi_caller_allocation_end >> simp[] >> qexistsl [`cap`,`live`,`B`] >> simp[]) >>
     irule abi_caller_allocation_end >> simp[] >> qexistsl [`sz`,`dstid`,`b`] >> gvs[]) >>
  `!i. B <= i /\ i < B+L ==> ~(d <= i /\ i < d+32)` by
    (`B+cap <= b \/ b+sz <= B` by metis_tac[abi_caller_allocation_separate] >>
     gvs[] >> decide_tac) >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecPrimWord clamp) st = ((),en) /\ lookup_var output s = SOME (n2w d) /\
   not_fresh_at st output /\ w2n (n2w B:256 word) + L <= s.vs_alloca_next /\
   w2n (n2w B:256 word) + p < dimword(:256) /\
   w2n (n2w d:256 word) + 32 <= s.vs_alloca_next /\ ptr_covers G tn output s 32` by
    gvs[eval_operand_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        not_fresh_at_def, w2n_n2w, LESS_MOD] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all abi_decode_allocated_word_success_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t.vs_inst_idx = LENGTH en.cs_current_insts` by fs[abi_valid_allocated_post_def] >>
  `t with vs_inst_idx := LENGTH en.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,H',tf)` by
    (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ [] _` mp_tac >> simp[]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP H' x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
  `lookup_var output t = lookup_var output s /\
   lookup_var source t = lookup_var source s` by
    (`eval_operand (Var output) t = SOME (n2w d)` by
       (first_assum irule >> simp[]) >>
     `eval_operand (Var source) t = SOME (n2w B)` by
       (first_assum irule >> simp[]) >>
     fs[eval_operand_def]) >>
  `tf.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d+32}` by
    gvs[w2n_n2w, LESS_MOD] >>
  qexistsl [`t`,`H'`,`tf`] >> simp[allocas_from_def] >>
  conj_tac >-
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  conj_tac >-
    (irule abi_decode_ptr_window_frame >> qexistsl [`G`,`s`,`tn`] >>
     simp[w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  conj_tac >-
    (`val_wf tv v /\ type_memory_size tv = 32` by
       fs[abi_decoder_metadata_def, value_has_type_val_wf] >>
     `val_footprint tv v <= 32` by metis_tac[val_footprint_le] >>
     `val_in_memory tv v d t.vs_memory` by fs[abi_valid_allocated_post_def] >>
     rpt strip_tac >> irule clean_footprint_val_in_memory_robust >>
     simp[] >> qexistsl [`t.vs_memory`,`tn.t_mem DIFF {i | d <= i /\ i < d+32}`] >>
     simp[] >> decide_tac) >>
  conj_tac >-
    (`gas_origin_ptr_path (ARB,lo,K F,ctx,func,PG) (s,G,tn) [] (OK t,H',tf)` by simp[] >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  fs[allocas_from_def]
QED
