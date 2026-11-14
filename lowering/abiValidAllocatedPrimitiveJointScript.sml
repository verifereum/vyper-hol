(* Source value, resources and pointer safety on one primitive decode run. *)
Theory abiValidAllocatedPrimitiveJoint
Ancestors
  abiValidAllocatedLeaves abiValidAllocatedContract abiValidDecodedMetadata
  abiDecodePtrWordJoint abiDecodePtrMemberFrame abiMalformedRecursiveInterface
  abiDecoderTypedContract abiDecoderWordTyped abiDecoderReentry abiDecoderCoherence
  abiDecoderClampedWord abiDecoderContract entryDecoderHistoryFrame
  abiDecoderReentryPointer abiValidAllocatedObservations ctorAbiActualWorld
  exprPtrCleanBufferPost valueEncodingTyping valueEncodingDefs
  loweringStateRelDefs exprLoweringProps bodyPtrDefs ptrDiscipline compileEnv
  venomState venomMemDefs venomExecSemantics finite_map words list arithmetic

Theorem abi_valid_allocated_primitive_joint_observations:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_taint tn pos = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    abi_decode_ptr_window G' tn' t output (n2w d) 32 /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(d <= i /\ i < d+32) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s.vs_alloca_next = t.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all abi_valid_allocated_primitive_run >> strip_tac >>
  drule_all abi_valid_allocated_primitive_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
     (DecPrimWord clamp) st = ((),en)` by metis_tac[] >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all abi_malformed_allocated_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `B+L < dimword(:256)` by fs[abi_malformed_allocated_window_def] >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      not_fresh_at_def] >>
  `lookup_var output s = SOME (n2w d)` by fs[eval_operand_def] >>
  `p+32 <= L` by
    (drule abi_decoder_primitive_cases >>
     disch_then (qspec_then `clamp` mp_tac) >> simp[] >> strip_tac >>
     drule abi_decoder_coherent_header >> strip_tac >>
     fs[abi_decoder_header_def]) >>
  `B < dimword(:256) /\ d < dimword(:256)` by decide_tac >>
  fs[] >>
  `(t with vs_inst_idx := s.vs_inst_idx) with
      vs_inst_idx := LENGTH en.cs_current_insts = t` by
    (simp[venom_state_component_equality] >> fs[abi_valid_allocated_post_def]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by
    fs[EVERY_MEM] >>
  `t.vs_inst_idx = LENGTH en.cs_current_insts` by
    fs[abi_valid_allocated_post_def] >>
  `alloca_history func t` by
    (drule_all entry_straight_line_alloca_history >> fs[]) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord clamp) _ = _`
    (mp_then Any
      (qspecl_then [`tn`, `t`, `s`, `p`, `lo`, `func`, `d`, `ctx`,
         `PG`, `L`, `G`, `B`] mp_tac)
      (abi_decode_word_success_joint |>
      Q.INST [`d` |-> `destination_word`] |>
      Q.INST [`b` |-> `n2w B`, `h` |-> `L`, `destination_word` |-> `n2w d`,
        `u` |-> `t with vs_inst_idx := s.vs_inst_idx`, `s` |-> `s`])) >>
  (impl_tac >- (simp[w2n_n2w] >> metis_tac[])) >>
  strip_tac >>
  `d < dimword(:256)` by decide_tac >>
  `abi_decode_ptr_window G' tn' t output (n2w d) 32 /\
   abi_decode_ptr_window G' tn' t source (n2w B) L` by
    gvs[abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def] >>
  `val_wf tv v /\ type_memory_size tv = 32` by
    fs[abi_decoder_metadata_def, value_has_type_val_wf] >>
  `val_in_memory tv v d t.vs_memory` by
    fs[abi_valid_allocated_post_def] >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
     val_in_memory tv v d mem` by
    (rpt strip_tac >> irule clean_window_value_robust >>
     (conj_tac >- fs[abi_valid_allocated_post_def]) >>
     goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
     qexists_tac `32` >> fs[abi_decode_ptr_window_def]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, allocas_from_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_primitive_joint:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_taint tn pos = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    abi_decode_ptr_window G' tn' t output (n2w d) 32 /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(d <= i /\ i < d+32) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >> drule_all abi_valid_allocated_primitive_joint_observations >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[]
QED
