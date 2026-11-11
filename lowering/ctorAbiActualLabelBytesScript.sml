Theory ctorAbiActualLabelBytes
Ancestors
  ctorAbiActualObservations ctorAbiActualBytes ctorAbiActualNarrowWord
  abiDecoderVarSequence abiDecoderBytesTyped abiDecoderBytesFrame abiDecoderLoop
  abiDecoderContract abiDecoderReentryPointer abiDecoderReentry
  abiEncoderRegisteredEffect abiEncoderProps allocaFrontierBound allocaBudgetProps
  fragExec instIdxIndep venomState venomExecSemantics venomInst
  compileEnv valueEncoding words list arithmetic finite_map venomMemDefs

Theorem ctor_actual_bytestring_labels_fragment:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  type_memory_bytes ce ty < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section =
    enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      abi_decode_frame d (type_memory_bytes ce ty) initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial t /\
      (alloca_inv t <=> alloca_inv initial) /\
      (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial) /\
      t.vs_labels = initial.vs_labels) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all ctor_actual_bytestring_ceiling_sequence >> strip_tac >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  qexists `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
    abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
    remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem ctor_actual_bytestring_labels_run:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
  ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,type_memory_bytes ce ty)] initial actual /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
    fresh_vars_wrt limit_st actual /\ actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\ actual.vs_labels = initial.vs_labels
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all ctor_actual_bytestring_labels_fragment >>
  disch_then (qspecl_then [`site`, `func`, `ctx`] assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
    [(d,type_memory_bytes ce ty)] initial actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,type_memory_bytes ce ty)]`] >> simp[]) >>
  `ctor_actual_scratch func ids D N actual` by
    (drule ctor_actual_scratch_same_allocas >> simp[]) >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def]
QED
