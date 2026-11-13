(* Dynamic preparation exposes logical input and resources independently. *)
Theory abiTupleEncodeOpenDynamic
Ancestors
  abiTupleEncodeOpenPrepare abiTupleEncodeOpenAssembly abiTupleEncodePrepare
  abiTupleEncodeOpenInput abiTupleEncodeLayout abiBuiltinEncodeResources
  abiBuiltinEncodeInput abiBuiltinAllocation abiEncoderOpenInput abiEncoderInput
  abiTupleProps abiDecoderReentry abiDecoderContract compileEnv exprLowering
  venomState venomExecSemantics words list arithmetic finite_map
  abiDecoderFootprint abiDecoderAllocation abiScratchBuiltinSource

Theorem abi_tuple_encode_open_dynamic_prepare:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  abi_tuple_encode_open_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  abi_tuple_encode_layout ce xs ats /\ any_dynamic ats /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap
    (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_encoder_open_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
      (Tuple ats) (ListV avs) sb (abi_tuple_bytes ce xs) actual.vs_memory /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_decoder_operand_live staged.cs_next_var source_buf.buf_operand /\
    LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
    abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  drule_all abi_tuple_encode_open_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_tuple_encode_open_dynamic_input >> strip_tac >>
  `abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual` by
    (mp_tac (Q.INST [`st` |-> `staged`, `ready` |-> `staged`,
      `source_cap` |-> `abi_tuple_bytes ce (xs:(operand # type) list)`,
      `s` |-> `abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce (xs:(operand # type) list)) initial`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_resources_transport) >>
     impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_budget_window_disjoint[local]:
  abi_decoder_budget first last b cap s /\ (p+n <= b \/ b+cap <= p) ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
Proof
  strip_tac >> drule abi_decoder_budget_frontier >> strip_tac >>
  irule abi_decoder_child_scratch_disjoint >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  first_x_assum drule_all >> strip_tac >> decide_tac
QED

Theorem abi_tuple_encode_open_resources_scratch:
  abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap s ==>
  let outsz = 32+32*word_size (maxlen+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4)) in
  let allocated = abi_builtin_allocate_state st.cs_next_id outsz s in
  abi_footprint_disjoint sb source_cap (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  abi_footprint_disjoint p outsz (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  (sb+source_cap <= p+32 \/ p+32+(case method_id_opt of NONE => 0 | SOME _ => 32) <= sb)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  simp_tac bool_ss [abi_builtin_encode_resources_def, LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac >- (irule abi_encode_budget_window_disjoint >> goal_assum (drule_at Any) >> asm_simp_tac bool_ss []) >>
  conj_tac >- (irule abi_encode_budget_window_disjoint >> goal_assum (drule_at Any) >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_builtin_store_separate >> goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
  qexists_tac `maxlen` >> asm_simp_tac bool_ss []
QED
