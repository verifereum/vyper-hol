(* Actual initialized loop entry from the typed primitive-array precondition. *)
Theory abiDecoderPrimitiveArrayInit
Ancestors
  abiDecoderArrayInit abiDecoderPrimitiveArrayFacts abiDecoderArrayLoopInit
  abiDecoderPrimitiveLoopContext abiDecoderArrayInvariant abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderLoop abiDecoderContract abiDecoderFrame
  abiDecoderAllocation fragExec exprLoweringProps emitHelperProps compileEnv valueEncoding
  venomState words list arithmetic
Libs
  Omega

Theorem abi_decoder_primitive_array_pre_ranges:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  fresh_vars_wrt st initial /\ (d + 32 <= b \/ b + cap <= d)
Proof
  strip_tac >> drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [] >> Omega.OMEGA_TAC
QED

Theorem abi_decoder_primitive_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\
  loop_st.cs_next_id <= end_st.cs_next_id /\ loop_st.cs_next_var <= end_st.cs_next_var /\
  fn_has_code st loop_st fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot
      [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] /\
    abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared /\
    fresh_vars_wrt loop_st prepared /\ fresh_vars_wrt end_st prepared /\
    ~prepared.vs_halted /\ mload slot prepared = 0w /\
    prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    b <= slot /\ slot + 32 <= b + cap /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap prepared /\
    (!op w. eval_operand op initial = SOME w ==> eval_operand op prepared = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial prepared /\
    abi_decode_sim ctx fn initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`first` |-> `st.cs_next_id`] abi_decode_array_loop_init_from_state)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx fn initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  `!op w. eval_operand op initial = SOME w ==> eval_operand op prepared = SOME w` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  drule_all abi_decoder_array_init_memory >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d)`
    by metis_tac[] >>
  `abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared` by
    (simp_tac bool_ss [abi_decoder_loop_inputs_def] >>
     metis_tac[abi_decoder_operand_live_fresh]) >>
  `fresh_vars_wrt end_st prepared` by
    (mp_tac (Q.SPECL [`loop_st`, `end_st`, `prepared`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  qexistsl_tac [`prepared`, `slot`] >> gvs[Excl "enc_def"]
QED
