(* The real array initializer and finite loop compose under physical ownership. *)
Theory abiScratchDecoderArrayExecute
Ancestors
  abiScratchDecoderContract abiScratchDecoderArrayInit abiScratchDecoderLoopInput
  abiScratchDecoderLoopEntry abiScratchEncoderContract abiScratchEffect abiDecoderRecursiveArray
  abiDecoderCoherence abiDecoderTypedContract abiDecoderAllocation abiDecoderContract
  abiDecoderLoop abiDecoderReentry abiDecodeRanges abiEncoder fragExec compileEnv valueEncoding
  vyperABI vyperValue venomState words list arithmetic

Theorem abi_scratch_decoder_array_execute:
  compile_abi_decode_to_buf dst src opc hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  abi_scratch_decoder ce env sf ty tv /\ fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi_op sb d first last b cap initial /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_st.cs_next_id <= last /\
    first <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < last` by decide_tac >>
  drule_all abi_scratch_decoder_array_initialize >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`st` |-> `loop_st`, `initial` |-> `prepared:venom_state`,
    `site` |-> `loop_st.cs_next_id-2`, `ip` |-> `FST (setup:operand # operand)`,
    `hi` |-> `hi_op:operand`] abi_scratch_decoder_loop_input) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `ip` |-> `FST (setup:operand # operand)`, `cnt` |-> `SND (setup:operand # operand)`,
    `next` |-> `loop_st.cs_next_var`, `start` |-> `loop_st:compile_state`,
    `initial` |-> `prepared:venom_state`, `site` |-> `loop_st.cs_next_id-2`]
    abi_scratch_decoder_loop_from_state) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared t` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `final.cs_next_id`, `st.cs_next_id`,
       `loop_st.cs_next_var`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `st.cs_next_id`,
       `st.cs_next_var`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
