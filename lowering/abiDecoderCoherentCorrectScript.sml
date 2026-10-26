(* Recursive decoder correctness for all coherent value types.
   Checked caller establishment of coherence and resource bounds is separate. *)
Theory abiDecoderCoherentCorrect
Ancestors
  abiDecoderCoherence abiDecoderCorrect abiDecoderCorrectLeaves abiDecoderCorrectArray
  abiDecoderCorrectFixed abiDecoderCorrectTuple abiDecoderCorrectStruct compileEnv list

Theorem abi_decoder_coherent_correct:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_decoder_correct ce env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[abi_decoder_correct_base]
  >- simp[abi_decoder_correct_flag]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      FIRST [irule abi_decoder_correct_array, irule abi_decoder_correct_fixed_array] >> simp[])
  >- (rpt strip_tac >> irule abi_decoder_correct_tuple >> simp[]) >>
  rpt strip_tac >> irule abi_decoder_correct_struct >> asm_simp_tac bool_ss []
QED

(* TOP-LEVEL: actual execution, with no recursive correctness hypothesis. *)
Theorem abi_decoder_decode:
  compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    start last src dst opc hi sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory tv v d t.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_correct ce env sf ty tv` by
    (irule abi_decoder_coherent_correct >> fs[abi_decoder_recursive_pre_def]) >>
  mp_tac abi_decoder_correct_run >> asm_simp_tac bool_ss []
QED
