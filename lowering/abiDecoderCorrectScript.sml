(* The recursive execution claim consumed as a child induction hypothesis.
   Defining this contract does not establish correctness for every type. *)
Theory abiDecoderCorrect
Ancestors
  abiDecoderEffect abiDecoderCoherence abiDecoderReentry abiDecoderLoop
  abiDecoderAllocation fragExec abiEncoder compileEnv valueEncoding
  venomState venomExecSemantics words list

Definition abi_sites_decoder_correct_def:
  abi_sites_decoder_correct sites ce env sf ty tv <=>
    !dst src opc base_op hi start end_st func ctx first last b cap limit_st initial av v src_base sb d.
    compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    (base_op = Lit 0w \/ opc = MLOAD) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      start last src dst opc base_op hi src_base sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
    abi_sites_decoder_budget sites first last b cap initial /\
    first <= abi_decoder_entry_floor start /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?t. val_in_memory tv v d t.vs_memory /\
      abi_sites_decoder_effect sites first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial t /\
      t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      ~t.vs_halted /\ abi_decode_sim ctx func initial t
End

Overload abi_decoder_correct = “abi_sites_decoder_correct UNIV”

Theorem abi_decoder_correct_def:
  abi_decoder_correct ce env sf ty tv <=>
    !dst src opc base_op hi start end_st func ctx first last b cap limit_st initial av v src_base sb d.
    compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    (base_op = Lit 0w \/ opc = MLOAD) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      start last src dst opc base_op hi src_base sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
    abi_decoder_budget first last b cap initial /\
    first <= abi_decoder_entry_floor start /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?t. val_in_memory tv v d t.vs_memory /\
      abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial t /\
      t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  rewrite_tac[abi_sites_decoder_correct_def]
QED

Theorem abi_decoder_correct_run:
  abi_decoder_correct ce env sf ty tv /\
  compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    start last src dst opc base_op hi src_base sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor start /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory tv v d t.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >> qpat_x_assum `abi_decoder_correct _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_correct_def]) >>
  disch_then drule >> asm_simp_tac bool_ss [] >>
  disch_then (drule_at Any) >> asm_simp_tac bool_ss [] >> metis_tac[]
QED

(* Helper: an unconditional PHI-free endpoint suffices for every decoder. *)
Theorem abi_decoder_correct_run_simple:
  abi_decoder_correct ce env sf ty tv /\
  compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  fn_has_code start end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    start last src dst opc base_op hi src_base sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor start /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. val_in_memory tv v d t.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >> mp_tac abi_decoder_correct_run >> asm_simp_tac bool_ss []
QED
