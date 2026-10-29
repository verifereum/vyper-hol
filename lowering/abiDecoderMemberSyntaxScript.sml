(* Derive a recursive member's endpoint PHI condition from its actual successor.
   TOP-LEVEL: abi_decoder_member_exit_phi.
   Helper: a completed-block equality propagates through compiler extensions. *)
Theory abiDecoderMemberSyntax
Ancestors
  abiDecoderMemberCode abiDecoderMemberSetup abiDecoderLoopCode abiDecoderPhi
  abiDecoderAppend abiDecoderContract fragExec compileEnv venomExecSemantics venomInst
  list rich_list arithmetic

Theorem abi_decoder_extension_blocks_middle:
  cs_extends start middle /\ cs_extends middle final /\
  start.cs_blocks = final.cs_blocks ==>
  middle.cs_blocks = final.cs_blocks
Proof
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  rename1 `middle.cs_blocks = prefix ++ start.cs_blocks` >>
  rename1 `final.cs_blocks = suffix ++ middle.cs_blocks` >>
  `LENGTH prefix = 0 /\ LENGTH suffix = 0` by
    (qpat_assum `start.cs_blocks = final.cs_blocks` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
     qpat_assum `final.cs_blocks = suffix ++ middle.cs_blocks` (fn fin =>
       qpat_assum `middle.cs_blocks = prefix ++ start.cs_blocks` (fn mid =>
         pure_rewrite_tac [fin, mid, LENGTH_APPEND])) >> decide_tac) >>
  gvs[LENGTH_NIL]
QED

Theorem abi_decoder_member_exit_phi:
  compile_abi_decode_to_buf childdst childsrc opc hi di middle = ((),end_st) /\
  abi_decode_member_setup dst src opc hi dyn ao vo end_st = (ops,next_st) /\
  cs_extends next_st final /\ fn_has_code next_st final func /\
  abi_decode_source_opcode opc ==>
  middle.cs_blocks = end_st.cs_blocks \/
  !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_decoder_to_buf_exit_phi >> strip_tac >>
  Cases_on `middle.cs_blocks = end_st.cs_blocks` >- simp[] >>
  `phi_prefix_length end_st.cs_current_insts = 0` by metis_tac[] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_code_entry_prefix >> strip_tac >>
  asm_simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  Cases_on `end_st.cs_current_insts` >>
  gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def] >>
  rename1 `inst.inst_opcode = PHI` >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED
