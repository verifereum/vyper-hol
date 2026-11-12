(* Containing-block PHI facts need a nonempty prefix, not just zero PHIs. *)
Theory entryContainingExitPhi
Ancestors
  abiEncoderExitPhi abiDecoderPhi fragExec compileEnv venomExecSemantics
  moduleLowering stmtLowering emitHelper compilerFirstEmission

Theorem entry_containing_nonempty_exit_phi:
  fn_has_code first last fn /\ last.cs_current_insts <> [] /\
  phi_prefix_length last.cs_current_insts = 0 ==>
  !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [fn_has_code_def] >> rpt strip_tac >> gvs[] >>
  irule abi_encoder_nonempty_prefix_phi >>
  qexists_tac `last.cs_current_insts` >> simp[]
QED

Theorem entry_decoder_nonempty_containing_exit_phi:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi info first = ((),last) /\
  abi_decode_source_opcode opc /\ fn_has_code first last fn /\
  last.cs_current_insts <> [] ==>
  first.cs_blocks = last.cs_blocks \/
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule_all abi_decoder_to_buf_exit_phi >> strip_tac >> simp[] >>
  metis_tac[entry_containing_nonempty_exit_phi]
QED

Theorem entry_guarded_empty_body_emission:
  compile_guarded_body ce F nk ut iv [] rt first = ((),last) /\
  ~block_is_terminated first ==>
  ?opc. (opc = STOP \/ opc = INVALID) /\ emit_inst opc [] [] first = ((),last)
Proof
  Cases_on `rt` >>
  simp[compile_guarded_body_def, compile_stmt_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, comp_get_def] >>
  strip_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  metis_tac[]
QED
