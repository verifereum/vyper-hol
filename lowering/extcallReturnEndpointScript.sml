(* Endpoint embedding facts for the return-path continuations. *)
Theory extcallReturnEndpoint
Ancestors
  fragExec compileEnv venomExecSemantics venomInst list

(* A no-default return contributes no code after the decoder. *)
Theorem return_endpoint_return:
  comp_return result en = (result',sb) /\
  (sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
  en = sb /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  simp[comp_return_def] >> metis_tac[]
QED

(* The default path seals its decoder endpoint with a JMP before the exit. *)
Theorem return_endpoint_jump:
  emit_inst JMP [Label exit_lbl] [] en = (x,mid) /\
  new_block exit_lbl mid = (y,sb) /\
  cs_extends start en /\ cs_extends sb end_st /\
  fn_has_code start end_st func ==>
  en.cs_current_insts <> [] \/
  !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `en.cs_current_insts <> []` >> simp[] >>
  drule_all fn_has_code_emit_new_block >> strip_tac >>
  rpt strip_tac >> gvs[get_instruction_def] >>
  Cases_on `bb.bb_instructions` >>
  gvs[get_instruction_def, phi_prefix_length_def, mk_inst_def]
QED
