(* Internal nonempty block heads determine observer-function PHI prefixes.
   Empty final blocks still need the explicit endpoint premise. *)
Theory exprSimAbiDecodePhiBoundary
Ancestors
  abiDecoderPhi fragExec venomExecSemantics compileEnv list rich_list

Theorem abi_decode_nonempty_prefix_phi:
  isPREFIX xs ys /\ xs <> [] /\ phi_prefix_length xs = 0 ==>
  phi_prefix_length ys = 0
Proof
  Cases_on `xs` >> simp[] >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

Theorem abi_decode_observer_exit_phi:
  fn_has_code st last fn /\
  (st.cs_blocks = last.cs_blocks \/
   (last.cs_current_insts <> [] /\ phi_prefix_length last.cs_current_insts = 0)) ==>
  st.cs_blocks = last.cs_blocks \/
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  rw[fn_has_code_def] >> gvs[] >>
  disj2_tac >> irule abi_decode_nonempty_prefix_phi >> metis_tac[]
QED

Theorem abi_decode_to_buf_nonempty_observer_phi:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),last) /\
  abi_decode_source_opcode opc /\ fn_has_code st last fn /\
  last.cs_current_insts <> [] ==>
  st.cs_blocks = last.cs_blocks \/
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule_all abi_decoder_to_buf_exit_phi >> strip_tac >>
  irule abi_decode_observer_exit_phi >> simp[]
QED
