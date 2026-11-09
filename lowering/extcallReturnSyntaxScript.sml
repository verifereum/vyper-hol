(* Compiler-only closure facts for counted return decoding. *)
Theory extcallReturnSyntax
Ancestors
  extcallReturnDecoderCode abiDecoderVarSequence exprSimAbiGasBridge
  exprLoweringProps compileEnv venomInst list

Theorem return_decoder_ops_free:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) ==>
  frag_ops_free st en
Proof
  strip_tac >> drule return_decoder_frag_code >>
  simp[frag_ops_free_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[abi_decoder_reentry_opcode_def] >>
  strip_tac >> gvs[]
QED
