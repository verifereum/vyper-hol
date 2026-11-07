Theory exprSimAbiEncodeFramedBody
Ancestors
  exprSimAbiEncodeFramedLeaves exprSimAbiEncodeFramedArray
  exprSimAbiEncodeFramedComplex exprSimAbiEncodeExecFrame compileEnv

Theorem abi_encode_framed_contract_all:
  !ei. abi_encode_framed_contract ei
Proof
  Induct
  >- simp[abi_encode_framed_word_contract]
  >- simp[abi_encode_framed_bytes_contract]
  >- simp[abi_encode_framed_copy_contract]
  >- (rpt gen_tac >> irule abi_encode_framed_array_contract >> simp[]) >>
  irule abi_encode_framed_complex_contract >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `(ei,az,ms,dyn)` >> simp[]
QED

Theorem compile_abi_encode_to_buf_framed_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  metis_tac[abi_encode_framed_contract_all, abi_encode_framed_contract_def]
QED
