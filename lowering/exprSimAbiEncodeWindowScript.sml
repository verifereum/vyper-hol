(* Actual allocation-site interface probe for the expression ABI suffix. *)
Theory exprSimAbiEncodeWindow
Ancestors
  abiEncoderWindowRun abiEncoderWindowContract abiEncodeWindowBuiltin abiEncoder

Theorem abi_encode_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d initial ==>
  ?actual. window_strong_result ctx func st st' out at av d initial actual
Proof
  strip_tac >> drule_all compile_abi_encode_to_buf_window_strong_run >> simp[]
QED
