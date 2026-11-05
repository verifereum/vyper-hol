(* Preserve actual read windows across the builtin setup's selector store. *)
Theory exprSimAbiEncodeOpenSetup
Ancestors
  abiEncodeWindowBuiltin abiBuiltinEncodeSetup abiEncoderWindow abiDecoderContract

Theorem abi_encode_setup_frame_window_input:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_input_bytewise >>
  qexists_tac `s.vs_memory` >> simp[] >> rpt strip_tac >>
  gvs[abi_builtin_encode_setup_frame_def, abi_decode_frame_def] >>
  first_x_assum irule >> decide_tac
QED
