(* Transport only the completed encoder simulation, not intermediate room. *)
Theory exprSimAbiEncodeRelabelContext
Ancestors
  exprSimAbiEncodeSourceRoom exprSimAbiEncodeWindowRoom

Theorem abi_encode_completed_sim_context:
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  abi_decode_sim (ctx with ctx_functions := [obs]) obs s t ==>
  abi_decode_sim ctx obs s t
Proof
  metis_tac[abi_decode_sim_ctx_no_invoke]
QED
