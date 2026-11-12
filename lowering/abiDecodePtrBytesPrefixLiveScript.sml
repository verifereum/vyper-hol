Theory abiDecodePtrBytesPrefixLive
Ancestors
  abiDecoderBytesBound abiDecoderGuard abiEncoder placeMemoryCodeLayout
  compileEnv emitHelper freshWrites arithmetic pred_set

(* These are the five straight-line phases preceding the bytes runtime tail.
   Protect every entry variable, including ones absent from the runtime map. *)
Theorem abi_decode_bytes_prefix_protected:
  abi_decode_bytes_head pos hi sa = (head,c1) /\
  compile_abi_dec_addr (Var src) pos c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (cnt,c3) /\
  abi_decode_le_guard cnt (Lit (n2w n)) c3 = ((),c4) /\
  abi_decode_bytes_payload_guard head cnt hi c4 = ((),c5) /\
  hi <> Lit 0w ==>
  (!x. not_fresh_at sa x ==> not_fresh_at c1 x) /\
  (!x. not_fresh_at c1 x ==> not_fresh_at c3 x) /\
  (!x. not_fresh_at c3 x ==> not_fresh_at c4 x) /\
  (!x. not_fresh_at c4 x ==> not_fresh_at c5 x)
Proof
  strip_tac >>
  gvs[abi_decode_bytes_head_def, abi_decode_bytes_payload_guard_def,
       abi_decode_le_guard_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_next_var >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
  rpt conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
  goal_assum (drule_at Any) >> decide_tac
QED
