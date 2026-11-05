(* Exact arbitrary-byte observation, independent of ABI acceptance. *)
Theory abiDecoderRejectResources
Ancestors
  abiDecoderFrame venomState words list arithmetic

Definition abi_reject_input_def:
  abi_reject_input src hi sb bs fp s <=>
    eval_operand src s = SOME (n2w sb) /\
    eval_operand hi s = SOME (n2w (sb + LENGTH bs)) /\
    hi <> Lit 0w /\ sb + LENGTH bs < dimword(:256) /\
    mem_bytes_at sb (LENGTH bs) s.vs_memory = bs /\
    abi_footprint_disjoint sb (LENGTH bs) fp
End

Theorem abi_reject_input_preserved:
  abi_reject_input src hi sb bs fp s /\
  abi_decode_footprint_frame fp s t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  abi_reject_input src hi sb bs fp t
Proof
  rw[abi_reject_input_def] >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

Theorem abi_reject_count_preserved:
  abi_reject_input src hi sb bs fp s /\ 32 <= LENGTH bs /\
  abi_decode_footprint_frame fp s t ==>
  mload sb t = mload sb s
Proof
  rpt strip_tac >> irule abi_decode_footprint_frame_mload >>
  qexists_tac `fp` >> simp[] >>
  gvs[abi_reject_input_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED
