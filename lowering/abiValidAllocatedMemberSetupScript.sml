(* Allocation-backed member navigation changes only SSA variables. *)
Theory abiValidAllocatedMemberSetup
Ancestors
  abiValidAllocatedContract abiMalformedMemberSetup abiMalformedTraversal
  abiDecoderMemberSetup compileEnv venomState valueEncodingProofs valueEncoding
  abiMalformedRecursiveInterface

Theorem abi_valid_allocated_member_setup_frame:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  abi_valid_allocated_frame sites d n s t /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  drule abi_malformed_member_setup_instructions >> strip_tac >>
  drule_all abi_malformed_setup_sequence_frame >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  simp[abi_valid_allocated_frame_def]
QED

(* Completed members remain typed while a disjoint child subrange is decoded. *)
Theorem abi_valid_allocated_members_kept:
  abi_valid_allocated_frame sites d n s t /\ alloca_inv s /\
  abi_malformed_destination func cenv scopes dstid q (type_memory_size_list tvs) s /\
  dstid NOTIN sites /\ (q + type_memory_size_list tvs <= d \/ d+n <= q) /\
  tuple_in_memory vs tvs q s.vs_memory /\ tuple_val_wf vs tvs ==>
  tuple_in_memory vs tvs q t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at q (type_memory_size_list tvs) t.vs_memory =
    mem_bytes_at q (type_memory_size_list tvs) s.vs_memory` by
    (irule abi_valid_allocated_frame_sibling >> metis_tac[]) >>
  irule (cj 5 val_in_memory_mem_agree_proof) >>
  metis_tac[]
QED
