(* TOP-LEVEL: allocation sequences preserve compatible pending requests.
   Word-sized counter requests remain valid across fresh and cached slots. *)
Theory abiAllocationRequests
Ancestors
  abiAllocationSequence abiAllocationFrame memoryValueSnapshot compileEnv venomState list pair arithmetic

Theorem abi_allocation_sequence_request:
  !allocations ss id byte_count.
    abi_alloca_request_ok id byte_count ss /\ EVERY (\allocation. byte_count <= SND allocation) allocations ==>
    abi_alloca_request_ok id byte_count (abi_allocation_sequence allocations ss)
Proof
  Induct_on `allocations` >- simp[] >> qx_gen_tac `allocation` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, abi_allocation_sequence_cons] >> strip_tac >>
  first_x_assum irule >> simp[] >> irule abi_allocation_frame_request >> simp[]
QED

Theorem abi_allocation_sequence_word_requests:
  !allocations requests ss.
    EVERY (\allocation. SND allocation = 32) allocations /\ EVERY (\request. SND request = 32) requests /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) ss) requests ==>
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) (abi_allocation_sequence allocations ss)) requests
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `request` >> DISCH_TAC >>
  `abi_alloca_request_ok (FST request) (SND request) ss /\ SND request = 32` by fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`allocations`, `ss`, `FST (request:num # num)`, `SND (request:num # num)`] abi_allocation_sequence_request) >>
  impl_tac >- fs[EVERY_MEM] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed pending allocation request preservation: " ^ name)
  end) (DB.thms "abiAllocationRequests")
