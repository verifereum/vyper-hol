(* TOP-LEVEL: compose Log frames across its real output allocation and
   encoder. Every allocation older than the new output remains readable. *)
Theory abiLogAllocationFrame
Ancestors
  abiStateFrame abiAllocatedWindows compileEnv venomState list arithmetic

Theorem abi_log_allocation_state_frame:
  !before middle after.
    abi_state_frame before middle /\ abi_state_frame middle (after with vs_logs := middle.vs_logs) ==>
    abi_state_frame before (after with vs_logs := before.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`before`, `middle`] abi_state_frame_observables) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  irule abi_state_frame_trans >> qexists_tac `middle` >> fs[]
QED

Theorem abi_log_allocation_reads:
  !before middle after old_id next_id.
    old_id < next_id /\ middle.vs_memory = before.vs_memory /\
    (!id offset count. abi_allocated_window before id offset count ==> abi_allocated_window middle id offset count) /\
    (!id offset count. id < next_id /\ id <> old_id /\ abi_allocated_window middle id offset count ==>
      read_memory offset count after = read_memory offset count middle) ==>
    !id offset count. id < old_id /\ abi_allocated_window before id offset count ==>
      read_memory offset count after = read_memory offset count before
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `read_memory read_offset read_len after = read_memory read_offset read_len before` >>
  rename1 `abi_allocated_window before read_id read_offset read_len` >>
  `read_id < next_id /\ read_id <> old_id` by decide_tac >>
  `abi_allocated_window middle read_id read_offset read_len` by
    (qpat_x_assum `!id offset count. abi_allocated_window before _ _ _ ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!id offset count. _ ==> read_memory offset count after = _`
    (qspecl_then [`read_id`, `read_offset`, `read_len`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation and Log caller frames: " ^ name)
  end) (DB.thms "abiLogAllocationFrame")
