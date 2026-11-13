(* Allocation-site absence is a fold invariant, not a consequence of history. *)
Theory entryFutureAllocation
Ancestors
  calldataMemberResourceFrame venomState finite_map arithmetic

Theorem entry_singleton_future_absent:
  (!id. old < id /\ id < hi ==> FLOOKUP initial.vs_allocas id = NONE) /\
  old < lo /\
  (!id. id <> old ==>
    FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) ==>
  !id. lo <= id /\ id < hi ==> FLOOKUP ready.vs_allocas id = NONE
Proof
  rpt strip_tac >>
  `old < id /\ id <> old` by decide_tac >> metis_tac[]
QED

Theorem entry_absent_member_ownership:
  (!id. lo <= id /\ id < hi ==> FLOOKUP s.vs_allocas id = NONE) ==>
  calldata_member_own fn lo hi s
Proof
  simp[calldata_member_own_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem entry_empty_future_allocations:
  s.vs_allocas = FEMPTY ==>
  !id. cutoff <= id ==> FLOOKUP s.vs_allocas id = NONE
Proof
  simp[]
QED

Theorem entry_future_allocations_frame:
  (!id. cutoff <= id ==> FLOOKUP s.vs_allocas id = NONE) /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  hi <= next /\ cutoff <= next ==>
  !id. next <= id ==> FLOOKUP t.vs_allocas id = NONE
Proof
  rpt strip_tac >> `hi <= id /\ cutoff <= id` by decide_tac >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry future allocation inherited admission"
  end) [entry_singleton_future_absent, entry_absent_member_ownership,
        entry_empty_future_allocations, entry_future_allocations_frame];
