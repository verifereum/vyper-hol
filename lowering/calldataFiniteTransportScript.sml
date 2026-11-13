(* Finite decoder fragments: safe run transport and unchanged allocator fields. *)
Theory calldataFiniteTransport
Ancestors
  fragExecMem allocaFrontierBound venomMemDefs

Theorem calldata_finite_fragment_run:
  frag_exec_mem ctx st last (\s. s = initial) Q
    (\r. ?z. r = Abort Revert_abort z) /\
  fn_has_code st last fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial))
Proof
  simp_tac bool_ss [frag_exec_mem_def] >> strip_tac >>
  first_x_assum (qspec_then `fn` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem calldata_alloca_inv_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_inv s ==> alloca_inv t
Proof
  strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem calldata_alloca_frontier_inv_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_frontier_inv ctx fn site s ==> alloca_frontier_inv ctx fn site t
Proof
  simp[alloca_frontier_inv_def, allocaBudgetPropsTheory.remaining_alloca_budget_def]
QED
