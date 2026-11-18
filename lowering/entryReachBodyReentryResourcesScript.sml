(* Actual index-counter readiness from partial allocation history. *)
Theory entryReachBodyReentryResources
Ancestors
  actualAllocExec abiAllocationHistory venomMemDefs allocaFrontierBound
  allocaBudgetProps finite_map words arithmetic list

Theorem entry_index_counter_readiness:
  abi_decode_index_init first = (ip,last) /\
  (!i. MEM i (emitted_insts first last) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ abi_alloca_history (fn_insts fn) s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?p. (FLOOKUP s.vs_allocas first.cs_next_id = NONE /\
        p = s.vs_alloca_next /\ p+32 < dimword (:256)) \/
      (FLOOKUP s.vs_allocas first.cs_next_id = SOME (p,32) /\
        p < dimword (:256) /\ p+32 <= s.vs_alloca_next)
Proof
  strip_tac >> drule actual_index_init_literal_site >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  Cases_on `FLOOKUP s.vs_allocas first.cs_next_id`
  >- (`FLOOKUP s.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `s.vs_alloca_next` >> simp[]) >>
  PairCases_on `x` >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (x0,x1)` by metis_tac[] >>
  drule_all abi_alloca_history_function_size >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> strip_tac >> gvs[] >>
  `x0+32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  fs[alloca_frontier_inv_def, dimword_def,
     fcpLib.INDEX_CONV ``dimindex (:256)``] >> decide_tac
QED

Theorem entry_index_counter_owner_separation:
  alloca_inv s /\ FLOOKUP s.vs_allocas oid = SOME (d,capacity) /\
  oid <> aid /\ sz <= capacity /\
  ((FLOOKUP s.vs_allocas aid = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas aid = SOME (p,32)) ==>
  d+sz <= p \/ p+32 <= d
Proof
  strip_tac
  >- (fs[alloca_inv_def, alloca_next_valid_def] >>
      `d+capacity <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  fs[alloca_inv_def, allocas_non_overlapping_def] >>
  `d+capacity <= p \/ p+32 <= d` by metis_tac[] >> decide_tac
QED
