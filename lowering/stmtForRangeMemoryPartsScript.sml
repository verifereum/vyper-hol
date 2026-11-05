(* Memory boundary for the range loop's variable store. *)
Theory stmtForRangeMemoryParts
Ancestors
  instMemFrontier bodyMemoryDefs stmtSimForRounds exprLoweringProps
  venomMemDefs venomExecSemantics

Theorem for_range_allocated_store_below:
  !s aid b sz dst v iid outs.
    alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
    32 <= sz /\ eval_operand dst s = SOME (n2w b) /\
    b < dimword (:256) ==>
    inst_mem_below_frontier (mk_inst iid MSTORE [dst; v] outs) s
Proof
  rpt strip_tac >> simp[below_frontier_MSTORE] >>
  rpt strip_tac >> gvs[] >>
  irule alloca_region_below_frontier >>
  conj_tac >- fs[alloca_inv_def] >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[]
QED
