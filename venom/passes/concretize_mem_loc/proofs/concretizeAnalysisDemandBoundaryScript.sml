Theory concretizeAnalysisDemandBoundary
Ancestors
  finiteByteDemand frameJointDemand concretizeAnalysisSafeKill
  o1PassContract ptrDiscipline frameOriginHistory basePtrDefs
  venomExecSemantics venomInst venomWf concretizeMemLocDefs
  pred_set finite_map list arithmetic

(* R and writes are projections of occurrences/edges supplied by consumers.
   No projection theorem for all joint transitions is asserted here. In
   particular, INVOKE cannot be counted as an atomic whole-callee write
   while its nested observations are also expanded in the trace. *)

Theorem concretize_future_witness_no_kill:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\
  joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> PHI /\
  allocation_exclusive P fn v /\
  step_inst fuel C inst s = OK s' /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (n:num) < j /\ j <= N /\ byte IN R j /\
  (!k. n <= k /\ k < j ==> byte NOTIN writes k) /\
  writes n = range_bytes (step_writes inst s s') ==>
  ~ptr_ml_can_kill (Allocation aid) bp sizes inst
Proof
  strip_tac >>
  `byte NOTIN range_bytes (step_writes inst s s')` by
    (qpat_x_assum `!k. n <= k /\ k < j ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  drule_all concretize_protected_cached_byte_no_kill >> simp[]
QED
