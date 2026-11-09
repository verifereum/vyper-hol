(* ALLOCA metadata is the resource boundary of a return observer. *)
Theory extcallReturnObserverResources
Ancestors
  extcallReturnObserver extcallReturnCountedTransport abiReturnPrefixTransport
  abiMalformedRecursiveInterface localPtrsProps compileEnv venomState
  list sorting pred_set exprLoweringProps venomInst venomWf

Theorem return_observer_alloca_structure:
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) ==>
  (state_rel obs ce cx es s <=> state_rel func ce cx es s) /\
  (immutable_alloca_sep obs ce cx es s <=> immutable_alloca_sep func ce cx es s) /\
  (abi_malformed_destination obs ce scopes aid d n s <=>
   abi_malformed_destination func ce scopes aid d n s) /\
  abi_malformed_scratch_sites st en obs = abi_malformed_scratch_sites st en func
Proof
  strip_tac >> rpt conj_tac
  >- (simp[state_rel_def, local_ptrs_rel_def, local_backed_def] >> metis_tac[])
  >- (simp[immutable_alloca_sep_def] >> metis_tac[])
  >- (simp[abi_malformed_destination_def] >> metis_tac[]) >>
  simp[abi_malformed_scratch_sites_def, EXTENSION] >> metis_tac[]
QED

Theorem return_observer_alloca_charge:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) ==>
  pending_alloca_size obs s = pending_alloca_size func s
Proof
  strip_tac >> irule return_observer_pending_charge >>
  irule return_observer_allocas_permutation >> simp[] >>
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  fs[fn_inst_ids_distinct_def, GSYM fn_insts_def] >>
  metis_tac[ALL_DISTINCT_MAP, fn_insts_def]
QED

Theorem return_observer_input_state:
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = DALLOCA ==>
    MEM i (fn_insts func)) ==>
  stmt_state_rel (return_observer_context ctx obs) obs ce cx es s
Proof
  strip_tac >> drule_all return_observer_alloca_charge >> strip_tac >>
  drule return_observer_alloca_structure >> strip_tac >>
  fs[stmt_state_rel_def] >> rpt conj_tac
  >- (irule return_observer_context_alloca_room >> metis_tac[])
  >- (irule return_observer_context_fmp_room_subset >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem return_observer_input_ready:
  abi_return_decode_ready ctx func ce cx es st sites dstid live base_op dst
    B cap bs d n s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = DALLOCA ==>
    MEM i (fn_insts func)) ==>
  abi_return_decode_ready (return_observer_context ctx obs) obs ce cx es st
    sites dstid live base_op dst B cap bs d n s
Proof
  strip_tac >>
  `stmt_state_rel (return_observer_context ctx obs) obs ce cx es s` by
    (irule return_observer_input_state >>
     fs[abi_return_decode_ready_def] >> metis_tac[]) >>
  drule return_observer_alloca_structure >> strip_tac >>
  fs[abi_return_decode_ready_def]
QED

Theorem return_observer_input_entry:
  abi_malformed_entry ctx func ce cx es st sites dstid live base_op hi src dst
    B L xs p d n s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = DALLOCA ==>
    MEM i (fn_insts func)) ==>
  abi_malformed_entry (return_observer_context ctx obs) obs ce cx es st
    sites dstid live base_op hi src dst B L xs p d n s
Proof
  strip_tac >>
  `stmt_state_rel (return_observer_context ctx obs) obs ce cx es s` by
    (irule return_observer_input_state >>
     fs[abi_malformed_entry_def] >> metis_tac[]) >>
  drule return_observer_alloca_structure >> strip_tac >>
  fs[abi_malformed_entry_def]
QED

(* A call-free context cannot recover the caller's call-closure reserves.
   The original initial bounds and the execution charge are retained. *)
Theorem return_observer_output_state:
  stmt_state_rel (return_observer_context ctx obs) obs ce cx es t /\
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  local_prefix ctx' obs cut s t /\ t.vs_fmp = s.vs_fmp ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `pending_alloca_size obs s = pending_alloca_size func s /\
   pending_alloca_size obs t = pending_alloca_size func t` by
    (conj_tac >> irule return_observer_alloca_charge >> simp[]) >>
  `t.vs_alloca_next + pending_alloca_size func t <=
   s.vs_alloca_next + pending_alloca_size func s` by
    metis_tac[return_observer_prefix_static_charge] >>
  drule return_observer_alloca_structure >> strip_tac >>
  fs[stmt_state_rel_def] >> rpt conj_tac
  >- (fs[alloca_room_def] >> decide_tac)
  >- (irule fmp_room_static_charge >> goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem return_observer_output_resources:
  abi_malformed_resource_post (return_observer_context ctx obs) obs
    ce cx es next sites dstid s t /\
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  local_prefix ctx' obs cut s t /\ t.vs_fmp = s.vs_fmp ==>
  abi_malformed_resource_post ctx func ce cx es next sites dstid s t
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule return_observer_output_state >>
     fs[abi_malformed_resource_post_def] >> metis_tac[]) >>
  fs[abi_malformed_resource_post_def] >> metis_tac[]
QED
