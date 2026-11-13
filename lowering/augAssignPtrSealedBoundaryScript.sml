(* Sealed-function boundary probe.  Keeping fn_insts is NOT the full
   interface of stmt_state_rel: alloca_room requires exact registration in
   ctx.ctx_functions (exprLoweringPropsScript.sml:247).  In particular, two
   distinct same-named functions cannot both satisfy the precondition, even
   if splitting their blocks preserves the complete instruction list.
   These lemmas expose the obstruction; they do not assert a task falsehood.
   A context-changing sealing construction would need additional transport
   for call graph, body_inv and all execution/exemption judgments. *)
Theory augAssignPtrSealedBoundary
Ancestors
  exprLoweringProps loweringPosts fragGasPathPtr fragExec venomInst

Theorem alloca_room_function_unique:
  !ctx f g s t.
    alloca_room ctx f s /\ alloca_room ctx g t /\
    f.fn_name = g.fn_name ==> f = g
Proof
  rpt strip_tac >> gvs[alloca_room_def]
QED

Theorem stmt_state_rel_function_unique:
  !ctx f g ce cx es s ce' cx' es' t.
    stmt_state_rel ctx f ce cx es s /\
    stmt_state_rel ctx g ce' cx' es' t /\
    f.fn_name = g.fn_name ==> f = g
Proof
  simp[stmt_state_rel_def] >> metis_tac[alloca_room_function_unique]
QED

Theorem gas_path_ptr_edge_none_at_block_end:
  !D lo ctx fn PG G tn s n H tm r bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx = LENGTH bb.bb_instructions ==>
    ~gas_path_ptr_edge D lo ctx fn PG G tn s n H tm r
Proof
  rpt strip_tac >> gvs[gas_path_ptr_edge_def, get_instruction_def]
QED

Theorem gas_path_ptr_stopped_invariant:
  !D lo ctx fn PG G tn s k H tm r.
    gas_path_ptr D lo ctx fn PG G tn s k H tm r ==>
    !E Inv.
    (!s G tn n H tm r. E s ==>
       ~gas_path_ptr_edge D lo ctx fn PG G tn s n H tm r) /\
    (!s G tn n H tm u. ~E s /\ Inv s G tn /\
       gas_path_ptr_edge D lo ctx fn PG G tn s n H tm (OK u) ==>
       Inv u H tm) /\ Inv s G tn ==>
    !t. r = OK t ==> Inv t H tm
Proof
  ho_match_mp_tac gas_path_ptr_ind >>
  simp[exit_result_def] >> rpt strip_tac >> metis_tac[]
QED
