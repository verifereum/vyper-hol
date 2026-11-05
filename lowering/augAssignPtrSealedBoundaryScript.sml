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
  exprLoweringProps loweringPosts

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
