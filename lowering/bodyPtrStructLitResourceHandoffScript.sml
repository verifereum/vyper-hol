Theory bodyPtrStructLitResourceHandoff
Ancestors bodyPtrDefs exprSafeOperand freshWrites finite_map
  bodyPtrStructLitInvokeFrame

(* General missing projection of the child simulation's resource boundary.
   Allocation production and memory/taint framing are deliberately separate. *)
Theorem ghost_kept_provenance:
  ghost_kept ce es sa G0 tn0 s0 G tn /\ not_fresh_at sa p ==>
  FLOOKUP G p = FLOOKUP G0 p
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

(* The first field calls cfn immediately at sb: compile_struct_lit_def
   emits its ADD only AFTER that call. No extension fact is needed there. *)
Theorem structlit_alloc_buffer_child_handoff:
  compile_alloc_buffer bytes sa = (buf,sb) /\
  buf.buf_operand = Var p /\
  ghost_kept ce es sb G0 tn0 s0 G tn ==>
  FLOOKUP G p = FLOOKUP G0 p
Proof
  rpt strip_tac >>
  drule alloc_buffer_safe_operand >>
  simp[safe_operand_def] >> strip_tac >>
  irule ghost_kept_provenance >> metis_tac[]
QED

(* Duplicate-search / concrete consumer ledger:
   - alloc_buffer_safe_operand (exprSafeOperand) supplies not_fresh_at sb p
     directly; safe_operand_def projects it when buf_operand = Var p.
   - ghost_kept_operand (wordArgsPtr) is a TAINT projection, not provenance;
     ghost_kept_trans composes the complete boundary. Neither duplicates the
     missing general provenance projection above. GhostFrame has only the
     PC-reference transport; FreshGhost supplies ghost_inv update facts.
   - invoke_memory_return_edge_provenance and
     invoke_emitted_void_edge_provenance (InvokeFrame) already preserve the
     entire caller provenance map for output-free INVOKE. CutProbe's claim
     that this particular resource fact is missing is superseded by this
     explicit ledger; it is global crossing, not this transfer, that is open.

   Concrete normal first-field consumer:
     compile_alloc_buffer total_size sa = (buf,sb), buf_operand = Var p;
     produce FLOOKUP G0 p = SOME(b,total_size) at sb using the counted
     allocation edge; apply the field's expr_sim_ptr at sb. Its normal post
     provides ghost_kept ce es sb G0 tn0 s0 G tn. The checked theorem above
     rewrites the supplied child endpoint lookup to the produced binding.
     This is retention of the SAME endpoint, not construction of another one.
   compile_expr's StructLit branch starts compile_struct_lit at sb, and its
   cons clause starts cfn at sb before emitting ADD. Later field entries need
   compiler monotonicity (not_fresh_at_mono) and resource transport across the
   intervening stores; those are not proved by this first-entry probe.
   Residual obligations: allocation edge must establish the full child entry
   ghost_inv, body/statement relations and resource separation; child post's
   own ptr_buf_ok may still require declared field layout capacity. Binding
   equality alone establishes neither memory agreement nor taint cleanliness,
   and does not solve the narrow-call supplied-endpoint capacity obstruction.
*)
