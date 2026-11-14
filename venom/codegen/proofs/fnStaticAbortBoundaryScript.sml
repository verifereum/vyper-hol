Theory fnStaticAbortBoundary
Ancestors
  fnStaticAbortSim staticAbortExec frameRel contextCodegenRel codegenRel
  contextStaticAbortRel

(* The full pre-cut frame relation exposes exactly the concrete stack shape
   and shared fields needed by generated_lineage_static_abort_prefix.
   No relation on spill values is asserted after this cut. *)
Theorem static_abort_frame_cut:
  !ctx cp lo fn ra rest mem0 ps vs ast.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast ==>
  (?top. ast.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack) /\
  ast.as_call_ctx = vs.vs_call_ctx /\
  ast.as_requests = vs.vs_requests
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def,
       plan_stack_rel_def, frame_view_def] >> metis_tac[]
QED
