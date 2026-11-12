Theory bodyPtrIfExpGeneratedFrame
Ancestors bodySim exprLoweringProps

Theorem ifexp_generated_caller_frame:
  !tops ctx ce cx fn es s.
    body_inv tops ctx ce cx /\ stmt_state_rel ctx fn ce cx es s ==>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    (?rpolicy unit.
      (if cx.in_deploy then
         ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
       else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
      ctx = unit.cu_context /\ ce.ce_target = rpolicy.rpol_target)
Proof
  rpt strip_tac >>
  gvs[body_inv_def, stmt_state_rel_def, alloca_room_def] >>
  metis_tac[]
QED
