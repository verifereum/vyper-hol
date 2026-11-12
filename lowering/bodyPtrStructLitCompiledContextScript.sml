(* The full expression frame fixes the running function to the compiled context.
   Instruction-ID distinctness alone does not provide this boundary. *)
Theory bodyPtrStructLitCompiledContext
Ancestors
  bodySim exprLoweringProps

Theorem body_frame_compiled_context:
  body_inv tops ctx cenv cx /\ stmt_state_rel ctx func cenv cx es s ==>
  lookup_function func.fn_name ctx.ctx_functions = SOME func /\
  ?rpolicy unit.
    (if cx.in_deploy then
       ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
     else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
    ctx = unit.cu_context /\ cenv.ce_target = rpolicy.rpol_target
Proof
  simp[body_inv_def, stmt_state_rel_def, alloca_room_def] >>
  metis_tac[]
QED
