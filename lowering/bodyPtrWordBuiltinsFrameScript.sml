(* Boundary from the unchanged frame to its actually lowered unit. *)
Theory bodyPtrWordBuiltinsFrame
Ancestors bodySim bodyPtrWordBuiltinsContext

Theorem body_inv_stmt_state_rel_unit:
  !tops ctx cenv cx func es s0.
    body_inv tops ctx cenv cx /\
    stmt_state_rel ctx func cenv cx es s0 ==>
    ?rpolicy unit.
      (if cx.in_deploy then
         ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
       else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
      ctx = unit.cu_context /\
      cenv.ce_target = rpolicy.rpol_target /\
      lookup_function func.fn_name unit.cu_context.ctx_functions = SOME func
Proof
  rpt strip_tac >>
  drule stmt_state_rel_lookup_function >>
  gvs[body_inv_def] >>
  metis_tac[]
QED
