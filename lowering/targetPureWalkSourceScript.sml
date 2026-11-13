(* Source-only machine frame for a supported, nonmutating target walk. *)
Theory targetPureWalkSource
Ancestors
  targetPureWalkInternalFrame targetPureWalkTraversal vyperCallOutcomeFrame

val _ = Parse.hide "body";

Theorem target_walk_source_frame:
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
    function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
    IS_SOME (supported_function_decl (cx_tops cx) c Internal)) (int_calls_target bt) /\
  eval_base_place cx bt es = (INL pv,ee) ==>
  machine_frame (es with logs := ee.logs) ee
Proof
  strip_tac >>
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_base_place cx bt)` by
    (irule target_walk_source_frame_from_internal >>
     conj_tac >- (qexists_tac `cenv` >> simp[] >> rpt strip_tac >>
       irule target_walk_internal_frame >> metis_tac[]) >> simp[]) >>
  gvs[state_rel_frame_def] >> first_x_assum (qspec_then `es` mp_tac) >> simp[]
QED
