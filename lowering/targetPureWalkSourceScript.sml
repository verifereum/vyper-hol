(* Source-only machine frame for a supported, nonmutating target walk. *)
Theory targetPureWalkSource
Ancestors
  targetPureWalkInternalFrame targetPureWalkTraversal vyperCallOutcomeFrame
  bodySim bodyTypedTargetScope gasContext abiEncodeArgsScopes

val _ = Parse.hide "body";

Theorem nonmutating_exprs_source_frame:
  body_inv tops ctx cenv cx /\
  ~exprs_can_mutate cenv es /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs es) /\
  eval_exprs cx es s = (res,t) ==>
  machine_frame (s with logs := t.logs) t /\ t.scopes = s.scopes
Proof
  strip_tac >>
  `cx_tops cx = tops` by metis_tac[body_inv_def, cx_tops_module] >>
  drule_then assume_tac body_inv_qualified_module_absent >>
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
       (eval_exprs cx es)` by
    (irule exprs_source_frame_from_internal >> conj_tac
     >- (qexists_tac `cenv` >> simp[] >> rpt strip_tac >>
         irule target_walk_internal_frame >>
         fs[body_inv_def, cenv_module_pins_def] >> metis_tac[]) >>
     fs[body_inv_def, listTheory.EVERY_MEM]) >>
  conj_tac
  >- (qpat_assum `state_rel_frame _ _`
       (mp_tac o Q.SPEC `s` o REWRITE_RULE [state_rel_frame_def]) >> simp[]) >>
  metis_tac[eval_exprs_no_mutation_scopes]
QED

Theorem target_walk_source_frame:
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
    function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  (!src. get_module_code cx (SOME src) = NONE) /\
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
