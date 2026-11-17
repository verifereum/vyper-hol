(* Source-side resources for the successful RHS and nonmutating target walk. *)
Theory localMemorySourceProbe
Ancestors
  localMemoryTargetProbe targetPureWalkSource targetPureWalkScopes
  targetPureSourceFrame bodySim exprSimHypsDefs gasContext
  vyperMachineFrame vyperState vyperInterpreter stmtLowering exprLowering
  compileVyper supportedProgram list

val _ = Parse.hide "body";

Theorem nonmutating_target_source_oracles:
  body_inv tops ctx cenv cx /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  EVERY (\c. FST c = NONE /\ supported_program tops /\
    IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
  eval_base_place cx bt mid = (INL pv,ee) ==>
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  ee.scopes = mid.scopes
Proof
  strip_tac >>
  `cx_tops cx = tops /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_func_mutability = build_func_mutability tops` by
    (fs[body_inv_def,cenv_module_pins_def] >> metis_tac[cx_tops_module]) >>
  `!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops ==>
    function_mutability_ok [(NONE,tops)] vis mut nr dflts body` by
    fs[body_inv_def] >>
  `machine_frame (mid with logs := ee.logs) ee` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`,`bt` |-> `bt`,`cx` |-> `cx`,
       `es` |-> `mid`,`pv` |-> `pv`,`ee` |-> `ee`]
       (SPEC_ALL target_walk_source_frame)) >> simp[] >> metis_tac[]) >>
  drule_all target_walk_scopes >> strip_tac >>
  fs[machine_frame_def,evaluation_state_component_equality]
QED

Theorem effect_free_memory_entry_types:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME root_ty /\
  ~expr_has_effect e /\ eval_expr cx e es = (rr,mid) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  eval_base_place cx bt mid = (INL pv,ee) /\
  lookup_scopes id ee.scopes = SOME entry ==>
  cenv.ce_var_type id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  (!t0. cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type)
Proof
  strip_tac >>
  `mid.scopes = es.scopes` by
    (drule_all effect_free_source_projection >>
     simp[evaluation_state_component_equality]) >>
  drule_all target_walk_scopes >> strip_tac >>
  `ee.scopes = es.scopes` by metis_tac[] >>
  drule_all local_memory_entry_types >> simp[]
QED
