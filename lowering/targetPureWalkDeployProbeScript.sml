(* Diagnostic only: this is not a counterexample to target_walk_frame. *)
Theory targetPureWalkDeployProbe
Ancestors
  targetPureWalkSyntax targetPlaceSimDefs vyperMachineFrame
  vyperTypeContract exprLowering compileVyper vyperTypeCallGraph

Definition deploy_probe_body_def:
  deploy_probe_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"x")))
       (Literal (BaseT (UintT 256)) (IntL 1))]
End

Definition deploy_probe_tops_def:
  deploy_probe_tops =
    [FunctionDecl Deploy Nonpayable F F "ctor" [] [] NoneT deploy_probe_body;
     FunctionDecl Internal View F F "index" [] [] (BaseT (UintT 256))
       [Expr (Call NoneT (IntCall (NONE,"ctor")) [] NONE);
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Definition deploy_probe_cx_def:
  deploy_probe_cx = empty_evaluation_context with
    <| in_deploy := T; sources := [(0w,[(NONE,deploy_probe_tops)])] |>
End

Definition deploy_probe_target_def:
  deploy_probe_target = SubscriptTarget (NameTarget "a")
    (Call (BaseT (UintT 256)) (IntCall (NONE,"index")) [] NONE)
End

Theorem deploy_probe_checked_syntax:
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) deploy_probe_tops ==>
     function_mutability_ok [(NONE,deploy_probe_tops)] vis mut nr dflts body) /\
  build_func_mutability deploy_probe_tops "index" = View /\
  lookup_callable_function F "ctor" deploy_probe_tops = NONE /\
  lookup_callable_function T "ctor" deploy_probe_tops =
    SOME (Nonpayable,F,[],[],NoneT,deploy_probe_body)
Proof
  EVAL_TAC >> rpt strip_tac >>
  gvs[stmt_mutability_ok_def, expr_mutability_ok_def,
      atarget_mutability_ok_def, write_mutability_ok_def,
      call_target_mutability_ok_def] >> EVAL_TAC
QED

Definition deploy_probe_state_def:
  deploy_probe_state = empty_state with
    <| immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 0)))])];
       scopes := [FEMPTY |+ ("a", <| assignable := T;
         type := ArrayTV (BaseTV (UintT 256)) (Fixed 1);
         value := ArrayV (SArrayV []); popped := [] |>)] |>
End

Theorem deploy_probe_target_syntax:
  ~expr_can_mutate
    (cenv with ce_func_mutability := build_func_mutability deploy_probe_tops)
    (target_to_expr deploy_probe_target) /\
  get_module_code deploy_probe_cx NONE = SOME deploy_probe_tops /\
  EVERY (\c. FST c = NONE) (int_calls_target deploy_probe_target)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem deploy_probe_source_execution:
  !obs. eval_base_place deploy_probe_cx deploy_probe_target
      (deploy_probe_state with gas_obs := obs) =
    (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
     (deploy_probe_state with
       <| gas_obs := obs;
          immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 1)))])] |>))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem deploy_probe_admissible:
  gas_admissible (eval_base_place deploy_probe_cx deploy_probe_target)
    target_res_ok deploy_probe_state
Proof
  simp[gasContextTheory.gas_admissible_def, deploy_probe_source_execution,
       target_res_ok_def]
QED

Theorem deploy_probe_source_not_frame:
  !obs res ee.
    eval_base_place deploy_probe_cx deploy_probe_target
      (deploy_probe_state with gas_obs := obs) = (res,ee) ==>
    ~machine_frame (deploy_probe_state with logs := ee.logs) ee /\
    ee.scopes = deploy_probe_state.scopes
Proof
  simp[deploy_probe_source_execution] >> rpt strip_tac >> gvs[] >>
  gvs[machine_frame_def, deploy_probe_state_def, vyperStateTheory.empty_state_def,
      finite_mapTheory.FLOOKUP_EXT] >>
  fs[FUN_EQ_THM] >> first_x_assum (qspec_then `"x"` mp_tac) >> EVAL_TAC >> simp[]
QED
