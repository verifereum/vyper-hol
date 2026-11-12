(* Diagnostic only: not a counterexample to the full target_walk_frame. *)
Theory targetPureWalkModuleProbe
Ancestors
  targetPureWalkSyntax targetPlaceSimDefs vyperMachineFrame
  vyperTypeContract exprLowering compileVyper vyperTypeCallGraph

Definition module_probe_body_def:
  module_probe_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"x")))
       (Literal (BaseT (UintT 256)) (IntL 1))]
End

Definition module_probe_other_def:
  module_probe_other =
    [FunctionDecl Internal Nonpayable F F "write" [] [] NoneT module_probe_body]
End

Definition module_probe_tops_def:
  module_probe_tops =
    [FunctionDecl Internal View F F "index" [] [] (BaseT (UintT 256))
       [Expr (Call NoneT (IntCall (SOME 1,"write")) [] NONE);
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Definition module_probe_cx_def:
  module_probe_cx = empty_evaluation_context with
    <| in_deploy := F;
       sources := [(0w,[(NONE,module_probe_tops);(SOME 1,module_probe_other)])] |>
End

Definition module_probe_target_def:
  module_probe_target = SubscriptTarget (NameTarget "a")
    (Call (BaseT (UintT 256)) (IntCall (NONE,"index")) [] NONE)
End

Theorem module_probe_checked_syntax:
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) module_probe_tops ==>
     function_mutability_ok [(NONE,module_probe_tops)] vis mut nr dflts body) /\
  call_target_mutability_ok [(NONE,module_probe_tops)] View
    (IntCall (SOME 1,"write")) /\
  build_func_mutability module_probe_tops "index" = View
Proof
  EVAL_TAC >> rpt strip_tac >>
  gvs[stmt_mutability_ok_def, expr_mutability_ok_def,
      atarget_mutability_ok_def, write_mutability_ok_def,
      call_target_mutability_ok_def] >> EVAL_TAC
QED

Definition module_probe_state_def:
  module_probe_state = empty_state with
    <| immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 0)))])];
       scopes := [FEMPTY |+ ("a", <| assignable := T;
         type := ArrayTV (BaseTV (UintT 256)) (Fixed 1);
         value := ArrayV (SArrayV []); popped := [] |>)] |>
End

Theorem module_probe_target_syntax:
  ~expr_can_mutate
    (cenv with ce_func_mutability := build_func_mutability module_probe_tops)
    (target_to_expr module_probe_target) /\
  get_module_code module_probe_cx NONE = SOME module_probe_tops /\
  EVERY (\c. FST c = NONE) (int_calls_target module_probe_target) /\
  ~module_probe_cx.in_deploy
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem module_probe_recursive_lookup:
  get_module_code
    (module_probe_cx with stk := [(NONE,"index")]) (SOME 1) =
    SOME module_probe_other /\
  lookup_callable_function F "write" module_probe_other =
    SOME (Nonpayable,F,[],[],NoneT,module_probe_body)
Proof
  EVAL_TAC
QED

Theorem module_probe_source_execution:
  !obs. eval_base_place module_probe_cx module_probe_target
      (module_probe_state with gas_obs := obs) =
    (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
     (module_probe_state with
       <| gas_obs := obs;
          immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 1)))])] |>))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem module_probe_admissible:
  gas_admissible (eval_base_place module_probe_cx module_probe_target)
    target_res_ok module_probe_state
Proof
  simp[gasContextTheory.gas_admissible_def, module_probe_source_execution,
       target_res_ok_def]
QED

Theorem module_probe_source_not_frame:
  !obs res ee.
    eval_base_place module_probe_cx module_probe_target
      (module_probe_state with gas_obs := obs) = (res,ee) ==>
    ~machine_frame (module_probe_state with logs := ee.logs) ee /\
    ee.scopes = module_probe_state.scopes
Proof
  simp[module_probe_source_execution] >> rpt strip_tac >> gvs[] >>
  gvs[machine_frame_def, module_probe_state_def, vyperStateTheory.empty_state_def,
      finite_mapTheory.FLOOKUP_EXT] >>
  fs[FUN_EQ_THM] >> first_x_assum (qspec_then `"x"` mp_tac) >> EVAL_TAC >> simp[]
QED

