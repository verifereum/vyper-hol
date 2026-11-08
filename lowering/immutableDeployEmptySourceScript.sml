(* Source-side audit for the shared empty immutable deployment fixture. *)
Theory immutableDeployEmptySource
Ancestors
  immutableDeployEmptyDeployment vyperTypeContract vyperTypeInvariants
  exprSimHypsDefs vyperTypeCallStackSoundness vyperContext

Definition empty_immutable_env_def:
  empty_immutable_env =
    <|current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
      bare_globals := FEMPTY |+ ((NONE,"dst"),StructT (NONE,"Empty")) |+
                              ((NONE,"neighbor"),BaseT (UintT 256));
      bare_global_assignable := FEMPTY |+ ((NONE,"dst"),StructT (NONE,"Empty")) |+
                                         ((NONE,"neighbor"),BaseT (UintT 256));
      toplevel_vtypes := FEMPTY |+ ((NONE,"dst"),Type (StructT (NONE,"Empty"))) |+
                                 ((NONE,"neighbor"),Type (BaseT (UintT 256)));
      type_defs := type_env empty_immutable_tops;
      fn_sigs := FEMPTY |+ ((NONE,"__init__"),
                            <|param_types := []; num_defaults := 0; ret_ty := NoneT|>);
      flag_members := FEMPTY; event_fields := FEMPTY|>
End

Definition empty_immutable_es_def:
  empty_immutable_es = empty_state with
    <|scopes := [FEMPTY]; outcomes := SOME [];
      immutables := [(0w,[(NONE,FEMPTY |+ ("dst",(StructTV [],StructV [])) |+
                                       ("neighbor",(BaseTV (UintT 256),IntV 1)))])]|>
End

Definition empty_immutable_expr_def:
  empty_immutable_expr = StructLit (StructT (NONE,"Empty")) (NONE,"Empty") []
End

Theorem empty_immutable_target_typing:
  type_place_target empty_immutable_env (TopLevelNameTarget (NONE,"dst")) =
    SOME (Type (StructT (NONE,"Empty"))) /\
  type_widens_to empty_immutable_env.type_defs (expr_type empty_immutable_expr)
    (StructT (NONE,"Empty"))
Proof
  EVAL_TAC
QED

Theorem empty_immutable_call_safety_fails:
  ~call_evaluation_safe empty_immutable_cx (int_calls_expr empty_immutable_expr)
Proof
  simp[call_evaluation_safe_def, empty_immutable_cx_def,
       empty_evaluation_context_def]
QED

Theorem empty_immutable_source_pre_fails:
  ~expr_body_pre empty_immutable_ce empty_immutable_cx empty_immutable_env
    empty_immutable_expr empty_immutable_es
Proof
  simp[expr_body_pre_def, empty_immutable_call_safety_fails]
QED
