Theory immutableDeployEmptyFixture
Ancestors
  immutableDeployEmptyProbe exprSimAggregates exprSimHypsDefs compileVyper supportedProgram

Theorem empty_struct_vv_sim:
  !ctx func cenv cx env ann nsid ty es.
    expr_body_pre cenv cx env (StructLit ann nsid []) es ==>
    expr_vv_sim ctx func cenv cx ty (StructLit ann nsid []) es
Proof
  rpt strip_tac >>
  qspecl_then [`F`, `ctx`, `func`, `cenv`, `cx`, `ann`, `nsid`, `[]`]
    mp_tac compile_struct_lit_vv_case >>
  simp[exprs_case_def, expr_vv_case_def] >>
  disch_then drule >> simp[]
QED

Definition empty_immutable_tops_def:
  empty_immutable_tops =
    [StructDecl "Empty" [];
     VariableDecl Private Immutable "dst" (StructT (NONE,"Empty")) NONE;
     VariableDecl Private Immutable "neighbor" (BaseT (UintT 256)) NONE;
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT []]
End

Theorem empty_immutable_program_supported:
  supported_program empty_immutable_tops
Proof
  EVAL_TAC
QED

Theorem empty_immutable_destination_supported:
  supported_immutable_type empty_immutable_tops (NONE,"dst") =
    SOME (StructT (NONE,"Empty"))
Proof
  EVAL_TAC
QED

Theorem empty_immutable_layout_probe:
  add_immutable_locations (get_struct_fields (make_struct_fields_map empty_immutable_tops))
    empty_immutable_tops 0 FEMPTY =
    FEMPTY |+ ((NONE,"dst"),ImmutableLoc 0) |+
              ((NONE,"neighbor"),ImmutableLoc 0) /\
  compute_immutables_len (get_struct_fields (make_struct_fields_map empty_immutable_tops))
    empty_immutable_tops = 32
Proof
  EVAL_TAC
QED

Theorem empty_immutable_constructor_probe:
  classify_functions empty_immutable_tops =
    ([],[],NONE,SOME (Payable,F,F,"__init__",[],[],NoneT,[])) /\
  ctor_named_init (SOME (Payable,F,F,"__init__",[],[],NoneT,[])) /\
  fn_allocs_ok empty_immutable_tops
    (Payable,F,F,"__init__",[],[],NoneT,[])
Proof
  EVAL_TAC
QED

Theorem empty_immutable_deploy_boundary:
  lower_vyper_deploy_unit empty_immutable_tops policy [] =
    run_deploy_lowering T policy [] 32 [] 0 []
      ((build_compile_env empty_immutable_tops Deploy Payable "__init__"
          [] NoneT [] F) with
        <|ce_is_ctor := T; ce_raw_return := F;
          ce_target := policy.rpol_target|>)
      [] T F 0 F "__deploy"
Proof
  simp[lower_vyper_deploy_unit_def, empty_immutable_constructor_probe,
       empty_immutable_layout_probe, package_constructor_def,
       set_constructor_package_target_def, update_cenv_nonreentrant_def,
       build_positional_args_def] >>
  EVAL_TAC
QED
