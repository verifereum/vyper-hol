(* Concrete fixtures expose complete-unit frame obligations reproducibly;
   these abbreviations do not add semantic invariants or assume frames. *)
Theory bodyPtrWordBuiltinsAbsRuntime
Ancestors compileVyper bodySim bodyPtrDefs exprSimHypsDefs
  bodyPtrWordBuiltinsNameProbe venomCompilerTypes venomPolicyTypes
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Definition word_abs_runtime_expr_def:
  word_abs_runtime_expr = Builtin (BaseT (IntT 256)) Abs
    [Name (BaseT (IntT 256)) "x"]
End

Definition word_abs_runtime_tops_def:
  word_abs_runtime_tops =
    [FunctionDecl External Nonpayable F F "foo"
      [("x", BaseT (IntT 256))] [] NoneT [Expr word_abs_runtime_expr]]
End

Definition word_abs_runtime_policy_def:
  word_abs_runtime_policy = <|rpol_target := all_capabilities;
    rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize|>
End

(* Evaluate the public recursion equations, not Defn's internal relation. *)
val () = computeLib.upd_compset (fn cs =>
  (computeLib.scrub_const cs ``compile_expr``;
   computeLib.scrub_const cs ``compile_builtin_dispatch``;
   computeLib.scrub_const cs ``compile_type_builtin_dispatch``;
   computeLib.add_thms
     [exprLoweringTheory.compile_expr_component_eq,
      exprLoweringTheory.compile_builtin_dispatch_component_eq,
      exprLoweringTheory.compile_type_builtin_dispatch_component_eq] cs))

(* Named concrete source/environment keep staged certificates shared. *)
Definition word_abs_runtime_source_def:
  word_abs_runtime_source =
    (Nonpayable,F,F,"foo",[("x",BaseT (IntT 256))],[],NoneT,
     [Expr word_abs_runtime_expr])
End

Definition word_abs_runtime_cenv_def:
  word_abs_runtime_cenv =
    (build_compile_env word_abs_runtime_tops External Nonpayable "foo"
      [("x",BaseT (IntT 256))] NoneT [Expr word_abs_runtime_expr] F)
    with <|ce_raw_return := F; ce_nonreentrant := (F,0,F,F)|>
End

Theorem word_abs_runtime_package:
  package_external_fn word_abs_runtime_tops F (K 0)
    word_abs_runtime_source =
  ("fn_foo", word_abs_runtime_cenv,
   build_positional_args word_abs_runtime_cenv [("x",BaseT (IntT 256))],
   min_calldata_size word_abs_runtime_cenv [("x",BaseT (IntT 256))] 0,
   F,F,0,F,F,[Expr word_abs_runtime_expr],NONE)
Proof
  simp[package_external_fn_def, word_abs_runtime_source_def,
       word_abs_runtime_cenv_def, update_cenv_nonreentrant_def]
QED

Theorem word_abs_runtime_cenv_eval:
  word_abs_runtime_cenv =
  <|ce_target := K T; ce_vars := FEMPTY |+ ("x", MemLoc 0 32);
    ce_module_vars := FEMPTY; ce_storage_layout := FEMPTY;
    ce_module := NONE; ce_struct_fields := FEMPTY;
    ce_dynarray_capacity := K 0; ce_module_dynarray_capacity := K 0;
    ce_method_id := (\s tys. w2n (calldata_method_id
      (function_selector s (vyper_to_abi_types FEMPTY tys))));
    ce_flag_member_id := K (K 0); ce_flag_n_members := K 0;
    ce_var_type := (\n. if "x" = n then SOME (BaseT (IntT 256)) else NONE);
    ce_module_var_type := K NONE; ce_hashmap_info := K NONE;
    ce_event_info := K NONE; ce_type_env := FEMPTY; ce_returns_count := 0;
    ce_return_buf := NONE; ce_return_pc := NONE; ce_ctor_exit_label := NONE;
    ce_is_external := T; ce_ret_enc_info := AbiPrimWord;
    ce_ret_dec_info := DecPrimWord NoClamp; ce_max_return_size := 0;
    ce_is_ctor := F; ce_imm_alloca := NONE; ce_func_info := K (0,0,[]);
    ce_func_param_types := K []; ce_func_return_type := K NoneT;
    ce_func_ids := K 0; ce_nonreentrant := (F,0,F,F);
    ce_raw_return := F; ce_alloca_locals := T|>
Proof
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])) >>
  REFL_TAC
QED

Theorem word_abs_runtime_allocs:
  fn_allocs_ok word_abs_runtime_tops word_abs_runtime_source
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

Theorem word_abs_runtime_fallback:
  package_fallback_fn word_abs_runtime_tops F (K 0) NONE = NONE
Proof
  EVAL_TAC
QED

Theorem word_abs_runtime_posargs:
  build_positional_args word_abs_runtime_cenv [("x",BaseT (IntT 256))] =
  [("x",T,F,32,DecPrimWord NoClamp)]
Proof
  rewrite_tac[word_abs_runtime_cenv_eval] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

Theorem word_abs_runtime_mincds:
  min_calldata_size word_abs_runtime_cenv [("x",BaseT (IntT 256))] 0 = 36
Proof
  rewrite_tac[word_abs_runtime_cenv_eval] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED


Theorem word_abs_runtime_lowers:
  IS_SOME (lower_vyper_runtime_unit word_abs_runtime_tops word_abs_runtime_policy)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``package_external_fn``, ``run_lowering``, ``build_selectors``,
     ``package_fallback_fn``, ``fn_allocs_ok``, ``word_abs_runtime_expr``]) >>
  pure_rewrite_tac [set_external_package_target_all,
    set_fallback_package_target_all, GSYM word_abs_runtime_tops_def,
    GSYM word_abs_runtime_source_def, word_abs_runtime_package,
    word_abs_runtime_allocs, word_abs_runtime_fallback,
    word_abs_runtime_posargs, word_abs_runtime_mincds] >>
  simp[external_return_buffer_ok_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

(* The actual lowered unit and source call frame, not an arbitrary graph. *)
Definition word_abs_runtime_unit_def:
  word_abs_runtime_unit = THE
    (lower_vyper_runtime_unit word_abs_runtime_tops word_abs_runtime_policy)
End

Definition word_abs_runtime_cx_def:
  word_abs_runtime_cx = initial_evaluation_context
    [(0w, [(NONE, word_abs_runtime_tops)])] []
    (empty_call_txn with <|function_name := "foo"; args := [IntV 1]|>) NONE
End

Theorem word_abs_runtime_unit_eq:
  lower_vyper_runtime_unit word_abs_runtime_tops word_abs_runtime_policy =
    SOME word_abs_runtime_unit
Proof
  mp_tac word_abs_runtime_lowers >>
  Cases_on `lower_vyper_runtime_unit word_abs_runtime_tops word_abs_runtime_policy` >>
  simp[word_abs_runtime_unit_def]
QED

Theorem word_abs_runtime_body_inv:
  body_inv word_abs_runtime_tops word_abs_runtime_unit.cu_context
    (word_abs_runtime_cenv with ce_vars := vars) word_abs_runtime_cx
Proof
  rewrite_tac[body_inv_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (qexistsl [`word_abs_runtime_policy`, `word_abs_runtime_unit`] >>
      simp[word_abs_runtime_cx_def, vyperInterpreterTheory.initial_evaluation_context_def,
           word_abs_runtime_unit_eq, word_abs_runtime_cenv_eval,
           word_abs_runtime_policy_def, all_capabilities_def]) >>
  rewrite_tac[word_abs_runtime_cenv_eval] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

(* Parameter registration replaces its static MemLoc with this actual alloca. *)
Definition word_abs_runtime_frame_cenv_def:
  word_abs_runtime_frame_cenv = word_abs_runtime_cenv with
    ce_vars := FEMPTY |+ ("x", PtrVar (Var "%11") 32)
End

Definition word_abs_runtime_env_def:
  word_abs_runtime_env = function_entry_env
    (build_contract_type_artifact F [(NONE,word_abs_runtime_tops)])
    [(NONE,word_abs_runtime_tops)] NONE External [("x",BaseT (IntT 256))]
End

Definition word_abs_runtime_es_def:
  word_abs_runtime_es = empty_state with
    <|scopes := [FEMPTY |+ ("x", <|assignable := F; type := BaseTV (IntT 256);
                                value := IntV 1; popped := []|>)];
      outcomes := SOME []|>
End

Theorem word_abs_runtime_contract_check:
  check_contract F [] 0w [(NONE,word_abs_runtime_tops)] =
    SOME (build_contract_type_artifact F [(NONE,word_abs_runtime_tops)])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

Theorem word_abs_runtime_functions_typed:
  functions_well_typed word_abs_runtime_cx
Proof
  rewrite_tac[word_abs_runtime_cx_def] >>
  irule vyperTypeContractFunctionTheory.check_contract_functions_well_typed_initial >>
  qexistsl [`0w`, `build_contract_type_artifact F [(NONE,word_abs_runtime_tops)]`,
            `[(NONE,word_abs_runtime_tops)]`] >>
  simp[word_abs_runtime_contract_check, vyperContextTheory.empty_call_txn_def]
QED

Theorem word_abs_runtime_context_typed:
  context_well_typed word_abs_runtime_cx
Proof
  EVAL_TAC
QED

Theorem word_abs_runtime_expr_pre:
  expr_body_pre word_abs_runtime_frame_cenv word_abs_runtime_cx
    word_abs_runtime_env word_abs_runtime_expr word_abs_runtime_es
Proof
  rewrite_tac[expr_body_pre_def, expr_sim_inv_def,
    word_abs_runtime_functions_typed, word_abs_runtime_context_typed,
    word_abs_runtime_frame_cenv_def, word_abs_runtime_cenv_eval] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[vyperStateTheory.lookup_flag_def,
       vyperStateTheory.find_var_decl_by_name_def,
       vyperValueTheory.evaluate_type_def,
       vyperTypingTheory.value_has_type_def,
       vyperTypingTheory.well_formed_type_value_def,
       vyperValueTheory.within_int_bound_def, AllCaseEqs()] >>
  qexists_tac `[]` >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       vyperInterpreterTheory.lookup_function_def,
       relationTheory.irreflexive_def] >>
  gen_tac >> strip_tac >> drule relationTheory.TC_CASES1_E >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED
