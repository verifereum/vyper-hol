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
    (empty_call_txn with <|function_name := "foo"; args := [IntV 1];
      block_number := 1; block_hashes := [0w]|>) NONE
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

Theorem word_abs_runtime_eval:
  bind (eval_expr word_abs_runtime_cx word_abs_runtime_expr)
    (read_result word_abs_runtime_cx)
    (word_abs_runtime_es with gas_obs := gs) =
  (INL (IntV 1), word_abs_runtime_es with gas_obs := gs)
Proof
  EVAL_TAC
QED

Theorem word_abs_runtime_gas_admissible:
  gas_admissible
    (bind (eval_expr word_abs_runtime_cx word_abs_runtime_expr)
      (read_result word_abs_runtime_cx)) expr_res_ok word_abs_runtime_es
Proof
  simp[gasContextTheory.gas_admissible_def, word_abs_runtime_eval,
       exprSimDefsTheory.expr_res_ok_def]
QED

Definition word_abs_runtime_func_def:
  word_abs_runtime_func = THE (lookup_function "__entry"
    word_abs_runtime_unit.cu_context.ctx_functions)
End

Theorem word_abs_runtime_func_name:
  word_abs_runtime_func.fn_name = "__entry"
Proof
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``package_external_fn``, ``run_lowering``, ``build_selectors``,
     ``package_fallback_fn``, ``fn_allocs_ok``, ``word_abs_runtime_expr``])) >>
  pure_rewrite_tac [set_external_package_target_all,
    set_fallback_package_target_all, GSYM word_abs_runtime_tops_def,
    GSYM word_abs_runtime_source_def, word_abs_runtime_package,
    word_abs_runtime_allocs, word_abs_runtime_fallback,
    word_abs_runtime_posargs, word_abs_runtime_mincds] >>
  simp[external_return_buffer_ok_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])) >>
  simp[listTheory.INDEX_FIND_def]
QED

(* The expression begins after the actual parameter decoder (ids 10--20).
   Using the compiled block prefix avoids inventing a replacement function. *)
Definition word_abs_runtime_sa_def:
  word_abs_runtime_sa = (initial_compile_state "fn_foo") with
    <|cs_next_var := 14; cs_next_label := 4; cs_next_id := 21;
      cs_current_insts := TAKE 11
        (EL 4 word_abs_runtime_func.fn_blocks).bb_instructions|>
End

Definition word_abs_runtime_sb_def:
  word_abs_runtime_sb = SND (lower_value compile_expr
    word_abs_runtime_frame_cenv (BaseT (IntT 256)) word_abs_runtime_expr
    word_abs_runtime_sa)
End

Theorem word_abs_runtime_compile:
  lower_value compile_expr word_abs_runtime_frame_cenv
    (BaseT (IntT 256)) word_abs_runtime_expr word_abs_runtime_sa =
    (Var "%22", word_abs_runtime_sb)
Proof
  rewrite_tac[word_abs_runtime_sb_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_func``, ``function_selector``,
     ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

Theorem word_abs_runtime_code:
  fn_has_code word_abs_runtime_sa word_abs_runtime_sb word_abs_runtime_func /\
  fn_inst_ids_distinct word_abs_runtime_func
Proof
  rewrite_tac[word_abs_runtime_sb_def, word_abs_runtime_sa_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_func``, ``function_selector``,
     ``calldata_method_id``, ``vyper_to_abi_types``, ``fn_has_code``]) >>
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``package_external_fn``, ``run_lowering``, ``build_selectors``,
     ``package_fallback_fn``, ``fn_allocs_ok``, ``word_abs_runtime_expr``,
     ``fn_has_code``]) >>
  pure_rewrite_tac [set_external_package_target_all,
    set_fallback_package_target_all, GSYM word_abs_runtime_tops_def,
    GSYM word_abs_runtime_source_def, word_abs_runtime_package,
    word_abs_runtime_allocs, word_abs_runtime_fallback,
    word_abs_runtime_posargs, word_abs_runtime_mincds] >>
  simp[external_return_buffer_ok_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``,
     ``fn_has_code``]) >>
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``,
     ``isPREFIX``]) >>
  simp[] >> EVAL_TAC
QED

Theorem word_abs_runtime_tx_env_valid:
  tx_env_ok word_abs_runtime_cx.txn
Proof
  EVAL_TAC
QED

(* Target expression-entry state: the parameter alloca holds IntV 1. *)
Definition word_abs_runtime_s0_def:
  word_abs_runtime_s0 = (init_venom_state "fn_foo") with
    <|vs_memory := REPLICATE 31 0w ++ [1w];
      vs_vars := FEMPTY |+ ("%11",0w);
      vs_allocas := FEMPTY |+ (17,(0,32)); vs_alloca_next := 32;
      vs_inst_idx := 11;
      vs_block_ctx := empty_block_context with bc_number := 1w|>
End

Theorem word_abs_runtime_call_ctx:
  call_ctx_rel word_abs_runtime_cx.txn word_abs_runtime_s0.vs_call_ctx
    word_abs_runtime_s0.vs_tx_ctx word_abs_runtime_s0.vs_block_ctx
Proof
  EVAL_TAC >> simp[]
QED

Theorem word_abs_runtime_state_rel:
  local_ptrs_rel word_abs_runtime_func word_abs_runtime_frame_cenv
    word_abs_runtime_es.scopes word_abs_runtime_s0 ==>
  state_rel word_abs_runtime_func word_abs_runtime_frame_cenv
    word_abs_runtime_cx word_abs_runtime_es word_abs_runtime_s0
Proof
  rewrite_tac[compileEnvTheory.state_rel_def, word_abs_runtime_call_ctx] >>
  strip_tac >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

Theorem word_abs_runtime_locals:
  local_backed word_abs_runtime_func "%11" word_abs_runtime_s0 0 32 ==>
  local_ptrs_rel word_abs_runtime_func word_abs_runtime_frame_cenv
    word_abs_runtime_es.scopes word_abs_runtime_s0
Proof
  strip_tac >>
  rewrite_tac[compileEnvTheory.local_ptrs_rel_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_func``, ``local_backed``, ``function_selector``,
     ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  rw[AllCaseEqs()] >>
  gvs[word_abs_runtime_s0_def, venomStateTheory.init_venom_state_def,
      venomStateTheory.empty_block_context_def, venomStateTheory.empty_call_context_def,
      venomStateTheory.empty_tx_context_def] >>
  rule_assum_tac (CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``local_backed``, ``word_abs_runtime_func``])) >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem word_abs_runtime_local_backed:
  local_backed word_abs_runtime_func "%11" word_abs_runtime_s0 0 32
Proof
  rewrite_tac[compileEnvTheory.local_backed_def] >> disj1_tac >>
  qexists_tac `<|inst_id := 17; inst_opcode := ALLOCA;
    inst_operands := [Lit 32w]; inst_outputs := ["%11"]|>` >>
  simp[word_abs_runtime_s0_def, venomStateTheory.init_venom_state_def] >>
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
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
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[]
QED

Theorem word_abs_runtime_memory:
  mem_agree_outside {} word_abs_runtime_s0.vs_memory mem ==>
  val_in_memory (BaseTV (IntT 256)) (IntV 1) 0 mem
Proof
  strip_tac >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- EVAL_TAC >>
  qexistsl_tac [`32`, `word_abs_runtime_s0.vs_memory`] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
      gvs[mem_agree_outside_def]) >>
  EVAL_TAC >> simp[wordsTheory.w2n_n2w]
QED

Theorem word_abs_runtime_ghost:
  FLOOKUP G "%11" = SOME (0,32) ==>
  ghost_inv NONE word_abs_runtime_frame_cenv word_abs_runtime_cx
    word_abs_runtime_es G entry_taint word_abs_runtime_s0
Proof
  strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_s0``, ``ptr_covers``, ``val_in_memory``,
     ``mem_agree_outside``, ``function_selector``, ``calldata_method_id``,
     ``vyper_to_abi_types``]) >>
  rw[AllCaseEqs()] >> gvs[]
  >- (simp[ptr_covers_def, ptrDisciplineTheory.op_taint_def,
           word_abs_runtime_s0_def, venomStateTheory.init_venom_state_def,
           venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `w = 0w` by gvs[word_abs_runtime_s0_def,
    venomStateTheory.init_venom_state_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[] >> irule word_abs_runtime_memory >> simp[]
QED

Theorem word_abs_runtime_state:
  state_rel word_abs_runtime_func word_abs_runtime_frame_cenv
    word_abs_runtime_cx word_abs_runtime_es word_abs_runtime_s0
Proof
  irule word_abs_runtime_state_rel >> irule word_abs_runtime_locals >>
  irule word_abs_runtime_local_backed
QED

Theorem word_abs_runtime_local_reserved:
  local_ptrs_reserved word_abs_runtime_frame_cenv word_abs_runtime_sa
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_func``, ``function_selector``, ``calldata_method_id``,
     ``vyper_to_abi_types``, ``not_fresh_at``]) >>
  rw[AllCaseEqs()] >> gvs[] >>
  `"11" = toString (11:num)` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  simp[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `toString n = toString 11` mp_tac >>
  pure_rewrite_tac[ASCIInumbersTheory.toString_inj] >>
  strip_tac >> gvs[]
QED

Theorem word_abs_runtime_alloca_inv:
  alloca_inv word_abs_runtime_s0
Proof
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[]
QED

Theorem word_abs_runtime_functions:
  word_abs_runtime_unit.cu_context.ctx_functions = [word_abs_runtime_func]
Proof
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
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
  simp[listTheory.INDEX_FIND_def]
QED

Theorem word_abs_runtime_no_calls_scratch:
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA)
    (fn_insts word_abs_runtime_func)
Proof
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
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
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

Theorem word_abs_runtime_no_reachable:
  !g. ~TC (fn_directly_calls word_abs_runtime_unit.cu_context)
    word_abs_runtime_func.fn_name g
Proof
  gen_tac >>
  `!g. ~fn_directly_calls word_abs_runtime_unit.cu_context
    word_abs_runtime_func.fn_name g` suffices_by
    (strip_tac >> strip_tac >> drule relationTheory.TC_CASES1_E >> simp[]) >>
  simp[fcgDefsTheory.fn_directly_calls_def, word_abs_runtime_functions,
    word_abs_runtime_func_name, venomInstTheory.lookup_function_def,
    listTheory.FIND_def, listTheory.INDEX_FIND_def] >>
  mp_tac word_abs_runtime_no_calls_scratch >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem word_abs_runtime_fmp_room:
  fmp_room word_abs_runtime_unit.cu_context word_abs_runtime_func
    word_abs_runtime_s0
Proof
  simp[exprLoweringPropsTheory.fmp_room_def, word_abs_runtime_no_reachable, listTheory.EXISTS_MEM] >>
  mp_tac word_abs_runtime_no_calls_scratch >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem word_abs_runtime_alloca_insts:
  FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts word_abs_runtime_func) =
    [<|inst_id := 17; inst_opcode := ALLOCA; inst_operands := [Lit 32w];
       inst_outputs := ["%11"]|>]
Proof
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
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
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

Theorem word_abs_runtime_pending_alloca:
  pending_alloca_size word_abs_runtime_func word_abs_runtime_s0 = 0
Proof
  rewrite_tac[exprLoweringPropsTheory.pending_alloca_size_def] >>
  `FILTER (\i. i.inst_opcode = ALLOCA /\
      i.inst_id NOTIN FDOM word_abs_runtime_s0.vs_allocas)
      (fn_insts word_abs_runtime_func) =
    FILTER (\i. i.inst_id NOTIN FDOM word_abs_runtime_s0.vs_allocas)
      (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts word_abs_runtime_func))`
    by (qspec_tac (`fn_insts word_abs_runtime_func`, `is`) >>
        Induct >> simp[] >> gen_tac >>
        Cases_on `h.inst_opcode = ALLOCA` >> simp[] >>
        Cases_on `h.inst_id IN FDOM word_abs_runtime_s0.vs_allocas` >> simp[]) >>
  pop_assum SUBST1_TAC >> rewrite_tac[word_abs_runtime_alloca_insts] >>
  EVAL_TAC
QED

Theorem word_abs_runtime_alloca_room:
  alloca_room word_abs_runtime_unit.cu_context word_abs_runtime_func
    word_abs_runtime_s0
Proof
  simp[exprLoweringPropsTheory.alloca_room_def, word_abs_runtime_functions,
    word_abs_runtime_no_reachable, word_abs_runtime_pending_alloca,
    venomInstTheory.lookup_function_def, listTheory.FIND_def,
    listTheory.INDEX_FIND_def, word_abs_runtime_func_name,
    word_abs_runtime_s0_def, venomStateTheory.init_venom_state_def, wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem word_abs_runtime_alloca_sizes:
  !inst n base sz.
    MEM inst (fn_insts word_abs_runtime_func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP word_abs_runtime_s0.vs_allocas inst.inst_id = SOME (base,sz) ==>
    sz = w2n n
Proof
  rpt strip_tac >>
  `MEM inst (FILTER (\i. i.inst_opcode = ALLOCA)
    (fn_insts word_abs_runtime_func))` by simp[listTheory.MEM_FILTER] >>
  gvs[word_abs_runtime_alloca_insts, word_abs_runtime_s0_def,
    venomStateTheory.init_venom_state_def, finite_mapTheory.FLOOKUP_UPDATE,
    wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem word_abs_runtime_stmt_state:
  stmt_state_rel word_abs_runtime_unit.cu_context word_abs_runtime_func
    word_abs_runtime_frame_cenv word_abs_runtime_cx word_abs_runtime_es
    word_abs_runtime_s0
Proof
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  simp[word_abs_runtime_state, word_abs_runtime_alloca_inv,
    word_abs_runtime_alloca_room, word_abs_runtime_fmp_room] >>
  conj_tac
  >- CONV_TAC (computeLib.RESTR_EVAL_CONV
       [``word_abs_runtime_func``, ``function_selector``, ``calldata_method_id``,
        ``vyper_to_abi_types``]) >>
  conj_tac
  >- (CONV_TAC (computeLib.RESTR_EVAL_CONV
       [``word_abs_runtime_func``, ``function_selector``, ``calldata_method_id``,
        ``vyper_to_abi_types``]) >> simp[]) >>
  metis_tac[word_abs_runtime_alloca_sizes]
QED

Theorem word_abs_runtime_no_dalloca:
  ~ctx_has_dalloca word_abs_runtime_unit.cu_context
Proof
  simp[ptrDisciplineTheory.ctx_has_dalloca_def, word_abs_runtime_functions,
    listTheory.EXISTS_MEM] >>
  mp_tac word_abs_runtime_no_calls_scratch >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem word_abs_runtime_entry_fields:
  ~word_abs_runtime_frame_cenv.ce_is_ctor /\
  (!x sz. word_abs_runtime_frame_cenv.ce_return_buf = SOME (PtrVar (Var x) sz)
    ==> not_fresh_at word_abs_runtime_sa x) /\
  (!x sz. word_abs_runtime_frame_cenv.ce_return_pc = SOME (PtrVar (Var x) sz)
    ==> not_fresh_at word_abs_runtime_sa x) /\
  ~word_abs_runtime_s0.vs_halted /\
  word_abs_runtime_s0.vs_current_bb = word_abs_runtime_sa.cs_current_bb /\
  word_abs_runtime_s0.vs_inst_idx = LENGTH word_abs_runtime_sa.cs_current_insts
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_abs_runtime_func``, ``function_selector``, ``calldata_method_id``,
     ``vyper_to_abi_types``]) >> simp[] >>
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
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
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

Theorem word_abs_runtime_frame:
  FLOOKUP G "%11" = SOME (0,32) ==>
  lower_value compile_expr word_abs_runtime_frame_cenv (BaseT (IntT 256))
    word_abs_runtime_expr word_abs_runtime_sa = (Var "%22",word_abs_runtime_sb) /\
  fn_has_code word_abs_runtime_sa word_abs_runtime_sb word_abs_runtime_func /\
  fn_inst_ids_distinct word_abs_runtime_func /\
  local_ptrs_reserved word_abs_runtime_frame_cenv word_abs_runtime_sa /\
  ~ctx_has_dalloca word_abs_runtime_unit.cu_context /\
  ~word_abs_runtime_frame_cenv.ce_is_ctor /\
  (!x sz. word_abs_runtime_frame_cenv.ce_return_buf = SOME (PtrVar (Var x) sz)
    ==> not_fresh_at word_abs_runtime_sa x) /\
  (!x sz. word_abs_runtime_frame_cenv.ce_return_pc = SOME (PtrVar (Var x) sz)
    ==> not_fresh_at word_abs_runtime_sa x) /\
  gas_admissible (bind (eval_expr word_abs_runtime_cx word_abs_runtime_expr)
    (read_result word_abs_runtime_cx)) expr_res_ok word_abs_runtime_es /\
  stmt_state_rel word_abs_runtime_unit.cu_context word_abs_runtime_func
    word_abs_runtime_frame_cenv word_abs_runtime_cx word_abs_runtime_es
    word_abs_runtime_s0 /\
  ghost_inv NONE word_abs_runtime_frame_cenv word_abs_runtime_cx
    word_abs_runtime_es G entry_taint word_abs_runtime_s0 /\
  ~word_abs_runtime_s0.vs_halted /\
  word_abs_runtime_s0.vs_current_bb = word_abs_runtime_sa.cs_current_bb /\
  word_abs_runtime_s0.vs_inst_idx = LENGTH word_abs_runtime_sa.cs_current_insts
Proof
  strip_tac >>
  mp_tac word_abs_runtime_entry_fields >> mp_tac word_abs_runtime_code >>
  simp[word_abs_runtime_compile, word_abs_runtime_local_reserved,
    word_abs_runtime_no_dalloca, word_abs_runtime_stmt_state,
    word_abs_runtime_ghost] >>
  metis_tac[word_abs_runtime_gas_admissible]
QED
