Theory bodyPtrBopInMachineConditions
Ancestors
  bodyPtrBopInMachineFrame bodyPtrBopInCodeInventory
  bodyPtrBopInJointSource bodyPtrBopInActualSuffix bodyPtrBopInSourceFrame
  bodyPtrBopInLiveSourceFrame bodyPtrDefs gasContext exprSimDefs
  exprSimHypsDefs exprLoweringProps compileEnv loweringStateRelDefs compileVyper context venomState
  vyperInterpreter vyperState vyperContext finite_map bodyPtrBopInLocalSuffix

Theorem joint_membership_gas_admissible:
  gas_admissible (eval_expr joint_cx local_membership_fixture)
    expr_vv_res_ok joint_es
Proof
  simp[gas_admissible_def, local_membership_fixture_def,
       vyperInterpreterTheory.evaluate_def, bind_def, return_def,
       ignore_bind_def, read_result_def, type_check_def, assert_def,
       get_scopes_def, get_accounts_def, builtin_args_length_ok_def,
       vyperValueTheory.compatible_bound_def, vyperASTTheory.expr_type_def,
       joint_es_def, probe_es_def, probe_make_array_builtin,
       probe_in_builtin, lookup_scopes_def, read_place_def,
       read_memory_path_def, lift_option_type_def, lift_sum_def,
       evaluate_subscripts_def, FLOOKUP_UPDATE, expr_vv_res_ok_def]
QED

Theorem joint_cenv_frame_fields:
  ~joint_cenv.ce_is_ctor /\ joint_cenv.ce_return_buf = NONE /\
  joint_cenv.ce_return_pc = NONE /\ joint_cenv.ce_imm_alloca = NONE /\
  joint_cenv.ce_vars = FEMPTY |+ ("x",PtrVar (Var "%10") 64) |+
    ("y",PtrVar (Var "%13") 64)
Proof
  EVAL_TAC
QED

Theorem actual_suffix_frame_fields:
  (actual_suffix_start sel).cs_next_var = 14 /\
  (actual_suffix_start sel).cs_current_bb = "fn_probe"
Proof
  EVAL_TAC
QED

Theorem joint_machine_code_conditions:
  local_ptrs_reserved joint_cenv (actual_suffix_start equality_selector) /\
  ~joint_cenv.ce_is_ctor /\
  (!x sz. joint_cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at (actual_suffix_start equality_selector) x) /\
  (!x sz. joint_cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at (actual_suffix_start equality_selector) x) /\
  ~joint_machine.vs_halted /\
  joint_machine.vs_current_bb =
    (actual_suffix_start equality_selector).cs_current_bb /\
  joint_machine.vs_inst_idx =
    LENGTH (actual_suffix_start equality_selector).cs_current_insts
Proof
  simp[local_ptrs_reserved_def, joint_cenv_frame_fields,
       joint_machine_def, init_venom_state_def, actual_suffix_frame_fields,
       FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rewrite_tac[not_fresh_at_def, actual_suffix_frame_fields] >>
  `"%13" = STRING #"%" (toString (13:num))` by EVAL_TAC >>
  `"%10" = STRING #"%" (toString (10:num))` by EVAL_TAC >>
  asm_rewrite_tac[] >> simp[ASCIInumbersTheory.toString_11]
QED

Theorem joint_membership_compilation:
  compile_expr joint_cenv (BaseT BoolT) local_membership_fixture
    (actual_suffix_start equality_selector) =
    (StackValue (BaseT BoolT) (Var "%14"),actual_suffix_end equality_selector)
Proof
  simp[joint_cenv_def, actual_membership_suffix]
QED

(* The exact antecedent of expr_vv_sim_ptr at the one joint witness. *)
Theorem joint_membership_pointer_antecedents:
  compile_expr joint_cenv (BaseT BoolT) local_membership_fixture
    (actual_suffix_start equality_selector) =
    (StackValue (BaseT BoolT) (Var "%14"),actual_suffix_end equality_selector) /\
  fn_has_code (actual_suffix_start equality_selector)
    (actual_suffix_end equality_selector) (equality_runtime_function equality_selector) /\
  fn_inst_ids_distinct (equality_runtime_function equality_selector) /\
  local_ptrs_reserved joint_cenv (actual_suffix_start equality_selector) /\
  ~ctx_has_dalloca (equality_runtime_context equality_selector) /\
  ~joint_cenv.ce_is_ctor /\
  (!x sz. joint_cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at (actual_suffix_start equality_selector) x) /\
  (!x sz. joint_cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at (actual_suffix_start equality_selector) x) /\
  gas_admissible (eval_expr joint_cx local_membership_fixture) expr_vv_res_ok joint_es /\
  stmt_state_rel (equality_runtime_context equality_selector)
    (equality_runtime_function equality_selector) joint_cenv joint_cx joint_es joint_machine /\
  ghost_inv NONE joint_cenv joint_cx joint_es joint_provenance entry_taint joint_machine /\
  ~joint_machine.vs_halted /\
  joint_machine.vs_current_bb = (actual_suffix_start equality_selector).cs_current_bb /\
  joint_machine.vs_inst_idx = LENGTH (actual_suffix_start equality_selector).cs_current_insts
Proof
  simp[joint_membership_compilation, actual_membership_contained,
       equality_runtime_ids_distinct, equality_runtime_no_dalloca,
       joint_machine_code_conditions, joint_membership_gas_admissible,
       joint_machine_stmt_state_rel, joint_machine_ghost, joint_cenv_frame_fields]
QED
