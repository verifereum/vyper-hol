(* Joint-premise audit for the scalar-code fixture. *)
Theory immutableDeployLocalPremiseProbe
Ancestors
  immutableDeployLocalBackingProbe immutableDeployLocalCodeProbe
  immutableDeployEmptyValid immutableDeployEmptyStacked immutableDeployEmptyDeployment
  bodySim exprSimHypsDefs stmtSimDefs typedCopyMetadata vyperContext
  exprSimMain exprSimSource

Theorem local_probe_lowering_unit:
  lower_vyper_deploy_unit local_probe_tops empty_immutable_policy [] =
    SOME local_probe_unit
Proof
  mp_tac local_probe_lowering_succeeds >>
  Cases_on `lower_vyper_deploy_unit local_probe_tops empty_immutable_policy []` >>
  simp[local_probe_unit_def]
QED

Theorem local_probe_context_metadata:
  local_probe_cx.in_deploy /\
  get_module_code local_probe_cx NONE = SOME local_probe_tops /\
  get_tenv local_probe_cx = type_env local_probe_tops /\
  (!src ts. get_module_code local_probe_cx src = SOME ts ==> src = NONE)
Proof
  simp[local_probe_cx_def, empty_immutable_valid_cx_def,
       empty_immutable_stacked_cx_def, empty_immutable_cx_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def] >> EVAL_TAC >> simp[]
QED


Theorem stmt_env_environment_projection:
  !ce lc ty st sa.
    FST (stmt_env ce lc ty st sa) = FST (declare_stmt_local ce st sa)
Proof
  rpt gen_tac >>
  simp[loweringPostsTheory.stmt_env_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem local_probe_real_ce_declaration:
  local_probe_real_ce =
    FST (declare_local local_probe_ce "x" (BaseT (UintT 256)) assigned_immutable_sa)
Proof
  simp[local_probe_real_ce_def, local_probe_decl_result_def,
       stmt_env_environment_projection, local_probe_decl_def,
       stmtLoweringTheory.declare_stmt_local_def]
QED

Theorem local_probe_real_ce_shape:
  local_probe_real_ce = local_probe_ce with
    <|ce_var_type updated_by ("x" =+ SOME (BaseT (UintT 256)));
      ce_vars updated_by (\m. m |+ ("x",PtrVar (Var "%1") 32))|>
Proof
  rewrite_tac[local_probe_real_ce_declaration, stmtLoweringTheory.declare_local_def] >>
  `local_probe_ce.ce_alloca_locals` by EVAL_TAC >>
  `type_memory_bytes local_probe_ce (BaseT (UintT 256)) = 32` by EVAL_TAC >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_var_def] >>
  EVAL_TAC >> simp[]
QED

Theorem local_probe_body_inv:
  body_inv local_probe_tops local_probe_unit.cu_context
    local_probe_empty_ce local_probe_cx
Proof
  simp[body_inv_def, local_probe_context_metadata,
       local_probe_empty_ce_def, local_probe_real_ce_shape] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac
  >- (qexistsl [`empty_immutable_policy`, `local_probe_unit`] >>
      conj_tac
      >- (qexists `[]` >> simp[local_probe_lowering_unit]) >> EVAL_TAC) >>
  simp[local_probe_ce_def,
       compileVyperTheory.build_compile_env_ce_func_ids,
       compileVyperTheory.build_compile_env_ce_func_param_types,
       compileVyperTheory.build_compile_env_ce_func_info,
       compileVyperTheory.build_compile_env_ce_func_return_type] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac
  >- (irule typedCopyMetadataTheory.build_compile_env_struct_metadata_acyclic >>
      EVAL_TAC >> simp[]) >>
  simp[compileVyperTheory.build_compile_env_def, cenv_module_pins_def,
       compileVyperTheory.build_flag_info_def, compileVyperTheory.allocate_args_def] >>
  EVAL_TAC >> simp[]
QED

Definition local_probe_env_def:
  local_probe_env = empty_immutable_env with
    <|type_defs := type_env local_probe_tops;
      var_types := FEMPTY |+ ("x",StructT (NONE,"Empty"));
      var_assignable := FEMPTY |+ ("x",T)|>
End

Definition local_probe_es_def:
  local_probe_es = empty_immutable_es with scopes :=
    [FEMPTY |+ ("x",<|assignable := T; type := StructTV [];
                      value := StructV []; popped := []|>)]
End

Theorem local_probe_target_typing:
  supported_immutable_type local_probe_tops (NONE,"dst") =
      SOME (StructT (NONE,"Empty")) /\
  type_place_target local_probe_env (TopLevelNameTarget (NONE,"dst")) =
      SOME (Type (StructT (NONE,"Empty"))) /\
  type_widens_to local_probe_env.type_defs (StructT (NONE,"Empty"))
      (StructT (NONE,"Empty")) /\
  well_typed_expr local_probe_env (Name (StructT (NONE,"Empty")) "x")
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem local_probe_env_consistent:
  env_consistent local_probe_env local_probe_cx local_probe_es
Proof
  simp[vyperTypeInvariantsTheory.env_consistent_def] >> conj_tac
  >- (EVAL_TAC >>
      simp[vyperInterpreterTheory.lookup_function_def,
           vyperTypeContractTheory.function_live_def,
           vyperStateTheory.lookup_flag_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE,
      vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem local_probe_state_typed:
  state_well_typed local_probe_es /\
  accounts_well_typed local_probe_es.accounts /\
  context_well_typed local_probe_cx
Proof
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

Theorem local_probe_sim_inv:
  expr_sim_inv local_probe_empty_ce local_probe_cx local_probe_env local_probe_es
Proof
  simp[expr_sim_inv_def, local_probe_env_consistent,
       local_probe_state_typed, local_probe_functions_typed] >>
  simp[local_probe_env_def, local_probe_empty_ce_def, local_probe_real_ce_shape] >>
  conj_tac >- (rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
    EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- (rpt strip_tac >>
    drule (cj 4 local_probe_context_metadata) >> strip_tac >>
    gvs[local_probe_context_metadata] >>
    qpat_x_assum `lookup_flag _ _ = SOME _` mp_tac >>
    simp[local_probe_tops_def, vyperStateTheory.lookup_flag_def]) >>
  conj_tac >- (simp[local_probe_context_metadata] >> EVAL_TAC >>
    rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- simp[local_probe_ce_def, compileVyperTheory.build_compile_env_def,
    local_probe_context_metadata, compileVyperTheory.build_flag_info_def,
    compileVyperTheory.allocate_args_def, local_probe_tops_def] >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[AllCaseEqs(), vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    drule (cj 4 local_probe_context_metadata) >> strip_tac >>
    gvs[local_probe_context_metadata] >>
    qpat_x_assum `find_var_decl_by_name _ _ = SOME _` mp_tac >>
    simp[local_probe_tops_def, vyperStateTheory.find_var_decl_by_name_def] >>
    rpt strip_tac >> gvs[AllCaseEqs()]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    gvs[immutableDeployEmptySourceTheory.empty_immutable_env_def, finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC) >>
  conj_tac >- (rpt strip_tac >>
    gvs[immutableDeployEmptySourceTheory.empty_immutable_env_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
    EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
    simp[wordsTheory.dimword_def, valueEncodingTheory.type_memory_size_def]) >>
  EVAL_TAC >> rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  EVAL_TAC >> simp[compileEnvTheory.regions_disjoint_def,
                   valueEncodingTheory.type_memory_size_def] >>
  gvs[immutableDeployEmptyProbeTheory.empty_struct_evaluated_probe]
QED

Theorem local_probe_calls_safe:
  call_evaluation_safe local_probe_cx []
Proof
  simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexists `[]` >> EVAL_TAC >> simp[] >> conj_tac
  >- (simp[relationTheory.irreflexive_def] >>
      metis_tac[relationTheory.TC_CASES1,
        vyperTypeCallGraphSoundnessTheory.call_edge_rel_def, listTheory.MEM]) >>
  simp[vyperInterpreterTheory.lookup_function_def] >>
  rpt gen_tac >> Cases_on `fn = "__init__"` >>
  simp[vyperTypeCallGraphTheory.int_calls_expr_def,
       vyperTypeCallGraphTheory.int_calls_stmt_def,
       vyperTypeCallGraphTheory.int_calls_atarget_def]
QED

Theorem local_probe_body_pre:
  expr_body_pre local_probe_empty_ce local_probe_cx local_probe_env
    (Name (StructT (NONE,"Empty")) "x") local_probe_es
Proof
  simp[expr_body_pre_def, local_probe_sim_inv,
       cj 4 local_probe_target_typing,
       vyperTypeCallGraphTheory.int_calls_expr_def, local_probe_calls_safe] >>
  EVAL_TAC >> simp[]
QED

Theorem local_probe_vv_sim:
  !ctx func ty.
    expr_vv_sim ctx func local_probe_empty_ce local_probe_cx ty
      (Name (StructT (NONE,"Empty")) "x") local_probe_es
Proof
  rpt gen_tac >> irule compile_expr_vv_sim >>
  qexists `local_probe_env` >>
  simp[expr_sim_pre_body, local_probe_body_pre,
       vyperTypeCallGraphTheory.int_calls_expr_def]
QED

Definition local_probe_entry_def:
  local_probe_entry = local_probe_backing_state
    ((init_venom_state "__deploy") with
      <|vs_memory := REPLICATE 31 0w ++ [1w] ++ REPLICATE 128 0w;
        vs_inst_idx := 3; vs_labels := FEMPTY |+ ("runtime_begin",0w);
        vs_block_ctx := empty_block_context with bc_number := 1w|>)
End


Theorem local_probe_one_bytes:
  byte$word_to_bytes_aux 32 (1w : bytes32) T =
    REPLICATE 31 (0w : word8) ++ [1w]
Proof
  simp[byteTheory.word_to_bytes_aux_compute, byteTheory.get_byte_def,
       byteTheory.byte_index_def, fcpLib.INDEX_CONV ``dimindex(:256)``,
       wordsTheory.dimword_def] >>
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem local_probe_entry_state_rel:
  state_rel local_probe_fn local_probe_empty_ce local_probe_cx
    local_probe_es local_probe_entry
Proof
  rewrite_tac[compileEnvTheory.state_rel_def] >>
  conj_tac
  >- (simp[local_probe_es_def, immutableDeployEmptySourceTheory.empty_immutable_es_def,
           local_probe_entry_def] >>
      irule local_probe_empty_local_ptrs >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
    EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
    EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
    EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
    simp[local_probe_one_bytes] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Theorem local_probe_no_calls:
  !g. ~TC (fn_directly_calls local_probe_unit.cu_context) local_probe_fn.fn_name g
Proof
  `!g. ~fn_directly_calls local_probe_unit.cu_context local_probe_fn.fn_name g` by
    (simp[fcgDefsTheory.fn_directly_calls_def, local_probe_fn_member] >>
     rewrite_tac[local_probe_fn_shape] >> EVAL_TAC >>
     rpt strip_tac >> gvs[] >> rpt strip_tac >> gvs[]) >>
  metis_tac[relationTheory.TC_CASES1]
QED

Theorem local_probe_entry_stmt_state_rel:
  stmt_state_rel local_probe_unit.cu_context local_probe_fn local_probe_empty_ce
    local_probe_cx local_probe_es local_probe_entry
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, local_probe_entry_state_rel] >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[exprLoweringPropsTheory.alloca_room_def,
    local_probe_fn_member, local_probe_no_calls] >> EVAL_TAC >>
    simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  conj_tac >- (simp[exprLoweringPropsTheory.fmp_room_def, local_probe_no_calls,
    local_probe_fn_shape] >> EVAL_TAC) >>
  conj_tac >- (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
    EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >>
    simp[compileEnvTheory.regions_disjoint_def,
         valueEncodingTheory.type_memory_size_def] >>
    rpt strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def,
        immutableDeployEmptyProbeTheory.empty_struct_evaluated_probe,
        finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
    EVAL_TAC >> simp[venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  rewrite_tac[local_probe_fn_shape] >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem local_probe_fn_distinct:
  fn_inst_ids_distinct local_probe_fn
Proof
  rewrite_tac[local_probe_fn_shape] >> EVAL_TAC
QED

Theorem local_probe_entry_env_fields:
  local_probe_empty_ce.ce_vars = FEMPTY |+ ("x",PtrVar (Var "%1") 0) /\
  local_probe_empty_ce.ce_imm_alloca = SOME (Var "%0") /\
  local_probe_empty_ce.ce_return_pc = NONE
Proof
  simp[local_probe_empty_ce_def, local_probe_real_ce_shape, local_probe_ce_def,
       compileVyperTheory.build_compile_env_def,
       compileVyperTheory.allocate_args_def] >>
  Cases_on `build_flag_info local_probe_tops (K (K 0)) (K 0)` >> simp[]
QED

Theorem local_probe_entry_reserved:
  local_ptrs_reserved local_probe_empty_ce local_probe_sa
Proof
  simp[compileEnvTheory.local_ptrs_reserved_def, local_probe_entry_env_fields,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  simp[compileEnvTheory.not_fresh_at_def, local_probe_sa_shape] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `toString n = _` (mp_tac o AP_TERM ``toNum``) >>
  simp[ASCIInumbersTheory.toNum_toString] >> EVAL_TAC >> simp[]
QED

Theorem local_probe_entry_control:
  ret_pc_ok local_probe_empty_ce local_probe_sa local_probe_entry /\
  ~block_is_terminated local_probe_sa /\
  ~local_probe_entry.vs_halted /\
  local_probe_entry.vs_current_bb = local_probe_sa.cs_current_bb /\
  local_probe_entry.vs_inst_idx = LENGTH local_probe_sa.cs_current_insts
Proof
  conj_tac >- simp[loweringPostsTheory.ret_pc_ok_def, local_probe_entry_env_fields] >>
  rewrite_tac[local_probe_sa_shape] >> EVAL_TAC
QED

Theorem local_probe_gas_admissible:
  gas_admissible (eval_stmt local_probe_cx local_probe_empty_stmt)
    (stmt_res_ok NoLoop) local_probe_es
Proof
  rewrite_tac[gasContextTheory.gas_admissible_def] >>
  rpt gen_tac >> EVAL_TAC >> rpt strip_tac >> gvs[] >>
  simp[stmt_res_ok_def]
QED

Theorem local_probe_joint_premises:
  body_inv local_probe_tops local_probe_unit.cu_context
    local_probe_empty_ce local_probe_cx /\ local_probe_cx.in_deploy /\
  supported_immutable_type local_probe_tops (NONE,"dst") = SOME (StructT (NONE,"Empty")) /\
  type_place_target local_probe_env (TopLevelNameTarget (NONE,"dst")) =
    SOME (Type (StructT (NONE,"Empty"))) /\
  type_widens_to local_probe_env.type_defs
    (expr_type (Name (StructT (NONE,"Empty")) "x")) (StructT (NONE,"Empty")) /\
  expr_vv_sim local_probe_unit.cu_context local_probe_fn local_probe_empty_ce
    local_probe_cx (expr_type (Name (StructT (NONE,"Empty")) "x"))
    (Name (StructT (NONE,"Empty")) "x") local_probe_es /\
  expr_body_pre local_probe_empty_ce local_probe_cx local_probe_env
    (Name (StructT (NONE,"Empty")) "x") local_probe_es /\
  fn_has_code local_probe_sa
    (SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa))
    local_probe_fn /\
  fn_inst_ids_distinct local_probe_fn /\
  local_ptrs_reserved local_probe_empty_ce local_probe_sa /\
  ret_pc_ok local_probe_empty_ce local_probe_sa local_probe_entry /\
  ~block_is_terminated local_probe_sa /\
  gas_admissible (eval_stmt local_probe_cx local_probe_empty_stmt)
    (stmt_res_ok NoLoop) local_probe_es /\
  stmt_state_rel local_probe_unit.cu_context local_probe_fn local_probe_empty_ce
    local_probe_cx local_probe_es local_probe_entry /\
  ~local_probe_entry.vs_halted /\
  local_probe_entry.vs_current_bb = local_probe_sa.cs_current_bb /\
  local_probe_entry.vs_inst_idx = LENGTH local_probe_sa.cs_current_insts
Proof
  simp[local_probe_body_inv, local_probe_context_metadata,
       local_probe_target_typing, vyperASTTheory.expr_type_def,
       local_probe_vv_sim, local_probe_body_pre, local_probe_empty_fragment_code,
       local_probe_fn_distinct, local_probe_entry_reserved, local_probe_entry_control,
       local_probe_gas_admissible, local_probe_entry_stmt_state_rel]
QED
