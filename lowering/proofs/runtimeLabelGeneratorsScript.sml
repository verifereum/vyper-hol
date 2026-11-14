(* Runtime orchestration consumes body certificates at the proof interface. *)
Theory runtimeLabelGenerators
Ancestors
  runtimeLabelExprCallbacks runtimeLabelPrimitives runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
  moduleLowering stmtLowering compileEnv context emitHelper venomInst list
  loweringShapeDefs combinatorics alist

Theorem rb_compile_selector_checks:
  !sels. rb_operand_ok mid /\
    EVERY (\(sel,lbl). rb_operand_ok (Label lbl)) sels ==>
    rb_step (K T) (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def, rb_step_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_selector_checks_def] >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- gvs[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_compile_selector_dispatch_linear:
  EVERY (\(sel,lbl). rb_operand_ok (Label lbl)) sels /\
  rb_operand_ok (Label fallback) ==>
  rb_step (K T) (compile_selector_dispatch_linear sels fallback)
Proof
  strip_tac >> rewrite_tac[compile_selector_dispatch_linear_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_selector_checks, rb_emit_inst]
QED

Theorem rb_compile_sparse_bucket_search:
  !sels. rb_operand_ok mid /\ rb_operand_ok (Label fallback) /\
    EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels ==>
    rb_step (K T) (compile_sparse_bucket_search mid sels fallback)
Proof
  Induct >> simp[compile_sparse_bucket_search_def, rb_emit_inst] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_sparse_bucket_search_def] >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_alloc_bucket_labels:
  !n. rb_step (EVERY (\l. rb_operand_ok (Label l))) (alloc_bucket_labels n)
Proof
  completeInduct_on `n` >> Cases_on `n` >>
  simp[Once alloc_bucket_labels_def, rb_step_return] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY (\l. rb_operand_ok (Label l))` >>
  BETA_TAC >> reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_step_return >> gvs[]
QED

Theorem rb_group_into_buckets:
  !sels n. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels ==>
  EVERY (\b. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) (SND b))
    (group_into_buckets sels n)
Proof
  Induct >- simp[group_into_buckets_def] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [group_into_buckets_def, LET_THM] >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  rw[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem rb_create_bucket_blocks:
  !mid lbls buckets fallback.
    rb_operand_ok mid /\ rb_operand_ok (Label fallback) /\
    EVERY (\b. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) (SND b)) buckets ==>
    rb_step (K T) (create_bucket_blocks mid lbls buckets fallback)
Proof
  ho_match_mp_tac create_bucket_blocks_ind >> rpt strip_tac >>
  simp[Once create_bucket_blocks_def, rb_step_return] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- gvs[rb_compile_sparse_bucket_search] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_emit_data_section:
  rb_step (K T) (emit_data_section label)
Proof
  simp[rb_step_def, rb_state_ok_def, emit_data_section_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_emit_data_item:
  rb_step (K T) (emit_data_item item)
Proof
  rw[rb_step_def, rb_state_ok_def, emit_data_item_def,
       state_insts_def, all_blocks_def] >>
  Cases_on `st.cs_data_sections` >> gvs[]
QED

Theorem rb_data_label_fold:
  !labels. rb_step (K T)
    (FOLDL (\m lbl. comp_ignore_bind m (emit_data_item (DataLabel lbl)))
      (comp_return ()) labels)
Proof
  Induct using SNOC_INDUCT >> simp[FOLDL_SNOC, rb_step_return] >>
  gen_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_data_item]
QED

Theorem rb_sparse_target_list:
  EVERY (\l. rb_operand_ok (Label l)) labels /\
  rb_operand_ok (Label fallback) ==>
  EVERY (\l. rb_operand_ok (Label l))
    (GENLIST (\i. case ALOOKUP (MAP2 (\(bid,items) lbl. (bid,lbl)) buckets labels) i of
       SOME lbl => lbl | NONE => fallback) n)
Proof
  strip_tac >> simp[EVERY_GENLIST] >> gen_tac >> strip_tac >>
  CASE_TAC >> gvs[] >>
  drule alistTheory.ALOOKUP_MEM >>
  disch_then (mp_tac o MATCH_MP combinatoricsTheory.MEM_MAP2) >>
  simp[pairTheory.EXISTS_PROD] >> rpt strip_tac >> gvs[] >>
  gvs[EVERY_MEM]
QED

Theorem rb_compile_selector_dispatch_sparse:
  EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels /\
  rb_operand_ok (Label fallback) ==>
  rb_step (K T) (compile_selector_dispatch_sparse sels bucket_count fallback)
Proof
  strip_tac >> rewrite_tac[compile_selector_dispatch_sparse_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  IF_CASES_TAC
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
      >- (irule rb_compile_selector_checks >>
          gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD]) >>
      simp[rb_emit_inst]) >>
  irule rb_step_bind >> qexists_tac `EVERY (\l. rb_operand_ok (Label l))` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_alloc_bucket_labels] >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_return >> BETA_TAC) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule rb_emit_inst >> simp[EVERY_MAP] >>
      irule (SRULE [] rb_sparse_target_list) >> gvs[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_data_section] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_data_label_fold] >>
  irule rb_create_bucket_blocks >> simp[rb_group_into_buckets]
QED

Theorem rb_compile_abi_arg_ptr_guard:
  rb_operand_ok src /\ rb_operand_ok parent ==>
  rb_step (K T) (compile_abi_arg_ptr_guard opc src parent)
Proof
  strip_tac >> rewrite_tac[compile_abi_arg_ptr_guard_def] >>
  IF_CASES_TAC >> simp[rb_step_return] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  simp[rb_emit_void]
QED

Theorem rb_var_location_decode_operand:
  rb_location_ok loc /\ var_location_decode_operand loc = SOME dst ==>
  rb_operand_ok dst
Proof
  Cases_on `loc` >> simp[var_location_decode_operand_def, rb_location_ok_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem rb_compile_entry_checks:
  rb_step (K T) (compile_entry_checks min_cds payable)
Proof
  rewrite_tac[compile_entry_checks_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  IF_CASES_TAC >> simp[rb_step_return] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  simp[rb_emit_void]
QED

Theorem rb_compile_guarded_body:
  rb_stmt_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_guarded_body ce nr key trans view stmts ret)
Proof
  strip_tac >> rewrite_tac[compile_guarded_body_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_lock, rb_step_return]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- gvs[rb_stmt_contract_def, rb_loop_ok_def] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
  Cases_on `ret` >> simp[rb_emit_inst]
QED

Theorem rb_compile_fallback_body:
  rb_stmt_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_fallback_body ce payable nr key trans view stmts ret)
Proof
  strip_tac >> rewrite_tac[compile_fallback_body_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  simp[rb_compile_guarded_body]
QED

Theorem rb_compile_internal_param_decls:
  !params idx. rb_step (\r. EVERY (\(name,stk,op). rb_operand_ok op) (FST r))
    (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, rb_step_return] >>
  PairCases >> gen_tac >> rewrite_tac[compile_internal_param_decls_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >>
  qexists_tac `\r. EVERY (\(name,stk,op). rb_operand_ok op) (FST r)` >>
  BETA_TAC >> reverse conj_tac >- simp[] >>
  gen_tac >> strip_tac >> irule rb_step_return >> gvs[]
QED

Theorem rb_materialize_internal_params:
  !params ce. rb_env_ok ce /\
    EVERY (\(name,stk,op). rb_operand_ok op) params ==>
    rb_step rb_env_ok (materialize_internal_params ce params)
Proof
  Induct >> simp[materialize_internal_params_def, rb_step_return] >>
  PairCases >> gen_tac >> strip_tac >>
  rewrite_tac[materialize_internal_params_def] >> BETA_TAC >>
  reverse (Cases_on `h1`) >> simp[]
  >- (first_x_assum irule >> gvs[rb_env_bind_local, rb_location_ok_def]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `_ = SOME loc` >> Cases_on `loc` >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- gvs[rb_emit_void] >>
  first_x_assum irule >> gvs[rb_env_bind_local, rb_location_ok_def]
QED

Theorem rb_compile_create_kwarg_allocas:
  !specs. rb_step (EVERY (\(name,ptr,ty,e). rb_operand_ok ptr))
    (compile_create_kwarg_allocas ce specs)
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, rb_step_return] >>
  PairCases >> rewrite_tac[compile_create_kwarg_allocas_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY (\(name,ptr,ty,e). rb_operand_ok ptr)` >>
  BETA_TAC >> reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_return >> gvs[rb_buffer_ok_def]
QED

Theorem rb_compile_register_kwarg_vars:
  !kwvars ce. rb_env_ok ce /\
    EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars ==>
    rb_env_ok (compile_register_kwarg_vars ce kwvars)
Proof
  Induct >> simp[compile_register_kwarg_vars_def] >>
  PairCases >> gen_tac >> strip_tac >>
  rewrite_tac[compile_register_kwarg_vars_def] >>
  first_x_assum irule >> gvs[rb_env_ok_def, rb_location_ok_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs(), rb_location_ok_def] >> metis_tac[]
QED

Theorem rb_compile_decode_args:
  !args ce offset opc hi base_adj. rb_env_ok ce /\ rb_operand_ok hi ==>
    rb_step (K T) (compile_decode_args ce args offset opc hi base_adj)
Proof
  Induct >> simp[compile_decode_args_def, rb_step_return] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_decode_args_def] >> BETA_TAC >>
  Cases_on `h1`
  >- (simp[] >>
      ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_abi_clamp_basetype] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- (first_x_assum irule >> simp[]) >>
      Cases_on `FLOOKUP ce.ce_vars h0` >> simp[rb_step_return] >>
      rename1 `_ = SOME loc` >> Cases_on `var_location_decode_operand loc` >>
      simp[rb_step_return] >> irule rb_emit_void >> simp[] >>
      irule rb_var_location_decode_operand >> qexists_tac `loc` >>
      gvs[rb_env_ok_def] >> metis_tac[]) >>
  simp[] >> Cases_on `h2` >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `_ = SOME loc` >> Cases_on `var_location_decode_operand loc` >> simp[] >>
  rename1 `_ = SOME dst` >>
  `rb_operand_ok dst` by
    (irule rb_var_location_decode_operand >> qexists_tac `loc` >>
     gvs[rb_env_ok_def] >> metis_tac[]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac
  >- (ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_abi_arg_ptr_guard] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
      >- (irule (cj 1 rb_abi_decode) >> Cases_on `opc = CALLDATALOAD` >> simp[]) >>
      first_x_assum irule >> simp[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule (cj 1 rb_abi_decode) >> Cases_on `opc = CALLDATALOAD` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_register_positional_args:
  !args ce offset. rb_env_ok ce ==>
    rb_step rb_env_ok (compile_register_positional_args ce args offset)
Proof
  Induct >> simp[compile_register_positional_args_def, rb_step_return] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `_ = SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >> qx_gen_tac `buf` >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  `rb_env_ok (ce with ce_vars updated_by
    (\m. m |+ (h0,PtrVar buf.buf_operand x)))` by
      gvs[rb_env_bind_local, rb_buffer_ok_def, rb_location_ok_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_decode_args] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_init_kwargs:
  !kwvars ce offset num hi. rb_expr_contract /\ rb_env_ok ce /\
    EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars ==>
    rb_step (K T) (compile_init_kwargs ce kwvars offset num hi)
Proof
  Induct >> simp[compile_init_kwargs_def, rb_step_return] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_init_kwargs_def] >> BETA_TAC >> IF_CASES_TAC
  >- (simp_tac std_ss [LET_THM] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac
      >- (IF_CASES_TAC >> simp[rb_step_return] >>
          ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
          irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_abi_arg_ptr_guard, rb_step_return]) >>
      gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
      >- (irule (cj 1 rb_abi_decode) >> gvs[]) >>
      first_x_assum irule >> gvs[]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> gvs[rb_emit_void] >> IF_CASES_TAC >>
      gvs[rb_compile_store_bytestring, rb_emit_void]) >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_compile_entry_point_kwargs:
  rb_expr_contract /\ rb_env_ok ce /\
  EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars /\
  rb_operand_ok (Label common) ==>
  rb_step (K T) (compile_entry_point_kwargs ce kwvars offset num common)
Proof
  strip_tac >> rewrite_tac[compile_entry_point_kwargs_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_init_kwargs, rb_emit_inst]
QED

Theorem rb_compile_external_function_body:
  rb_stmt_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_external_function_body ce args nr key trans view stmts ret)
Proof
  strip_tac >> rewrite_tac[compile_external_function_body_def] >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  simp[rb_compile_register_positional_args, rb_compile_guarded_body]
QED

Theorem rb_compile_common_function_body:
  rb_stmt_contract /\ rb_env_ok ce /\
  EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars ==>
  rb_step (K T) (compile_common_function_body ce args kwvars nr key trans view stmts ret)
Proof
  strip_tac >> simp_tac std_ss [compile_common_function_body_def, LET_THM] >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  simp[rb_compile_register_positional_args, rb_compile_guarded_body,
       rb_compile_register_kwarg_vars]
QED

Theorem rb_compile_external_fn_bodies:
  !packages. rb_stmt_contract /\
    EVERY (\(lbl,ce,args,min_cds,pay,nr,key,trans,view,stmts,ret). rb_env_ok ce)
      packages ==> rb_step (K T) (compile_external_fn_bodies packages)
Proof
  Induct >> simp[compile_external_fn_bodies_def, rb_step_return] >>
  PairCases >> simp_tac std_ss [pairTheory.pair_case_thm] >> strip_tac >>
  rewrite_tac[compile_external_fn_bodies_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_entry_checks] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_external_function_body] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_group_entries:
  !entries. rb_expr_contract /\ rb_env_ok common.ec_env /\
    rb_operand_ok method_id /\ rb_operand_ok (Label common.ec_common_label) /\
    EVERY (\(sel,lbl,min_cds,k). rb_operand_ok (Label lbl)) entries /\
    EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars ==>
    rb_step (K T) (compile_group_entries method_id entries common kwvars offset)
Proof
  Induct >> simp[compile_group_entries_def, rb_step_return] >>
  PairCases >> simp_tac std_ss [pairTheory.pair_case_thm] >> strip_tac >>
  rewrite_tac[compile_group_entries_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_entry_checks] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_entry_point_kwargs] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_internal_function:
  rb_stmt_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_internal_function ce params has_buf nr key trans view
    F imm_len stmts ret)
Proof
  strip_tac >> rewrite_tac[compile_internal_function_def] >>
  irule rb_step_bind >>
  qexists_tac `\v. case v of NONE => T | SOME op => rb_operand_ok op` >>
  BETA_TAC >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
  qx_gen_tac `ret_buf` >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_step_bind >>
  qexists_tac `\r. EVERY (\(name,stk,op). rb_operand_ok op) (FST r)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_internal_param_decls] >>
  qx_gen_tac `decls` >> strip_tac >>
  ntac 2 (irule rb_bind_return >> BETA_TAC) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> qx_gen_tac `ret_pc` >> strip_tac >>
  simp_tac std_ss [] >> irule rb_bind_return >> BETA_TAC >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_env_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_materialize_internal_params >> simp[] >>
      Cases_on `ce.ce_return_buf`
      >- (Cases_on `ret_buf` >> gvs[rb_env_ok_def, rb_location_ok_def] >> metis_tac[]) >>
      rename1 `_ = SOME loc` >> Cases_on `loc` >> Cases_on `ret_buf` >>
      gvs[rb_env_ok_def, rb_location_ok_def] >> metis_tac[]) >>
  qx_gen_tac `env2` >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `ret` >> simp[rb_step_return] >> IF_CASES_TAC >>
      simp[rb_step_return] >> irule rb_step_ignore_bind >> simp[rb_step_return] >>
      qexists_tac `rb_buffer_ok` >> simp[rb_compile_alloc_buffer]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_lock, rb_step_return]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (gvs[rb_stmt_contract_def] >> first_x_assum irule >>
      simp[rb_loop_ok_def, rb_env_ok_def] >> gvs[rb_env_ok_def] >> metis_tac[]) >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac
  >- simp[rb_step_return] >> IF_CASES_TAC >> simp[rb_step_return] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
  Cases_on `ret` >> simp[rb_emit_inst]
QED

Theorem rb_compile_internal_fn_bodies:
  !packages. rb_stmt_contract /\
    EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,stmts,ret).
      rb_env_ok ce /\ ~ctor) packages ==>
    rb_step (K T) (compile_internal_fn_bodies packages)
Proof
  Induct >> simp[compile_internal_fn_bodies_def, rb_step_return] >>
  PairCases >> simp_tac std_ss [pairTheory.pair_case_thm] >> strip_tac >>
  rewrite_tac[compile_internal_fn_bodies_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- gvs[rb_compile_internal_function] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_fold_ignore:
  (!x. rb_step (K T) (action x)) ==>
  !xs. rb_step (K T)
    (FOLDL (\m x. comp_ignore_bind m (action x)) (comp_return ()) xs)
Proof
  strip_tac >> Induct using SNOC_INDUCT >>
  simp[FOLDL_SNOC, rb_step_return] >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[]
QED

Theorem rb_emit_dense_data_sections:
  !buckets. rb_step (K T) (emit_dense_data_sections buckets width info)
Proof
  Induct >> simp[emit_dense_data_sections_def, rb_step_return] >>
  gen_tac >> simp_tac std_ss [emit_dense_data_sections_def, LET_THM] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_data_section] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[] >>
  qmatch_goalsub_abbrev_tac `FOLDL action seed mids` >>
  qid_spec_tac `mids` >> Induct using SNOC_INDUCT >>
  simp[FOLDL_SNOC, Abbr `seed`] >- simp[rb_step_return] >>
  gen_tac >> simp_tac std_ss [Abbr `action`] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
  pairarg_tac >> asm_simp_tac std_ss [LET_THM] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_data_item] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_data_item]
QED

Theorem rb_compile_selector_dispatch_dense:
  EVERY (\l. rb_operand_ok (Label l)) labels /\
  rb_operand_ok (Label fallback) ==>
  rb_step (K T)
    (compile_selector_dispatch_dense sels bucket_count width buckets info labels fallback)
Proof
  strip_tac >> simp_tac std_ss [compile_selector_dispatch_dense_def, LET_THM] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  ntac 6 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  ntac 10 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  ntac 11 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  ntac 5 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- gvs[rb_emit_inst, EVERY_MAP] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_data_section] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[rb_emit_dense_data_sections] >>
  qmatch_goalsub_abbrev_tac `FOLDL action seed bs` >>
  qid_spec_tac `bs` >> Induct using SNOC_INDUCT >>
  simp[FOLDL_SNOC, Abbr `seed`] >- simp[rb_step_return] >>
  gen_tac >> simp_tac std_ss [Abbr `action`] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_data_item] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_data_item]
QED

Theorem compile_generate_runtime_no_runtime_begin:
  rb_expr_contract /\ rb_stmt_contract /\
  rb_runtime_inputs_ok selectors externals internals fallback ==>
  rb_step (K T) (compile_generate_runtime selectors externals internals fallback
    strategy bucket_count width buckets info)
Proof
  strip_tac >> simp_tac std_ss [compile_generate_runtime_def, LET_THM] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (gvs[rb_runtime_inputs_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
      Cases_on `strategy` >>
      simp[rb_compile_selector_dispatch_sparse, rb_compile_selector_dispatch_dense,
        rb_compile_selector_dispatch_linear, EVERY_MAP, EVERY_MEM,
        pairTheory.FORALL_PROD]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule rb_compile_external_fn_bodies >>
      gvs[rb_runtime_inputs_ok_def, EVERY_MEM, pairTheory.FORALL_PROD,
          rb_external_package_ok_def] >> metis_tac[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `fallback` >> simp[rb_emit_inst] >> PairCases_on `x` >> simp_tac std_ss [pairTheory.pair_case_thm] >>
      irule rb_compile_fallback_body >>
      gvs[rb_runtime_inputs_ok_def, rb_fallback_ok_def]) >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >> simp[rb_step_return] >>
  irule rb_compile_internal_fn_bodies >>
  gvs[rb_runtime_inputs_ok_def, EVERY_MEM, pairTheory.FORALL_PROD,
      rb_internal_package_ok_def] >> metis_tac[]
QED

Definition rb_job_ok_def:
  rb_job_ok (ExternalLegacyJob package) = rb_external_package_ok package /\
  rb_job_ok (ExternalCommonJob common kwvars) =
    (rb_env_ok common.ec_env /\
     EVERY (\(name,ptr,ty,e). rb_operand_ok ptr) kwvars)
End

Theorem rb_compile_external_groups:
  !groups. rb_expr_contract /\ rb_operand_ok mid /\ EVERY rb_group_ok groups ==>
    rb_step (EVERY rb_job_ok) (compile_external_groups mid groups)
Proof
  Induct >> simp[compile_external_groups_def, rb_step_return] >>
  Cases >> simp_tac std_ss [rb_group_ok_def] >> strip_tac
  >- (PairCases_on `p` >> gvs[rb_group_ok_def] >>
      rewrite_tac[compile_external_groups_def] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_selector_checks] >>
      irule rb_step_bind >> qexists_tac `EVERY rb_job_ok` >> BETA_TAC >>
      reverse conj_tac >- (first_x_assum irule >> simp[]) >>
      gen_tac >> strip_tac >> simp[rb_step_return, rb_job_ok_def]) >>
  rewrite_tac[compile_external_groups_def] >>
  irule rb_step_bind >> qexists_tac `EVERY (\(name,ptr,ty,e). rb_operand_ok ptr)` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_compile_create_kwarg_allocas] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- simp[rb_compile_group_entries] >>
  irule rb_step_bind >> qexists_tac `EVERY rb_job_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  gen_tac >> strip_tac >> simp[rb_step_return, rb_job_ok_def]
QED

Theorem rb_compile_external_jobs:
  !jobs. rb_stmt_contract /\ EVERY rb_job_ok jobs ==>
    rb_step (K T) (compile_external_jobs jobs)
Proof
  Induct >> simp[compile_external_jobs_def, rb_step_return] >>
  Cases >> simp_tac std_ss [rb_job_ok_def] >> strip_tac >>
  rewrite_tac[compile_external_jobs_def]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
      >- (irule rb_compile_external_fn_bodies >>
          PairCases_on `p` >> gvs[rb_external_package_ok_def]) >>
      first_x_assum irule >> simp[]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_common_function_body] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_group_dispatch_linear:
  rb_expr_contract /\ EVERY rb_group_ok groups /\
  rb_operand_ok (Label fallback) ==>
  rb_step (EVERY rb_job_ok) (compile_group_dispatch_linear groups fallback)
Proof
  strip_tac >> rewrite_tac[compile_group_dispatch_linear_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_step_bind >> qexists_tac `EVERY rb_job_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_external_groups] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]
QED

Theorem compile_generate_grouped_runtime_no_runtime_begin:
  rb_expr_contract /\ rb_stmt_contract /\
  rb_grouped_runtime_inputs_ok groups internals fallback ==>
  rb_step (K T) (compile_generate_grouped_runtime groups internals fallback)
Proof
  strip_tac >> rewrite_tac[compile_generate_grouped_runtime_def] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_job_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (irule rb_compile_group_dispatch_linear >> gvs[rb_grouped_runtime_inputs_ok_def]) >>
  qx_gen_tac `jobs` >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- simp[rb_compile_external_jobs] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `fallback` >> simp[rb_emit_inst] >> PairCases_on `x` >>
      simp_tac std_ss [pairTheory.pair_case_thm] >>
      irule rb_compile_fallback_body >>
      gvs[rb_grouped_runtime_inputs_ok_def, rb_fallback_ok_def]) >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >> simp[rb_step_return] >>
  irule rb_compile_internal_fn_bodies >>
  gvs[rb_grouped_runtime_inputs_ok_def, EVERY_MEM, pairTheory.FORALL_PROD,
      rb_internal_package_ok_def] >> metis_tac[]
QED
