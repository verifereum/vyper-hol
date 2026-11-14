(* Runtime orchestration consumes body certificates at the proof interface. *)
Theory runtimeLabelGenerators
Ancestors
  runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
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
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- gvs[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
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
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_ignore >> simp[rb_compile_selector_checks, rb_emit_inst]
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
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
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
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- gvs[rb_compile_sparse_bucket_search] >>
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
  gen_tac >> irule rb_ignore >> simp[rb_emit_data_item]
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
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  IF_CASES_TAC
  >- (irule rb_ignore >> conj_tac
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
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (irule rb_emit_inst >> simp[EVERY_MAP] >>
      irule (SRULE [] rb_sparse_target_list) >> gvs[]) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_data_section] >>
  irule rb_ignore >> conj_tac >- simp[rb_data_label_fold] >>
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
  irule rb_ignore >> conj_tac
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
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_lock, rb_step_return]) >>
  irule rb_ignore >> conj_tac
  >- gvs[rb_stmt_contract_def, rb_loop_ok_def] >>
  irule rb_step_bind >> qexists_tac `K T` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_step_def, comp_get_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return] >>
  irule rb_ignore >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
  Cases_on `ret` >> simp[rb_emit_inst]
QED

Theorem rb_compile_fallback_body:
  rb_stmt_contract /\ rb_env_ok ce ==>
  rb_step (K T) (compile_fallback_body ce payable nr key trans view stmts ret)
Proof
  strip_tac >> rewrite_tac[compile_fallback_body_def] >>
  irule rb_ignore >> conj_tac
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
  irule rb_ignore >> conj_tac >- gvs[rb_emit_void] >>
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
