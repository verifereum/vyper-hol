Theory groupedInternalLabels
Ancestors
  externalEntryShape loweringShapeRules compileUnit compileVyper vyperCompiler
  moduleLowering compileEnv emitHelper exprLowering loweringShapeDefs list
  entryInternalAppend fragExec
Libs monadsyntax

fun label_steps rws =
  let
    val rules = [comp_return_labels, emit_op_labels, emit_void_labels,
      emit_inst_labels, pairTheory.ELIM_UNCURRY] @ rws
    val step =
      FIRST [irule fresh_label_bind_labels,
             irule new_block_action_labels,
             irule comp_ignore_bind_labels >> conj_tac,
             irule comp_bind_labels >> conj_tac,
             FIRST_ASSUM MATCH_ACCEPT_TAC,
             disch_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC]
  in
    rpt gen_tac >> simp rules >> rpt (step >> rpt gen_tac >> simp rules)
  end

Theorem group_kwarg_alloca_labels[local]:
  !specs ce s.
    cs_extends s (SND (compile_create_kwarg_allocas ce specs s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_kwarg_allocas ce specs s)))
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_create_kwarg_allocas_def] >>
  label_steps [compile_alloc_buffer_labels]
QED

Theorem group_init_kwarg_labels[local]:
  !vars ce off k hi s.
    cs_extends s (SND (compile_init_kwargs ce vars off k hi s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_init_kwargs ce vars off k hi s)))
Proof
  Induct >> simp[compile_init_kwargs_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_init_kwargs_def] >>
  label_steps [compile_abi_arg_ptr_guard_labels, CONJUNCT1 compile_abi_decode_labels,
    lower_value_labels, compile_expr_labels, compile_store_bytestring_labels]
QED

Theorem group_entry_kwargs_labels[local]:
  !ce vars off k lbl s.
    cs_extends s (SND (compile_entry_point_kwargs ce vars off k lbl s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_entry_point_kwargs ce vars off k lbl s)))
Proof
  simp[compile_entry_point_kwargs_def] >> label_steps [group_init_kwarg_labels]
QED

Theorem selector_chain_labels[local]:
  !sels mid s. cs_extends s (SND (compile_selector_checks mid sels s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_selector_checks mid sels s)))
Proof
  Induct >> simp[compile_selector_checks_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_selector_checks_def] >>
  label_steps []
QED

Definition group_entry_labels_ok_def:
  (group_entry_labels_ok (ExternalSingle selector package) <=>
    ~internal_label_ok (FST package)) /\
  (group_entry_labels_ok (ExternalDefaults common entries specs off) <=>
    ~internal_label_ok common.ec_common_label /\
    EVERY (\(sel,lbl,mc,k). ~internal_label_ok lbl) entries)
End

Definition group_job_label_ok_def[local]:
  (group_job_label_ok (ExternalLegacyJob package) <=> ~internal_label_ok (FST package)) /\
  (group_job_label_ok (ExternalCommonJob common vars) <=> ~internal_label_ok common.ec_common_label)
End

Theorem fresh_noninternal[local]:
  !lbl. isPREFIX "@" lbl ==> ~internal_label_ok lbl
Proof
  Cases >> simp[internal_label_ok_def]
QED

Theorem fresh_group_label_bind[local]:
  !suffix k.
    (!lbl s. isPREFIX "@" lbl ==>
       cs_extends s (SND (k lbl s)) /\
       EVERY (\l. ~internal_label_ok l) (added_labels s (SND (k lbl s)))) ==>
    !s. cs_extends s (SND (comp_bind (fresh_label suffix) k s)) /\
       EVERY (\l. ~internal_label_ok l)
         (added_labels s (SND (comp_bind (fresh_label suffix) k s)))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> simp[comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule fresh_label_prefix >> strip_tac >>
  drule fresh_label_labels >>
  disch_then (qspec_then `\l. ~internal_label_ok l` strip_assume_tac) >>
  irule cs_extends_labels_trans >> qexists_tac `cs'` >> simp[] >>
  first_x_assum (qspecl_then [`a`, `cs'`] mp_tac) >>
  (impl_tac >- (Cases_on `a` >> gvs[])) >> simp[]
QED

Theorem group_entry_labels[local]:
  !entries mid common vars off.
    EVERY (\(sel,lbl,mc,k). ~internal_label_ok lbl) entries ==>
    !s. cs_extends s (SND (compile_group_entries mid entries common vars off s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_group_entries mid entries common vars off s)))
Proof
  Induct >> simp[compile_group_entries_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_group_entries_def] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC >>
  irule fresh_group_label_bind >> rpt gen_tac >> disch_tac >> BETA_TAC >>
  `~internal_label_ok lbl` by metis_tac[fresh_noninternal] >>
  fs[] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[emit_inst_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[compile_entry_checks_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[group_entry_kwargs_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  simp[]
QED

Theorem common_job_labels[local]:
  !ce args vars nr key trans view body rt s.
    cs_extends s (SND (compile_common_function_body ce args vars nr key trans view body rt s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_common_function_body ce args vars nr key trans view body rt s)))
Proof
  simp[compile_common_function_body_def] >>
  label_steps [compile_register_positional_args_labels, compile_guarded_body_labels]
QED

Theorem group_jobs_labels[local]:
  !jobs. EVERY group_job_label_ok jobs ==>
    !s. cs_extends s (SND (compile_external_jobs jobs s)) /\
      EVERY (\l. ~internal_label_ok l) (added_labels s (SND (compile_external_jobs jobs s)))
Proof
  Induct >> simp[compile_external_jobs_def, comp_return_labels] >>
  qx_gen_tac `job` >> Cases_on `job` >>
  simp[group_job_label_ok_def, compile_external_jobs_def] >>
  rpt gen_tac >> strip_tac >> irule comp_ignore_bind_labels >> simp[]
  >- (gen_tac >> irule compile_external_fn_bodies_labels >> simp[fresh_noninternal]) >>
  conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  irule comp_ignore_bind_labels >> simp[] >>
  gen_tac >> irule fresh_namespace_labels_mono >>
  simp[common_job_labels, fresh_noninternal]
QED

Theorem external_groups_labels[local]:
  !groups mid. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_external_groups mid groups s)) /\
      EVERY (\l. ~internal_label_ok l) (added_labels s (SND (compile_external_groups mid groups s)))
Proof
  Induct >> simp[compile_external_groups_def, comp_return_labels] >>
  qx_gen_tac `group` >> Cases_on `group`
  >- (PairCases_on `p` >>
      simp[compile_external_groups_def, group_entry_labels_ok_def] >>
      rpt gen_tac >> strip_tac >> irule comp_ignore_bind_labels >> conj_tac
      >- (gen_tac >> irule fresh_namespace_labels_mono >>
          simp[selector_chain_labels, fresh_noninternal]) >>
      irule comp_bind_labels >> simp[comp_return_labels]) >>
  simp[compile_external_groups_def, group_entry_labels_ok_def] >>
  rpt gen_tac >> strip_tac >> irule comp_bind_labels >> reverse conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[group_kwarg_alloca_labels, fresh_noninternal]) >>
  gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[group_entry_labels] >> irule comp_bind_labels >> simp[comp_return_labels]
QED

Theorem external_groups_jobs[local]:
  !groups mid s. EVERY group_entry_labels_ok groups ==>
    EVERY group_job_label_ok (FST (compile_external_groups mid groups s))
Proof
  Induct >> simp[compile_external_groups_def, comp_return_def] >>
  qx_gen_tac `group` >> Cases_on `group`
  >- (PairCases_on `p` >>
      simp[compile_external_groups_def, group_entry_labels_ok_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt gen_tac >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >> simp[group_job_label_ok_def] >>
      metis_tac[pairTheory.FST]) >>
  simp[compile_external_groups_def, group_entry_labels_ok_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> simp[group_job_label_ok_def] >>
  metis_tac[pairTheory.FST]
QED

Theorem group_dispatch_labels[local]:
  !groups fb. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_group_dispatch_linear groups fb s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_group_dispatch_linear groups fb s)))
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[compile_group_dispatch_linear_def] >>
  ntac 3 (irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC) >>
  irule fresh_group_label_bind >> rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[emit_inst_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[fresh_noninternal]) >>
  ntac 2 (irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC) >>
  irule comp_bind_labels >> simp[external_groups_labels] >>
  gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[emit_inst_labels, comp_return_labels]
QED

Theorem group_dispatch_jobs[local]:
  !groups fb s. EVERY group_entry_labels_ok groups ==>
    EVERY group_job_label_ok (FST (compile_group_dispatch_linear groups fb s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule external_groups_jobs >> metis_tac[pairTheory.FST]
QED

Theorem grouped_prefix_labels[local]:
  !groups fallback. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_generate_grouped_runtime groups [] fallback s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_generate_grouped_runtime groups [] fallback s)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[compile_generate_grouped_runtime_def, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  irule fresh_group_label_bind >> qx_genl_tac [`lbl`, `s`] >>
  disch_tac >> BETA_TAC >>
  Cases_on `compile_group_dispatch_linear groups lbl s` >>
  rename1 `compile_group_dispatch_linear groups lbl s = (jobs,st)` >>
  drule group_dispatch_jobs >>
  disch_then (qspecl_then [`lbl`, `s`] mp_tac) >> simp[] >> strip_tac >>
  drule group_dispatch_labels >>
  disch_then (qspecl_then [`lbl`, `s`] mp_tac) >> simp[] >> strip_tac >>
  irule cs_extends_labels_trans >> qexists_tac `st` >> simp[] >>
  once_rewrite_tac[comp_bind_def] >> asm_rewrite_tac[] >> BETA_TAC >>
  simp[GSYM comp_ignore_bind_def, CONJ_COMM] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[group_jobs_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (Cases_on `fallback` >- simp[emit_inst_labels] >>
      PairCases_on `x` >> simp[] >> gen_tac >>
      irule fresh_namespace_labels_mono >>
      simp[compile_fallback_body_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> simp[comp_return_labels]
QED

Theorem package_external_group_unit_labels:
  !mods target trans nkeys f.
    group_entry_labels_ok (package_external_group_unit mods target trans nkeys f)
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_external_group_unit_def, package_external_fn_unit_def,
       set_external_package_target_def, group_entry_labels_ok_def] >>
  CASE_TAC >> Cases_on `NULL f6` >>
  simp[group_entry_labels_ok_def, external_common_label_def,
       external_prefix_label_def, internal_label_ok_def, EVERY_MAP,
       pairTheory.FORALL_PROD, compute_selector_def] >>
  simp[EVERY_MEM] >> qx_gen_tac `prefix` >> PairCases_on `prefix` >> simp[]
QED

Theorem package_external_group_labels:
  !tops target trans nkeys f.
    group_entry_labels_ok (package_external_group tops target trans nkeys f)
Proof
  metis_tac[package_external_group_unit_labels, package_external_group_unit_singleton]
QED

Theorem compile_grouped_internal_suffix[local]:
  compile_generate_grouped_runtime groups ips fb st =
  compile_internal_fn_bodies ips
    (SND (compile_generate_grouped_runtime groups [] fb st))
Proof
  simp[compile_generate_grouped_runtime_def, LET_THM, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_grouped_runtime_extends:
  EVERY group_entry_labels_ok groups /\
  compile_generate_grouped_runtime groups ips fb start = ((),final) ==>
  cs_extends start final
Proof
  strip_tac >>
  drule grouped_prefix_labels >>
  disch_then (qspecl_then [`fb`, `start`] strip_assume_tac) >>
  qpat_x_assum `compile_generate_grouped_runtime _ _ _ _ = _`
    (assume_tac o ONCE_REWRITE_RULE [compile_grouped_internal_suffix]) >>
  metis_tac[cs_appends_internal_fn_bodies, cs_appends_def, cs_extends_trans]
QED

Theorem grouped_internal_run_labels:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups ==>
  ?start final data.
    compile_generate_grouped_runtime groups [] fb
      (initial_compile_state "__entry") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__entry" ips final = SOME (unit.cu_context,data) /\
    lowering_context_ok unit.cu_context /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  Cases_on `compile_generate_grouped_runtime groups [] fb
    (initial_compile_state "__entry")` >>
  rename1 `compile_generate_grouped_runtime _ [] _ _ = (u,start)` >> Cases_on `u` >>
  drule grouped_prefix_labels >>
  disch_then (qspecl_then [`fb`, `initial_compile_state "__entry"`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)` by
    (drule cs_extends_block_stream_labels >> strip_tac >>
     fs[initial_compile_state_def, internal_label_ok_def] >>
     rename1 `MAP _ _ = added_labels _ _` >>
     pop_assum (assume_tac o SYM) >> fs[EVERY_MAP, internal_label_ok_def]) >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,final)` >> Cases_on `u` >>
  qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_grouped_lowering_def] >>
  once_rewrite_tac[compile_grouped_internal_suffix] >>
  simp[AllCaseEqs()] >> strip_tac >>
  qexists_tac `data` >> gvs[]
QED
