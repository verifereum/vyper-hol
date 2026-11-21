(* Bound-label interfaces for the external-entry compiler wrappers. *)
Theory entryBodyBoundLabels
Ancestors
  bodyBoundLabels moduleLowering helperBoundLabels boundLabelRules
  compileEnv loweringShapeDefs

Theorem bound_labels_decode_args:
  (!l. compiler_label l ==> P l) ==>
  !xs ce off opc hi adj s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_decode_args ce xs off opc hi adj s))))
Proof
  strip_tac >> Induct >> simp[compile_decode_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_abi_clamp_basetype, cj 1 bound_labels_abi_decode,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[comp_return_def] >>
  rename1 `SOME loc` >> Cases_on `var_location_decode_operand loc` >>
  simp[comp_return_def, bound_labels_emit_void] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    compile_abi_arg_ptr_guard_def, comp_return_def,
    cj 1 bound_labels_abi_decode]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_register_positional_args:
  (!l. compiler_label l ==> P l) ==>
  !xs ce off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_register_positional_args ce xs off s))))
Proof
  strip_tac >> Induct >> simp[compile_register_positional_args_def,
    comp_return_def] >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer,
    bound_labels_decode_args, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_guarded_body:
  (!l. compiler_label l ==> P l) ==>
  !ce nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_guarded_body ce nr key trans view body rt s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_guarded_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_nonreentrant_lock,
    bound_labels_nonreentrant_unlock, cj 2 bound_labels_stmt_mutual,
    cj 2 bound_labels_primitives, bound_labels_emit_inst, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `rt` >> simp[bound_labels_emit_inst]
QED

Theorem bound_labels_external_function_body:
  (!l. compiler_label l ==> P l) ==>
  !ce args nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_function_body ce args nr key trans view body rt s))))
Proof
  rpt strip_tac >> simp[compile_external_function_body_def] >>
  irule bound_labels_bind >>
  simp[bound_labels_register_positional_args, bound_labels_guarded_body]
QED

Theorem bound_labels_fallback_body:
  (!l. compiler_label l ==> P l) ==>
  !ce pay nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_fallback_body ce pay nr key trans view body rt s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_fallback_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_guarded_body,
    bound_labels_emit_op, bound_labels_emit_void, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_entry_checks:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_entry_checks min_cds pay s))))
Proof
  simp[compile_entry_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_emit_void, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_external_fn_bodies:
  (!l. compiler_label l ==> P l) ==>
  !xs s.
    EVERY (\(lbl,ce,args,mc,pay,nr,key,tr,view,body,rt). P lbl) xs /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_fn_bodies xs s))))
Proof
  strip_tac >> Induct >> simp[compile_external_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[compile_external_fn_bodies_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_new_block,
    bound_labels_entry_checks, bound_labels_external_function_body]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_selector_checks:
  (!l. compiler_label l ==> P l) ==>
  !xs mid s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_selector_checks mid xs s))))
Proof
  strip_tac >> Induct >> simp[compile_selector_checks_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_selector_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_selector_dispatch_linear:
  (!l. compiler_label l ==> P l) ==>
  !xs fb s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_selector_dispatch_linear xs fb s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_selector_dispatch_linear_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block, bound_labels_selector_checks]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_runtime_linear_no_internals:
  (!l. compiler_label l ==> P l) ==>
  !sels exts fb bc mb db ei s.
    EVERY (\(lbl,ce,args,mc,pay,nr,key,tr,view,body,rt). P lbl) exts /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_generate_runtime sels exts [] fb Linear bc mb db ei s))))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_generate_runtime_def, compile_internal_fn_bodies_def] >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_selector_dispatch_linear,
    bound_labels_external_fn_bodies, bound_labels_new_block,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac]) >>
  namedCases_on `fb` ["", "fbody"] >> simp[bound_labels_emit_inst] >>
  PairCases_on `fbody` >>
  simp[bound_labels_fallback_body]
QED

Theorem bound_labels_create_kwarg_allocas[local]:
  (!l. compiler_label l ==> P l) ==>
  !specs ce s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_create_kwarg_allocas ce specs s))))
Proof
  strip_tac >> Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_lower_default[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (lower_value compile_expr ce ty e s))))
Proof
  strip_tac >> irule bound_labels_lower_value >>
  simp[cj 1 bound_labels_expr_mutual]
QED

Theorem bound_labels_init_kwargs[local]:
  (!l. compiler_label l ==> P l) ==>
  !vars ce off n hi s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_init_kwargs ce vars off n hi s))))
Proof
  strip_tac >> Induct >> simp[compile_init_kwargs_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[compile_init_kwargs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_lower_default, bound_labels_store_bytestring,
    cj 1 bound_labels_abi_decode, comp_return_def]),
    strip_tac, gen_tac, irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC]) >>
  simp[compile_abi_arg_ptr_guard_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_group_entries[local]:
  (!l. compiler_label l ==> P l) ==>
  !entries mid common kwvars off s.
    EVERY (\(sel,lbl,m,k). P lbl) entries /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_group_entries mid entries common kwvars off s))))
Proof
  strip_tac >> Induct >> simp[compile_group_entries_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> simp[compile_group_entries_def, compile_entry_point_kwargs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block, bound_labels_entry_checks, bound_labels_init_kwargs]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Definition external_group_labels_ok_def:
  external_group_labels_ok P (ExternalSingle sel pkg) = P (FST pkg) /\
  external_group_labels_ok P (ExternalDefaults common entries specs off) =
    (P common.ec_common_label /\ EVERY (\(sel,lbl,m,k). P lbl) entries)
End

Definition external_job_label_ok_def:
  external_job_label_ok P (ExternalLegacyJob pkg) = P (FST pkg) /\
  external_job_label_ok P (ExternalCommonJob common vars) = P common.ec_common_label
End

Theorem bound_labels_external_groups[local]:
  (!l. compiler_label l ==> P l) ==>
  !groups mid s.
    EVERY (external_group_labels_ok P) groups /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY (external_job_label_ok P) (FST (compile_external_groups mid groups s)) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_groups mid groups s))))
Proof
  strip_tac >> Induct >> simp[compile_external_groups_def, comp_return_def] >>
  Cases_on `h` >> simp[external_group_labels_ok_def] >-
    (rename1 `ExternalSingle sel pkg` >> PairCases_on `sel` >>
     rpt strip_tac >> simp[compile_external_groups_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     `EVERY P (MAP (\bb. bb.bb_label) (all_blocks cs'))` by
       (qpat_assum `!l. compiler_label l ==> P l`
          (mp_tac o MATCH_MP bound_labels_selector_checks) >>
        disch_then (qspecl_then [`[(sel0,sel1)]`, `mid`, `s`] mp_tac) >> simp[]) >>
     qpat_x_assum `!m t. _ ==> EVERY (external_job_label_ok P) _ /\ _`
       (qspecl_then [`mid`, `cs'`] mp_tac) >>
     simp[external_job_label_ok_def]) >>
  rpt strip_tac >> simp[compile_external_groups_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `EVERY P (MAP (\bb. bb.bb_label) (all_blocks cs'))` by
    metis_tac[bound_labels_create_kwarg_allocas, pairTheory.SND] >>
  `EVERY P (MAP (\bb. bb.bb_label) (all_blocks cs''))` by
    metis_tac[bound_labels_group_entries, pairTheory.SND] >>
  qpat_x_assum `!m t. _ ==> EVERY (external_job_label_ok P) _ /\ _`
    (qspecl_then [`mid`, `cs''`] mp_tac) >>
  simp[external_job_label_ok_def]
QED

Theorem bound_labels_external_jobs[local]:
  (!l. compiler_label l ==> P l) ==>
  !jobs s. EVERY (external_job_label_ok P) jobs /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_jobs jobs s))))
Proof
  strip_tac >> Induct >> simp[compile_external_jobs_def, comp_return_def] >>
  Cases_on `h` >> simp[external_job_label_ok_def]
  >- (rename1 `ExternalLegacyJob pkg` >> PairCases_on `pkg` >>
      rpt strip_tac >> gvs[compile_external_jobs_def] >>
      irule bound_labels_ignore_bind >> simp[] >>
      qpat_assum `!l. compiler_label l ==> P l`
        (mp_tac o MATCH_MP bound_labels_external_fn_bodies) >>
      disch_then (qspec_then
        `[(pkg0,pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7,pkg8,pkg9,pkg10)]` mp_tac) >>
      simp[]) >>
  rpt strip_tac >> simp[compile_external_jobs_def, compile_common_function_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_new_block,
    bound_labels_register_positional_args, bound_labels_guarded_body]),
    gen_tac, strip_tac, irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac])
QED

Theorem bound_labels_group_dispatch[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY (external_group_labels_ok P) groups /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY (external_job_label_ok P) (FST (compile_group_dispatch_linear groups fb s)) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_group_dispatch_linear groups fb s))))
Proof
  strip_tac >> simp[compile_group_dispatch_linear_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac bound_labels_fresh_label >>
  metis_tac[bound_labels_emit_op, bound_labels_emit_inst, bound_labels_new_block,
            bound_labels_external_groups, pairTheory.SND, pairTheory.FST]
QED

Theorem bound_labels_runtime_grouped_no_internals:
  (!l. compiler_label l ==> P l) /\
  EVERY (external_group_labels_ok P) groups /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_generate_grouped_runtime groups [] fb s))))
Proof
  strip_tac >>
  simp[compile_generate_grouped_runtime_def, compile_internal_fn_bodies_def] >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_bind_result >> simp[] >>
  qexists_tac `\jobs t. EVERY (external_job_label_ok P) jobs /\
                          EVERY P (MAP (\bb. bb.bb_label) (all_blocks t))` >>
  simp[] >> reverse conj_tac >- metis_tac[bound_labels_group_dispatch] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_external_jobs,
    bound_labels_new_block, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac]) >>
  namedCases_on `fb` ["", "fbody"] >> simp[bound_labels_emit_inst] >>
  PairCases_on `fbody` >> simp[bound_labels_fallback_body]
QED
