(* Structural producers for the actual deployment compilation unit. *)
Theory deployUnitProducers
Ancestors
  compileVyper vyperCompiler venomInst

Theorem run_deploy_lowering_context_ok[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  lowering_context_ok unit.cu_context
Proof
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem lower_vyper_deploy_unit_context_ok:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    lowering_context_ok unit.cu_context
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_context_ok >> simp[]
QED

Theorem run_deploy_lowering_entry[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  unit.cu_context.ctx_entry = SOME entry_label /\
  ?func. lookup_function entry_label unit.cu_context.ctx_functions = SOME func
Proof
  simp[run_deploy_lowering_def] >> rpt strip_tac >>
  pairarg_tac >>
  gvs[AllCaseEqs(), extract_context_with_internals_def,
      install_immutable_reservation_def, mk_venom_context_def,
      lookup_function_def, mk_raw_function_def, listTheory.FIND_thm]
QED

Theorem lower_vyper_deploy_unit_entry:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    unit.cu_context.ctx_entry = SOME "__deploy" /\
    ?func. lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_entry >> simp[]
QED

Theorem lower_vyper_deploy_unit_global_reserved:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    unit.cu_context.ctx_global_reserved =
      (if compute_immutables_len
            (get_struct_fields (make_struct_fields_map tops)) tops = 0
       then []
       else [(0, compute_immutables_len
                    (get_struct_fields (make_struct_fields_map tops)) tops)])
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_global_reserved >> simp[]
QED
