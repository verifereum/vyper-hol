(* Runtime dispatch and entry scaffolding retain the allocation windows. *)
Theory runtimePeakMemoryModule
Ancestors
  runtimePeakMemoryAbi runtimePeakMemoryCode runtimePeakMemoryExpr
  moduleLowering compileEnv context emitHelper venomInst list

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_abi_decode,
      dalloca_windows_abi_decode_helpers])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_internal_param_decls:
  !params idx. preserves_dalloca_windows window (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, dalloca_windows_return] >>
  Cases >> simp[compile_internal_param_decls_def] >> windows_tac []
QED

Theorem dalloca_windows_materialize_internal_params:
  !params ce. preserves_dalloca_windows window (materialize_internal_params ce params)
Proof
  Induct >> simp[materialize_internal_params_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[materialize_internal_params_def] >> windows_tac []
QED

Theorem dalloca_windows_decode_args:
  !args ce off opc hi adj. opc <> DALLOCA ==>
    preserves_dalloca_windows window (compile_decode_args ce args off opc hi adj)
Proof
  Induct >> simp[compile_decode_args_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_decode_args_def] >> strip_tac >>
  windows_tac [compile_abi_arg_ptr_guard_def]
QED

Theorem dalloca_windows_register_positional_args:
  !args ce off. preserves_dalloca_windows window (compile_register_positional_args ce args off)
Proof
  Induct >> simp[compile_register_positional_args_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_positional_args_def] >> windows_tac [dalloca_windows_decode_args]
QED

Theorem dalloca_windows_selector_checks:
  !sels mid. preserves_dalloca_windows window (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def, dalloca_windows_return] >>
  Cases >> simp[compile_selector_checks_def] >> windows_tac []
QED

Theorem dalloca_windows_emit_data_section[local]:
  preserves_dalloca_windows window (emit_data_section label)
Proof
  simp[preserves_dalloca_windows_def, compiler_dalloca_windows_def, emit_data_section_def]
QED

Theorem dalloca_windows_dispatch:
  preserves_dalloca_windows window (compile_selector_dispatch_linear lin_sels fb) /\
  preserves_dalloca_windows window (compile_selector_dispatch_sparse sels 0 fb) /\
  preserves_dalloca_windows window (compile_selector_dispatch_dense sels 0 0 [] info labels fb)
Proof
  simp[compile_selector_dispatch_linear_def, compile_selector_dispatch_sparse_def,
       compile_selector_dispatch_dense_def, emit_dense_data_sections_def] >>
  rpt conj_tac >> windows_tac [dalloca_windows_selector_checks,
      dalloca_windows_emit_data_section, sortingTheory.QSORT_DEF,
      emit_dense_data_sections_def]
QED

Theorem dalloca_windows_entry_checks:
  preserves_dalloca_windows window (compile_entry_checks min_cds payable)
Proof
  simp[compile_entry_checks_def] >> windows_tac []
QED

Theorem dalloca_windows_create_kwarg_allocas:
  !specs. preserves_dalloca_windows window (compile_create_kwarg_allocas ce specs)
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def] >> windows_tac []
QED

Theorem dalloca_windows_kwarg_alloca_defaults:
  !specs st.
    MAP (\(_,_,_,e). e) (FST (compile_create_kwarg_allocas ce specs st)) =
    MAP (\(_,_,e). e) specs
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> gvs[] >>
  first_x_assum (qspec_then `cs'` mp_tac) >> simp[]
QED

Theorem dalloca_windows_init_kwargs:
  !kwvars off n hi.
   (!e ct. MEM e (MAP (\(_,_,_,d). d) kwvars) ==>
      preserves_dalloca_windows window (compile_expr ce ct e)) ==>
   preserves_dalloca_windows window (compile_init_kwargs ce kwvars off n hi)
Proof
  Induct >> simp[compile_init_kwargs_def, dalloca_windows_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_init_kwargs_def] >> rpt strip_tac >>
  windows_tac [compile_abi_arg_ptr_guard_def, dalloca_windows_lower_value,
               dalloca_windows_store_bytestring] >> metis_tac[]
QED
