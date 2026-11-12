Theory runtimeSymSrcDataModule
Ancestors
  runtimeSymSrcDataFrame moduleLowering compileEnv

val frame_rules = [runtime_data_frame_bind, runtime_data_frame_ignore_bind,
  runtime_data_frame_return, runtime_data_frame_emit_op,
  runtime_data_frame_emit_inst, runtime_data_frame_emit_void,
  runtime_data_frame_fresh_label, runtime_data_frame_new_block,
  runtime_data_frame_get];
val frame_tac = fs frame_rules;

Theorem runtime_data_frame_selector_checks[simp]:
  !sels mid. runtime_data_frame (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def] >>
  Cases_on `h` >> gen_tac >>
  simp[compile_selector_checks_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >> gen_tac >> BETA_TAC) >>
  frame_tac
QED

Theorem runtime_data_frame_selector_dispatch_linear[simp]:
  runtime_data_frame (compile_selector_dispatch_linear sels fallback)
Proof
  simp[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_decode_args:
  (!v c. runtime_data_frame (compile_abi_clamp_basetype v c)) /\
  (!dst src opc lo hi info.
     runtime_data_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  !args cenv off opc hi adj.
    runtime_data_frame (compile_decode_args cenv args off opc hi adj)
Proof
  strip_tac >> Induct >> simp[compile_decode_args_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1` >> Cases_on `h2` >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> simp[] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_internal_param_decls[simp]:
  !params idx. runtime_data_frame (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_materialize_internal_params[simp]:
  !params cenv. runtime_data_frame (materialize_internal_params cenv params)
Proof
  Induct >> simp[materialize_internal_params_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1` >> simp[materialize_internal_params_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `x` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_register_positional_args:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!cenv args off opc hi adj.
     runtime_data_frame (compile_decode_args cenv args off opc hi adj)) ==>
  !args cenv off.
    runtime_data_frame (compile_register_positional_args cenv args off)
Proof
  strip_tac >> Induct >> simp[compile_register_positional_args_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_create_kwarg_allocas:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  !specs cenv. runtime_data_frame (compile_create_kwarg_allocas cenv specs)
Proof
  strip_tac >> Induct >> simp[compile_create_kwarg_allocas_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_create_kwarg_allocas_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_init_kwargs:
  (!dst src opc lo hi info.
     runtime_data_frame (compile_abi_decode_to_buf dst src opc lo hi info)) /\
  (!cenv ty e. runtime_data_frame (lower_value compile_expr cenv ty e)) /\
  (!src dst. runtime_data_frame (compile_store_bytestring src dst)) ==>
  !vars cenv off nkwargs hi.
    runtime_data_frame (compile_init_kwargs cenv (vars:(string # operand # type # expr) list) off nkwargs (hi:operand))
Proof
  strip_tac >> Induct >> simp[compile_init_kwargs_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_init_kwargs_def, comp_ignore_bind_def] >>
  IF_CASES_TAC
  >- (rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >>
      match_mp_tac runtime_data_frame_bind >> conj_tac
      >- (IF_CASES_TAC >>
          rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
               gen_tac >> BETA_TAC) >> frame_tac) >>
      gen_tac >> BETA_TAC >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
  gen_tac >> BETA_TAC >> match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (rpt (IF_CASES_TAC >> simp[]) >> frame_tac) >> simp[]
QED

Theorem runtime_data_frame_entry_point_kwargs:
  (!cenv vars off nkwargs hi.
     runtime_data_frame (compile_init_kwargs cenv (vars:(string # operand # type # expr) list) off nkwargs (hi:operand))) ==>
  runtime_data_frame (compile_entry_point_kwargs cenv (vars:(string # operand # type # expr) list) off nkwargs label)
Proof
  strip_tac >> simp[compile_entry_point_kwargs_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> fs[] >> metis_tac[]
QED

Theorem runtime_data_frame_entry_checks[simp]:
  runtime_data_frame (compile_entry_checks min_cds payable)
Proof
  simp[compile_entry_checks_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_guarded_body:
  (!cenv loop ty stmts. runtime_data_frame (compile_stmts cenv loop ty stmts)) /\
  (!key trans view. runtime_data_frame (compile_nonreentrant_lock key trans view)) /\
  (!key trans view. runtime_data_frame (compile_nonreentrant_unlock key trans view)) ==>
  runtime_data_frame (compile_guarded_body cenv nr key trans view stmts ret)
Proof
  strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> frame_tac) >>
  gen_tac >> BETA_TAC >> Cases_on `ret` >> frame_tac
QED

Theorem runtime_data_frame_external_function_body:
  (!cenv args off.
     runtime_data_frame (compile_register_positional_args cenv args off)) /\
  (!cenv nr key trans view stmts ret.
     runtime_data_frame (compile_guarded_body cenv nr key trans view stmts ret)) ==>
  runtime_data_frame
    (compile_external_function_body cenv args nr key trans view stmts ret)
Proof
  strip_tac >> simp[compile_external_function_body_def] >>
  match_mp_tac runtime_data_frame_bind >> fs[] >> metis_tac[]
QED

Theorem runtime_data_frame_fallback_body:
  (!cenv nr key trans view stmts ret.
     runtime_data_frame (compile_guarded_body cenv nr key trans view stmts ret)) ==>
  runtime_data_frame
    (compile_fallback_body cenv payable nr key trans view stmts ret)
Proof
  strip_tac >> simp[compile_fallback_body_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >> simp[]
QED

Theorem runtime_data_frame_internal_function:
  (!n. runtime_data_frame (compile_fixed_region_with_id n)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!key trans view. runtime_data_frame (compile_nonreentrant_lock key trans view)) /\
  (!key trans view. runtime_data_frame (compile_nonreentrant_unlock key trans view)) /\
  (!cenv loop ty stmts. runtime_data_frame (compile_stmts cenv loop ty stmts)) ==>
  runtime_data_frame (compile_internal_function cenv params has_buf nr key trans view
                                               ctor imm_len stmts ret)
Proof
  strip_tac >> simp[compile_internal_function_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (Cases_on `ret` >> simp[] >> IF_CASES_TAC >> simp[] >>
      match_mp_tac runtime_data_frame_bind >> fs[]) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      match_mp_tac runtime_data_frame_bind >> conj_tac
      >- (IF_CASES_TAC >> frame_tac) >>
      gen_tac >> BETA_TAC >> Cases_on `ret` >> frame_tac) >> frame_tac
QED

Theorem runtime_data_frame_external_fn_bodies:
  (!cenv args nr key trans view stmts ret.
     runtime_data_frame
       (compile_external_function_body cenv args nr key trans view stmts ret)) ==>
  !fns. runtime_data_frame (compile_external_fn_bodies fns)
Proof
  strip_tac >> Induct >> simp[compile_external_fn_bodies_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_internal_fn_bodies:
  (!cenv params has_buf nr key trans view ctor imm_len stmts ret.
     runtime_data_frame
       (compile_internal_function cenv params has_buf nr key trans view ctor imm_len stmts ret)) ==>
  !fns. runtime_data_frame (compile_internal_fn_bodies fns)
Proof
  strip_tac >> Induct >> simp[compile_internal_fn_bodies_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_generate_runtime:
  (!fns. runtime_data_frame (compile_external_fn_bodies fns)) /\
  (!fns. runtime_data_frame (compile_internal_fn_bodies fns)) /\
  (!cenv payable nr key trans view stmts ret.
     runtime_data_frame (compile_fallback_body cenv payable nr key trans view stmts ret)) ==>
  runtime_data_frame
    (compile_generate_runtime sels external_fns internal_fns fallback Linear
                              buckets metadata dense entry_info)
Proof
  strip_tac >> simp[compile_generate_runtime_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (Cases_on `fallback` >> simp[] >> PairCases_on `x` >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac runtime_data_frame_bind >> fs[]
QED

Theorem runtime_data_frame_common_function_body:
  (!cenv args off.
     runtime_data_frame (compile_register_positional_args cenv args off)) /\
  (!cenv nr key trans view stmts ret.
     runtime_data_frame (compile_guarded_body cenv nr key trans view stmts ret)) ==>
  runtime_data_frame
    (compile_common_function_body cenv args vars nr key trans view stmts ret)
Proof
  strip_tac >> simp[compile_common_function_body_def] >>
  match_mp_tac runtime_data_frame_bind >> fs[]
QED

Theorem runtime_data_frame_group_entries:
  (!cenv vars off nkwargs label.
     runtime_data_frame (compile_entry_point_kwargs cenv
       (vars:(string # operand # type # expr) list) off nkwargs label)) ==>
  !entries mid common vars off.
    runtime_data_frame (compile_group_entries mid entries common
      (vars:(string # operand # type # expr) list) off)
Proof
  strip_tac >> Induct >> simp[compile_group_entries_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_group_entries_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_external_groups:
  (!cenv specs. runtime_data_frame
     (compile_create_kwarg_allocas cenv (specs:(string # type # expr) list))) /\
  (!mid entries common vars off.
     runtime_data_frame (compile_group_entries mid entries common
       (vars:(string # operand # type # expr) list) off)) ==>
  !groups mid. runtime_data_frame (compile_external_groups mid groups)
Proof
  strip_tac >> Induct >> simp[compile_external_groups_def] >>
  gen_tac >> Cases_on `h`
  >- (PairCases_on `p` >> gen_tac >>
      simp[compile_external_groups_def, comp_ignore_bind_def] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
           gen_tac >> BETA_TAC) >> frame_tac) >>
  gen_tac >> simp[compile_external_groups_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_group_dispatch_linear:
  (!mid groups. runtime_data_frame (compile_external_groups mid groups)) ==>
  runtime_data_frame (compile_group_dispatch_linear groups fallback)
Proof
  strip_tac >> simp[compile_group_dispatch_linear_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_external_jobs:
  (!fns. runtime_data_frame (compile_external_fn_bodies fns)) /\
  (!cenv args vars nr key trans view stmts ret.
     runtime_data_frame
       (compile_common_function_body cenv args
         (vars:(string # operand # type # expr) list) nr key trans view stmts ret)) ==>
  !jobs. runtime_data_frame (compile_external_jobs jobs)
Proof
  strip_tac >> Induct >> simp[compile_external_jobs_def] >>
  gen_tac >> Cases_on `h` >>
  simp[compile_external_jobs_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem runtime_data_frame_generate_grouped_runtime:
  (!groups fallback. runtime_data_frame (compile_group_dispatch_linear groups fallback)) /\
  (!jobs. runtime_data_frame (compile_external_jobs jobs)) /\
  (!fns. runtime_data_frame (compile_internal_fn_bodies fns)) /\
  (!cenv payable nr key trans view stmts ret.
     runtime_data_frame (compile_fallback_body cenv payable nr key trans view stmts ret)) ==>
  runtime_data_frame (compile_generate_grouped_runtime groups internal_fns fallback)
Proof
  strip_tac >> simp[compile_generate_grouped_runtime_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (Cases_on `fallback` >> simp[] >> PairCases_on `x` >> frame_tac) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac runtime_data_frame_bind >> fs[]
QED
