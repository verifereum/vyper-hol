Theory bodyIntCallCompilerCreatePipeline
Ancestors
  bodyIntCallCompilerCreate bodyIntCallCompilerExtOperands
  bodyIntCallCompilerUniversal bodyIntCallCompilerAggregate
  bodyIntCallCompilerEncoder bodyIntCallCompilerContext
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit exprLowering context compileEnv

Theorem intcall_interval_slot_to_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_slot_to_memory src dst n loc a))
Proof
  simp[compile_slot_to_memory_def, intcall_interval_word_copy_loop]
QED

Theorem intcall_interval_create_salt:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce salt a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_create_salt cfn ce salt a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `salt` >>
  simp[compile_create_salt_def, intcall_interval_return] >>
  strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_lower_value, intcall_interval_return]
QED

Theorem intcall_interval_create_ctor_tuple:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_create_ctor_tuple cfn ce es a))
Proof
  rpt strip_tac >> simp[compile_create_ctor_tuple_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_multi_vvs_floor, intcall_interval_alloc_buffer,
            intcall_interval_extcall_store_values, intcall_interval_return])
QED

Theorem intcall_interval_create_blueprint_args:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce raw es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_create_blueprint_args cfn ce raw es a))
Proof
  rpt strip_tac >> Cases_on `raw`
  >- (Cases_on `es`
      >- (simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >>
          irule intcall_interval_bind_floor >>
          simp[intcall_interval_emit_inst, intcall_interval_return]) >>
      rename1 `compile_create_blueprint_args _ _ _ (e::tail)` >>
      Cases_on `tail` >>
      simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >>
      rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_lower_value, intcall_interval_emit_op,
                intcall_interval_emit_inst, intcall_interval_return])) >>
  Cases_on `es = []` >> simp[compile_create_blueprint_args_def,
                            intcall_interval_return] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_create_ctor_tuple,
            cj 2 intcall_interval_encode_family, intcall_interval_return])
QED

Theorem intcall_interval_create_snapshot:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_create_snapshot ce vv ty a))
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_alloc_buffer] >>
  Cases_on `vv_location vv` >> simp[]
  >- (rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_emit_op, intcall_interval_copy_memory_dynamic,
                intcall_interval_return])) >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_copy_memory_dynamic,
            intcall_interval_slot_to_memory, intcall_interval_imm_copy,
            intcall_interval_return])
QED

Theorem intcall_interval_raw_create:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce be ve es salt rof a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_raw_create cfn ce be ve es salt rof a))
Proof
  rpt strip_tac >> simp[compile_raw_create_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_create_snapshot, intcall_interval_lower_value,
            intcall_interval_emit_op]) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[intcall_interval_return] >>
      rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_alloc_buffer, intcall_interval_copy_memory_dynamic,
                intcall_interval_create_ctor_tuple, intcall_interval_emit_op,
                cj 2 intcall_interval_encode_family, intcall_interval_return])) >>
  simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_create_salt, intcall_interval_create_dispatch]
QED

Theorem intcall_interval_create_call:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce ck hs rof es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_create_call cfn ce ck hs rof es a))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `es`
  >- (simp[compile_create_call_def, comp_ignore_bind_def] >>
      irule intcall_interval_bind_floor >>
      simp[intcall_interval_emit_inst, intcall_interval_return]) >>
  rename1 `compile_create_call _ _ _ _ _ (e::tail)` >> Cases_on `tail`
  >- (simp[compile_create_call_def, comp_ignore_bind_def] >>
      irule intcall_interval_bind_floor >>
      simp[intcall_interval_emit_inst, intcall_interval_return]) >>
  Cases_on `ck` >> simp[compile_create_call_def] >>
  IF_CASES_TAC >> simp[comp_ignore_bind_def, intcall_interval_raw_create] >>
  rpt (simp[pairTheory.FORALL_PROD] >> rpt strip_tac >>
       irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_inst, intcall_interval_return,
            intcall_interval_lower_value, intcall_interval_create_proxy_buf,
            intcall_interval_create_salt, intcall_interval_create_dispatch,
            intcall_interval_create_copy, intcall_interval_create_blueprint_check,
            intcall_interval_create_blueprint_args,
            intcall_interval_create_blueprint_append]) >>
  simp[pairTheory.FORALL_PROD, intcall_interval_create_blueprint_append]
QED
