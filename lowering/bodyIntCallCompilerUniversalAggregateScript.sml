Theory bodyIntCallCompilerUniversalAggregate
Ancestors
  bodyIntCallCompilerAggregate bodyIntCallCompilerAbiWrappers
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval exprLowering compileEnv

Theorem intcall_interval_multi_exprs_floor:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_multi_exprs cfn cenv es a))
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def, intcall_interval_return] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
      simp[intcall_interval_return]) >>
  simp[] >> rpt strip_tac >> irule intcall_interval_lower_value >> simp[]
QED

Theorem intcall_interval_make_tuple_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es buf off a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_make_tuple cfn cenv es buf off a))
Proof
  strip_tac >> Induct >> simp[compile_make_tuple_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_make_array_elems_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es et sz hl buf idx a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_make_array_elems cfn cenv es et sz hl buf idx a))
Proof
  strip_tac >> Induct >> simp[compile_make_array_elems_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_make_array_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_make_array cfn cenv es et sz hl buf a))
Proof
  strip_tac >> Cases_on `hl` >>
  simp[compile_make_array_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_void, intcall_interval_return,
       intcall_interval_make_array_elems_all]
QED

Theorem intcall_interval_struct_lit_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !fs ty buf off a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_struct_lit cfn cenv ty fs buf off a))
Proof
  strip_tac >> Induct >> simp[compile_struct_lit_def, intcall_interval_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_struct_lit_def] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_concat_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es dp infos off a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_concat cfn cenv es dp infos off a))
Proof
  strip_tac >> Induct >> simp[compile_concat_def, intcall_interval_return] >>
  rpt gen_tac >> Cases_on `infos` >>
  simp[compile_concat_def, intcall_interval_return] >>
  rename1 `compile_concat cfn cenv _ _ (info::infos') _` >>
  PairCases_on `info` >>
  rpt strip_tac >> simp[compile_concat_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_lower_value])
QED

Theorem intcall_interval_attribute_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_attribute cfn cenv rt ty e fld a))
Proof
  strip_tac >> simp[compile_attribute_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_return])
QED

Theorem intcall_interval_subscript_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_subscript cfn cenv rt ty be ie a))
Proof
  strip_tac >> simp[compile_subscript_def] >>
  irule intcall_interval_bind_floor >> simp[] >>
  rpt strip_tac >> Cases_on `place_type cenv be`
  >- (simp[] >>
      rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_lower_value, intcall_interval_mapping_subscript,
                intcall_interval_return]) >>
      IF_CASES_TAC >> simp[intcall_interval_keccak_key, intcall_interval_return] >>
      rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_mapping_subscript, intcall_interval_return])) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[compile_tuple_subscript_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_return,
            intcall_interval_lower_value, intcall_interval_array_subscript,
            intcall_interval_ptr_load])
QED

Theorem intcall_interval_acc_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_acc cfn cenv e ak a))
Proof
  strip_tac >> Cases_on `ak` >>
  simp[compile_acc_def, intcall_interval_lower_value,
       intcall_interval_emit_inst] >>
  rpt (irule intcall_interval_pair_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_lower_value] >>
       rpt strip_tac >> simp[intcall_compiler_interval_refl,
                             intcall_interval_emit_inst])
QED

Theorem intcall_interval_abi_encode_args_all:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_abi_encode_args cfn cenv es a))
Proof
  strip_tac >> Induct >>
  simp[compile_abi_encode_args_def, intcall_interval_return] >>
  rpt strip_tac >> Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate cenv es` >>
  simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_materialize_vv, intcall_interval_unwrap_value,
            intcall_interval_return])
QED
