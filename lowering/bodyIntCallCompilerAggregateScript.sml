Theory bodyIntCallCompilerAggregate
Ancestors
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval exprLowering exprSimHypsDefs compileEnv

Theorem intcall_interval_lower_value:
  (!a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn cenv ty e a))) ==>
  !a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (lower_value cfn cenv ty e a))
Proof
  rpt strip_tac >> rewrite_tac[lower_value_def] >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_unwrap_value]
QED

Theorem intcall_interval_pure_multi_vvs:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_multi_vvs cfn cenv es a))
Proof
  strip_tac >> Induct >> simp[compile_multi_vvs_def, intcall_interval_return] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_return] >> rpt strip_tac >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_return]
QED

Theorem intcall_interval_pure_multi_exprs:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_multi_exprs cfn cenv es a))
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def, intcall_interval_return] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  conj_tac
  >- (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
      simp[intcall_interval_return]) >>
  simp[] >> rpt strip_tac >> irule intcall_interval_lower_value >> simp[]
QED

Theorem intcall_interval_ifexp_arm:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ifexp_arm cenv rt at vv a))
Proof
  strip_tac >> simp[compile_ifexp_arm_def, comp_ignore_bind_def] >> IF_CASES_TAC >>
  simp[intcall_interval_unwrap_value] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_pure_make_tuple:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es buf off a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_make_tuple cfn cenv es buf off a))
Proof
  strip_tac >> Induct >> simp[compile_make_tuple_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_pure_make_array_elems:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es et sz hl buf idx a.
    EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_make_array_elems cfn cenv es et sz hl buf idx a))
Proof
  strip_tac >> Induct >> simp[compile_make_array_elems_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_pure_make_array:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_make_array cfn cenv es et sz hl buf a))
Proof
  strip_tac >> Cases_on `hl` >>
  simp[compile_make_array_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_void, intcall_interval_return,
       intcall_interval_pure_make_array_elems]
QED

Theorem intcall_interval_pure_struct_lit:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !fs ty buf off a.
    EVERY (\p. ~expr_has_effect (SND p)) fs /\ k <= a.cs_next_var ==>
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

Theorem intcall_interval_pure_concat:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es dp infos off a.
    EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
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

Theorem intcall_interval_keccak_key:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_keccak256_key op b a))
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_keccak256_key_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void])
QED

Theorem intcall_interval_mapping_subscript:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_mapping_subscript op key a))
Proof
  strip_tac >> simp[compile_mapping_subscript_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void])
QED

Theorem intcall_interval_array_subscript:
  (!op a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (loader op a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_array_subscript base_op idx dyn static_n ws sz signed loader a))
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `signed` >>
  simp[compile_array_subscript_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_return, intcall_interval_emit_op,
            intcall_interval_emit_void])
QED

Theorem intcall_interval_pure_attribute:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  ~expr_has_effect e /\ k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_attribute cfn cenv rt ty e fld a))
Proof
  strip_tac >> simp[compile_attribute_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_return])
QED

Theorem intcall_interval_pure_subscript:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  ~expr_has_effect be /\ ~expr_has_effect ie /\ k <= a.cs_next_var ==>
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

Theorem intcall_interval_pair_bind_floor:
  (!a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mf a))) /\
  (!v a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mg v a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (UNCURRY mg (mf a)))
Proof
  strip_tac >>
  `UNCURRY mg (mf a) = comp_bind mf mg a` by
    simp[comp_bind_def, pairTheory.UNCURRY] >>
  simp[] >> irule intcall_interval_bind_floor >> simp[]
QED

Theorem intcall_interval_pure_acc:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  ~expr_has_effect e /\ k <= a.cs_next_var ==>
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
