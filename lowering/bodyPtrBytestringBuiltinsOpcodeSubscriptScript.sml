Theory bodyPtrBytestringBuiltinsOpcodeSubscript
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState exprLowering

Theorem no_extcode_mapping_subscript:
  !base key s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_mapping_subscript base key s))
Proof
  rpt strip_tac >> simp[compile_mapping_subscript_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_alloc_buffer])
QED

Theorem no_extcode_keccak256_key:
  !key b s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_keccak256_key key b s))
Proof
  rpt gen_tac >> Cases_on `b` >> strip_tac >> simp[compile_keccak256_key_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_alloc_buffer])
QED

Theorem no_extcode_tuple_subscript:
  !base off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_tuple_subscript base off s))
Proof
  simp[compile_tuple_subscript_def, no_extcode_emit_op]
QED

Theorem no_extcode_array_subscript:
  !base idx dyn count scale sz signed loader.
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (loader base s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND
      (compile_array_subscript base idx dyn count scale sz signed loader s))
Proof
  rpt strip_tac >> Cases_on `dyn` >> Cases_on `signed` >>
  simp[compile_array_subscript_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_alloc_buffer])
QED

(* The callback contract names only the two children of this helper. *)
Theorem no_extcode_subscript:
  !cfn ce rt ty base idx.
  (!t e s. (e = base \/ e = idx) /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce t e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_subscript cfn ce rt ty base idx s))
Proof
  map_every qx_gen_tac [`cfn`, `ce`, `rt`, `ty`, `be`, `idx`] >>
  rpt strip_tac >> simp[compile_subscript_def] >>
  irule no_extcode_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `place_type ce be` >> simp[] >>
  TRY (rename1 `ValPT vt` >> Cases_on `vt` >> simp[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_lower_value, no_extcode_fresh_ops,
         no_extcode_mapping_subscript, no_extcode_keccak256_key,
         no_extcode_tuple_subscript, no_extcode_array_subscript,
         no_extcode_ptr_load])
QED

Theorem no_extcode_attribute:
  !cfn ce rt ty base field.
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (cfn ce ty base s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_attribute cfn ce rt ty base field s))
Proof
  rpt strip_tac >> simp[compile_attribute_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_dynarray_pop:
  !base ws sz ctor imm loc s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_dynarray_pop base ws sz ctor imm loc s))
Proof
  rpt strip_tac >> simp[compile_dynarray_pop_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_ptr_load, no_extcode_ptr_store])
QED

Theorem no_extcode_toplevel_target:
  !cfn ce id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_target_ptr cfn ce (TopLevelNameTarget id) s))
Proof
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  namedCases_on `FLOOKUP ce.ce_module_vars id` ["", "binding"] >>
  simp[no_extcode_fresh_ops] >> Cases_on `binding` >>
  simp[no_extcode_fresh_ops]
QED
