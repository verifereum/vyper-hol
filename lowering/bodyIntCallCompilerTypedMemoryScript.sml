Theory bodyIntCallCompilerTypedMemory
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval context compileEnv

Theorem intcall_interval_typed_memory_family:
  (!cenv dst dst_ty src src_ty k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_store_memory_typed cenv dst dst_ty src src_ty a))) /\
  (!cenv dst src dst_tys src_tys dst_off src_off k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off a))) /\
  (!cenv dst dst_ty src src_ty count k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_copy_sarray_typed cenv dst dst_ty src src_ty count a))) /\
  (!cenv dst dst_ty cap src src_ty k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty a))) /\
  (!cenv dst src dst_fields src_fields dst_off src_off k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off a)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, intcall_interval_return]
  >- simp[Once compile_store_memory_typed_def, intcall_interval_return]
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, intcall_interval_return]
  >> suspend "struct_cons"
QED

Resume intcall_interval_typed_memory_family[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dst_ty`
  >- (simp[Once compile_store_memory_typed_def] >>
      irule intcall_interval_bind_floor >>
      simp[intcall_interval_emit_op, intcall_interval_emit_void]) >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- simp[Once compile_store_memory_typed_def, intcall_interval_store_bytestring] >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      gvs[] >>
      simp[Once compile_store_memory_typed_def, intcall_interval_copy_memory]
      >>~- ([`case b' of Fixed _ => _ | Dynamic _ => _`],
             Cases_on `b` >> Cases_on `b'` >> gvs[intcall_interval_copy_memory]) >>
      first_x_assum irule >> simp[]) >>
  simp[Once compile_store_memory_typed_def, intcall_interval_emit_void]
QED

Resume intcall_interval_typed_memory_family[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_with_byte_offset])
QED

Resume intcall_interval_typed_memory_family[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def,
       intcall_interval_copy_memory] >> IF_CASES_TAC >> gvs[] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_fresh_label, intcall_interval_fresh_var,
            intcall_interval_emit_inst, intcall_interval_new_block,
            intcall_interval_emit_op, intcall_interval_return])
QED

Resume intcall_interval_typed_memory_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `dst_ty = src_ty` >> gvs[] >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_fresh_label, intcall_interval_fresh_var,
            intcall_interval_emit_inst, intcall_interval_new_block,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_copy_memory_dynamic, intcall_interval_return])
QED

Resume intcall_interval_typed_memory_family[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name`
  >- (gvs[] >> simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
      rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_with_byte_offset])) >>
  rename1 `ALOOKUP src_fields name = SOME p` >> PairCases_on `p` >>
  gvs[] >> simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_with_byte_offset])
QED
Finalise intcall_interval_typed_memory_family

Theorem intcall_interval_store_memory_typed:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_store_memory_typed cenv dst dst_ty src src_ty a))
Proof
  strip_tac >> irule (cj 1 intcall_interval_typed_memory_family) >> simp[]
QED

Theorem intcall_interval_typed_copy_fields:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off a))
Proof
  strip_tac >> irule (cj 2 intcall_interval_typed_memory_family) >> simp[]
QED

Theorem intcall_interval_copy_sarray_typed:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_copy_sarray_typed cenv dst dst_ty src src_ty n a))
Proof
  strip_tac >> irule (cj 3 intcall_interval_typed_memory_family) >> simp[]
QED

Theorem intcall_interval_copy_dynarray_typed:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty a))
Proof
  strip_tac >> irule (cj 4 intcall_interval_typed_memory_family) >> simp[]
QED

Theorem intcall_interval_struct_typed_copy:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off a))
Proof
  strip_tac >> irule (cj 5 intcall_interval_typed_memory_family) >> simp[]
QED

Theorem intcall_interval_store_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_store_memory cenv src dst dst_ty src_ty a))
Proof
  strip_tac >> rewrite_tac[compile_store_memory_def] >>
  rpt IF_CASES_TAC >>
  simp[intcall_interval_emit_void, intcall_interval_store_bytestring,
       intcall_interval_store_memory_typed, intcall_interval_copy_memory]
QED
