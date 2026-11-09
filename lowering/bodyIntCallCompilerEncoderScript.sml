Theory bodyIntCallCompilerEncoder
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval abiEncoder compileEnv

Theorem intcall_interval_encode_static:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_encode_static dst src a))
Proof
  strip_tac >> simp[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_encode_static_info:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_encode_static_info dst src info a))
Proof
  strip_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, intcall_interval_encode_static,
       intcall_interval_return, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_void, intcall_interval_return]
QED

Theorem intcall_interval_encode_static_loop:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len a))
Proof
  strip_tac >> simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_emit_inst,
            intcall_interval_fresh_label, intcall_interval_new_block,
            intcall_interval_encode_static_info])
QED

Theorem intcall_interval_encode_family:
  (!dst cp info dyn off dp k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_encode_child dst cp info dyn off dp a))) /\
  (!dst src info k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_encode_to_buf dst src info a))) /\
  (!dst src elems so ho dp k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_encode_complex_elems dst src elems so ho dp a))) /\
  (!dst src info asz msz len k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_encode_dyn_loop dst src info asz msz len a)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- simp[Once compile_abi_encode_child_def, intcall_interval_encode_static]
  >- suspend "bytestring"
  >- suspend "copy"
  >- suspend "dynarray"
  >- simp[Once compile_abi_encode_child_def, intcall_interval_return]
  >- suspend "complex"
  >- simp[Once compile_abi_encode_child_def, intcall_interval_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume intcall_interval_encode_family[child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Resume intcall_interval_encode_family[bytestring]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Resume intcall_interval_encode_family[copy]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_void, intcall_interval_return]
QED

Resume intcall_interval_encode_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >> Cases_on `elem_is_dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_encode_static_loop])
QED

Resume intcall_interval_encode_family[complex]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Resume intcall_interval_encode_family[elems]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, arithmeticTheory.ADD_COMM])
QED

Resume intcall_interval_encode_family[loop]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_emit_inst,
            intcall_interval_fresh_label, intcall_interval_new_block])
QED
Finalise intcall_interval_encode_family
