Theory runtimeSymSrcDataABI
Ancestors
  runtimeSymSrcDataFrame abiEncoder compileEnv emitHelper

Theorem runtime_data_frame_abi_int_clamp[simp]:
  runtime_data_frame (compile_abi_int_clamp v bits signed)
Proof
  Cases_on `signed` >> simp[compile_abi_int_clamp_def]
QED

Theorem runtime_data_frame_abi_bytes_clamp[simp]:
  runtime_data_frame (compile_abi_bytes_clamp v n)
Proof
  simp[compile_abi_bytes_clamp_def]
QED

Theorem runtime_data_frame_abi_clamp_basetype[simp]:
  runtime_data_frame (compile_abi_clamp_basetype v c)
Proof
  Cases_on `c` >> simp[compile_abi_clamp_basetype_def]
QED

Theorem runtime_data_frame_abi_zero_pad[simp]:
  runtime_data_frame (compile_abi_zero_pad p n c)
Proof
  simp[compile_abi_zero_pad_def]
QED

Theorem runtime_data_frame_get_element_ptr[simp]:
  runtime_data_frame (compile_get_element_ptr p n)
Proof
  simp[compile_get_element_ptr_def]
QED

Theorem runtime_data_frame_get_dynarray_elem_ptr[simp]:
  runtime_data_frame (compile_get_dynarray_elem_ptr p i n)
Proof
  simp[compile_get_dynarray_elem_ptr_def]
QED

Theorem runtime_data_frame_abi_encode_static[simp]:
  runtime_data_frame (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def]
QED

Theorem runtime_data_frame_abi_decode_static:
  (!v. runtime_data_frame (clamp v)) ==>
  runtime_data_frame (compile_abi_decode_static src dst opc clamp)
Proof
  simp[compile_abi_decode_static_def]
QED

Theorem runtime_data_frame_abi_encode_static_info[simp]:
  runtime_data_frame (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def]
QED

Theorem runtime_data_frame_abi_encode_dyn_static_loop:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  strip_tac >> simp[compile_abi_encode_dyn_static_loop_def,
                       comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_abi_encode_mutual:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  (!dst cp ci dyn off dp.
    runtime_data_frame (compile_abi_encode_child dst cp ci dyn off dp)) /\
  (!dst src info.
    runtime_data_frame (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    runtime_data_frame
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src ei asz msz len.
    runtime_data_frame (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  gvs[runtime_data_frame_abi_encode_dyn_static_loop, arithmeticTheory.ADD_COMM] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- gvs[comp_ignore_bind_def] >>
       gen_tac >> BETA_TAC) >> gvs[comp_ignore_bind_def]
QED

Theorem runtime_data_frame_abi_encode_child:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_abi_encode_child dst cp ci dyn off dp)
Proof
  metis_tac[runtime_data_frame_abi_encode_mutual]
QED

Theorem runtime_data_frame_abi_encode_to_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_abi_encode_to_buf dst src info)
Proof
  metis_tac[runtime_data_frame_abi_encode_mutual]
QED

Theorem runtime_data_frame_abi_encode_complex_elems:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_abi_encode_complex_elems dst src elems so ho dp)
Proof
  metis_tac[runtime_data_frame_abi_encode_mutual]
QED

Theorem runtime_data_frame_abi_encode_dyn_loop:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  metis_tac[runtime_data_frame_abi_encode_mutual]
QED

Theorem runtime_data_frame_abi_dec_addr[simp]:
  runtime_data_frame (compile_abi_dec_addr bop pos)
Proof
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_abi_decode_range_check[simp]:
  runtime_data_frame (compile_abi_decode_range_check start endop hi)
Proof
  simp[compile_abi_decode_range_check_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_getelemptr_abi[simp]:
  runtime_data_frame (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_abi_decode_dyn_elem_ptr[simp]:
  runtime_data_frame
    (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)
Proof
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[]
QED

(* Keep the opcode choice opaque in the recursive decoder proof. *)
Theorem runtime_data_frame_abi_copy_case[simp]:
  runtime_data_frame
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)
Proof
  Cases_on `opc` >> simp[]
QED

Theorem runtime_data_frame_abi_decode_mutual:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  (!dst src opc bop hi info.
    runtime_data_frame (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    runtime_data_frame
      (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi ei asz msz ip cnt.
    runtime_data_frame
      (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def,
       runtime_data_frame_abi_decode_static] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (FIRST
    [irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC,
     CHANGED_TAC (pure_asm_rewrite_tac [COND_CLAUSES, comp_ignore_bind_def]),
     IF_CASES_TAC]) >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem runtime_data_frame_abi_decode_to_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_abi_decode_to_buf dst src opc bop hi info)
Proof
  metis_tac[runtime_data_frame_abi_decode_mutual]
QED

Theorem runtime_data_frame_abi_decode_complex_elems:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame
    (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)
Proof
  metis_tac[runtime_data_frame_abi_decode_mutual]
QED

Theorem runtime_data_frame_abi_decode_dyn_loop:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame
    (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt)
Proof
  metis_tac[runtime_data_frame_abi_decode_mutual]
QED
