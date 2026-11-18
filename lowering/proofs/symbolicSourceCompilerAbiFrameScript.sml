Theory symbolicSourceCompilerAbiFrame
Ancestors symbolicSourceCompilerFrame abiEncoder compileEnv emitHelper

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

Theorem symbolic_frame_abi_int_clamp[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_int_clamp v bits signed)
Proof
  strip_tac >>
  Cases_on `signed` >> simp[compile_abi_int_clamp_def]
QED

Theorem symbolic_frame_abi_bytes_clamp[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_bytes_clamp v n)
Proof
  strip_tac >>
  simp[compile_abi_bytes_clamp_def]
QED

Theorem symbolic_frame_abi_clamp_basetype[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_clamp_basetype v c)
Proof
  strip_tac >>
  Cases_on `c` >> simp[compile_abi_clamp_basetype_def]
QED

Theorem symbolic_frame_abi_zero_pad[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_zero_pad p n c)
Proof
  strip_tac >>
  simp[compile_abi_zero_pad_def]
QED

Theorem symbolic_frame_get_element_ptr[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_get_element_ptr p n)
Proof
  strip_tac >>
  simp[compile_get_element_ptr_def]
QED

Theorem symbolic_frame_get_dynarray_elem_ptr[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_get_dynarray_elem_ptr p i n)
Proof
  strip_tac >>
  simp[compile_get_dynarray_elem_ptr_def]
QED

Theorem symbolic_frame_abi_encode_static[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_encode_static dst src)
Proof
  strip_tac >>
  simp[compile_abi_encode_static_def]
QED

Theorem symbolic_frame_abi_decode_static:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!v. symbolic_frame R (clamp v)) ==>
  symbolic_frame R (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >>
  simp[compile_abi_decode_static_def]
QED

Theorem symbolic_frame_abi_encode_static_info[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_encode_static_info dst src info)
Proof
  strip_tac >>
  Cases_on `info` >> simp[compile_abi_encode_static_info_def]
QED

Theorem symbolic_frame_abi_encode_dyn_static_loop:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!label. symbolic_frame R (fresh_label label)) /\
  (!label. symbolic_frame R (new_block label)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  strip_tac >> simp[compile_abi_encode_dyn_static_loop_def,
                       comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_abi_dec_addr[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_dec_addr bop pos)
Proof
  strip_tac >>
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >> simp[]
QED

Theorem symbolic_frame_abi_decode_range_check[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_abi_decode_range_check start endop hi)
Proof
  strip_tac >>
  simp[compile_abi_decode_range_check_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_getelemptr_abi[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  strip_tac >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem symbolic_frame_abi_decode_dyn_elem_ptr[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R
    (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)
Proof
  strip_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule symbolic_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [irule symbolic_frame_bind >> conj_tac,
              gen_tac, CHANGED_TAC (simp[comp_ignore_bind_def])])
QED

Theorem symbolic_frame_abi_copy_case[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)
Proof
  strip_tac >>
  Cases_on `opc` >> simp[]
QED
