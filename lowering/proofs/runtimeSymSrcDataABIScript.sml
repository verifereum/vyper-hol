Theory runtimeSymSrcDataABI
Ancestors
  symbolicSourceCompilerAbiFrame
  runtimeSymSrcDataFrame symbolicSourceCompilerFrame abiEncoder compileEnv emitHelper

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem)))

Theorem runtime_data_frame_abi_int_clamp[simp]:
  runtime_data_frame (compile_abi_int_clamp v bits signed)
Proof
  apply_symbolic_frame symbolic_frame_abi_int_clamp >> simp[]
QED

Theorem runtime_data_frame_abi_bytes_clamp[simp]:
  runtime_data_frame (compile_abi_bytes_clamp v n)
Proof
  apply_symbolic_frame symbolic_frame_abi_bytes_clamp >> simp[]
QED

Theorem runtime_data_frame_abi_clamp_basetype[simp]:
  runtime_data_frame (compile_abi_clamp_basetype v c)
Proof
  apply_symbolic_frame symbolic_frame_abi_clamp_basetype >> simp[]
QED

Theorem runtime_data_frame_abi_zero_pad[simp]:
  runtime_data_frame (compile_abi_zero_pad p n c)
Proof
  apply_symbolic_frame symbolic_frame_abi_zero_pad >> simp[]
QED

Theorem runtime_data_frame_get_element_ptr[simp]:
  runtime_data_frame (compile_get_element_ptr p n)
Proof
  apply_symbolic_frame symbolic_frame_get_element_ptr >> simp[]
QED

Theorem runtime_data_frame_get_dynarray_elem_ptr[simp]:
  runtime_data_frame (compile_get_dynarray_elem_ptr p i n)
Proof
  apply_symbolic_frame symbolic_frame_get_dynarray_elem_ptr >> simp[]
QED

Theorem runtime_data_frame_abi_encode_static[simp]:
  runtime_data_frame (compile_abi_encode_static dst src)
Proof
  apply_symbolic_frame symbolic_frame_abi_encode_static >> simp[]
QED

Theorem runtime_data_frame_abi_decode_static:
  (!v. runtime_data_frame (clamp v)) ==>
  runtime_data_frame (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_abi_decode_static >> simp[]
QED

Theorem runtime_data_frame_abi_encode_static_info[simp]:
  runtime_data_frame (compile_abi_encode_static_info dst src info)
Proof
  apply_symbolic_frame symbolic_frame_abi_encode_static_info >> simp[]
QED

Theorem runtime_data_frame_abi_encode_dyn_static_loop:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_abi_encode_dyn_static_loop >> simp[]
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
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_abi_encode))) >>
  simp[runtime_data_frame_abi_encode_dyn_static_loop]
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
  apply_symbolic_frame symbolic_frame_abi_dec_addr >> simp[]
QED

Theorem runtime_data_frame_abi_decode_range_check[simp]:
  runtime_data_frame (compile_abi_decode_range_check start endop hi)
Proof
  apply_symbolic_frame symbolic_frame_abi_decode_range_check >> simp[]
QED

Theorem runtime_data_frame_getelemptr_abi[simp]:
  runtime_data_frame (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  apply_symbolic_frame symbolic_frame_getelemptr_abi >> simp[]
QED

Theorem runtime_data_frame_abi_decode_dyn_elem_ptr[simp]:
  runtime_data_frame
    (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)
Proof
  apply_symbolic_frame symbolic_frame_abi_decode_dyn_elem_ptr >> simp[]
QED

(* Keep the opcode choice opaque in the recursive decoder proof. *)
Theorem runtime_data_frame_abi_copy_case[simp]:
  runtime_data_frame
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)
Proof
  apply_symbolic_frame symbolic_frame_abi_copy_case >> simp[]
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
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_abi_decode))) >>
  simp[runtime_data_frame_abi_decode_static]
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
