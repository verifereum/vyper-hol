(* ABI operation correspondence boundaries. *)
Theory gasShadowCompileAbi
Ancestors
  gasShadowCompileContext gasShadowCompileBase gasShadowState abiEncoder
  compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_abi_int_clamp:
  gas_shadow_compiles (compile_abi_int_clamp v bits signed)
    (compile_abi_int_clamp v bits signed)
Proof
  Cases_on `signed` >> simp[compile_abi_int_clamp_def, LET_THM,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_abi_bytes_clamp:
  gas_shadow_compiles (compile_abi_bytes_clamp v m) (compile_abi_bytes_clamp v m)
Proof
  simp[compile_abi_bytes_clamp_def, LET_THM,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_abi_clamp_basetype:
  gas_shadow_compiles (compile_abi_clamp_basetype v clamp)
    (compile_abi_clamp_basetype v clamp)
Proof
  Cases_on `clamp` >> simp[compile_abi_clamp_basetype_def,
    gas_shadow_compiles_abi_int_clamp, gas_shadow_compiles_abi_bytes_clamp,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_void, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_abi_zero_pad:
  gas_shadow_compiles (compile_abi_zero_pad ptr_op len n)
    (compile_abi_zero_pad ptr_op len n)
Proof
  simp[compile_abi_zero_pad_def, gas_shadow_compiles_bind, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_get_element_ptr:
  gas_shadow_compiles (compile_get_element_ptr ptr_op off)
    (compile_get_element_ptr ptr_op off)
Proof
  simp[compile_get_element_ptr_def]
QED

Theorem gas_shadow_compiles_get_dynarray_elem_ptr:
  gas_shadow_compiles (compile_get_dynarray_elem_ptr ptr_op idx sz)
    (compile_get_dynarray_elem_ptr ptr_op idx sz)
Proof
  simp[compile_get_dynarray_elem_ptr_def, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_abi_encode_static:
  gas_shadow_compiles (compile_abi_encode_static dst src)
    (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, comp_ignore_bind_def,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_void, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_abi_decode_static:
  (!v. gas_shadow_compiles (f v) (g v)) ==>
  gas_shadow_compiles (compile_abi_decode_static src dst opc f)
    (compile_abi_decode_static src dst opc g)
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_abi_encode_static_info:
  gas_shadow_compiles (compile_abi_encode_static_info dst src info)
    (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def, comp_ignore_bind_def,
    gas_shadow_compiles_abi_encode_static, gas_shadow_compiles_bind,
    gas_shadow_compiles_emit_void, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_abi_encode_dyn_static_loop:
  gas_shadow_compiles (compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len)
    (compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len)
Proof
  simp[compile_abi_encode_dyn_static_loop_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block, gas_shadow_compiles_abi_encode_static_info]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_abi_dec_addr:
  gas_shadow_compiles (compile_abi_dec_addr bop pos) (compile_abi_dec_addr bop pos)
Proof
  Cases_on `bop = Lit 0w` >>
  simp[compile_abi_dec_addr_def, gas_shadow_compiles_return] >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_abi_decode_range_check:
  gas_shadow_compiles (compile_abi_decode_range_check start end_op hi)
    (compile_abi_decode_range_check start end_op hi)
Proof
  simp[compile_abi_decode_range_check_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_getelemptr_abi:
  gas_shadow_compiles (compile_getelemptr_abi src dyn off opc bop hi)
    (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_return]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_abi_decode_dyn_elem_ptr:
  gas_shadow_compiles (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
    (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_return]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_abi_encode_mutual:
  (!dst src info dyn off dp.
    gas_shadow_compiles (compile_abi_encode_child dst src info dyn off dp)
      (compile_abi_encode_child dst src info dyn off dp)) /\
  (!dst src info.
    gas_shadow_compiles (compile_abi_encode_to_buf dst src info)
      (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    gas_shadow_compiles (compile_abi_encode_complex_elems dst src elems so ho dp)
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src info abi_sz mem_sz len.
    gas_shadow_compiles (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len)
      (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac
  >- suspend "child"
  >- (once_rewrite_tac[compile_abi_encode_child_def] >>
      simp[gas_shadow_compiles_abi_encode_static])
  >- suspend "bytes"
  >- (once_rewrite_tac[compile_abi_encode_child_def] >>
      simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
           gas_shadow_compiles_emit_void, gas_shadow_compiles_return])
  >- suspend "array"
  >- (once_rewrite_tac[compile_abi_encode_child_def] >> simp[gas_shadow_compiles_return])
  >- suspend "complex"
  >- (once_rewrite_tac[compile_abi_encode_child_def] >> simp[gas_shadow_compiles_return])
  >- suspend "elems"
  >> suspend "loop"
QED

Resume gas_shadow_compiles_abi_encode_mutual[child]:
  strip_tac >> Cases_on `dyn` >> gvs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Resume gas_shadow_compiles_abi_encode_mutual[bytes]:
  once_rewrite_tac[compile_abi_encode_child_def] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_abi_encode_mutual[array]:
  strip_tac >> Cases_on `elem_is_dyn` >> gvs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_abi_encode_dyn_static_loop]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_abi_encode_mutual[complex]:
  strip_tac >> rename1 `AbiComplex (entry::entries)` >>
  Cases_on `EXISTS (\(_, _, _, is_dyn). is_dyn) (entry::entries)` >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> asm_rewrite_tac[] >>
  gvs[] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Resume gas_shadow_compiles_abi_encode_mutual[elems]:
  strip_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_abi_encode_mutual[loop]:
  strip_tac >> gvs[] >> once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Finalise gas_shadow_compiles_abi_encode_mutual

Theorem gas_shadow_compiles_abi_encode_child:
  gas_shadow_compiles (compile_abi_encode_child dst src info dyn off dp)
    (compile_abi_encode_child dst src info dyn off dp)
Proof
  metis_tac[gas_shadow_compiles_abi_encode_mutual]
QED

Theorem gas_shadow_compiles_abi_encode_to_buf:
  gas_shadow_compiles (compile_abi_encode_to_buf dst src info)
    (compile_abi_encode_to_buf dst src info)
Proof
  metis_tac[gas_shadow_compiles_abi_encode_mutual]
QED

Theorem gas_shadow_compiles_abi_encode_complex_elems:
  gas_shadow_compiles (compile_abi_encode_complex_elems dst src elems so ho dp)
    (compile_abi_encode_complex_elems dst src elems so ho dp)
Proof
  metis_tac[gas_shadow_compiles_abi_encode_mutual]
QED

Theorem gas_shadow_compiles_abi_encode_dyn_loop:
  gas_shadow_compiles (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len)
    (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len)
Proof
  metis_tac[gas_shadow_compiles_abi_encode_mutual]
QED

Theorem gas_shadow_compiles_abi_decode_copy:
  gas_shadow_compiles
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [d; s; n]
     | DLOAD => emit_void DLOADBYTES [d; s; n]
     | _ => emit_void MCOPY [d; s; n])
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [d; s; n]
     | DLOAD => emit_void DLOADBYTES [d; s; n]
     | _ => emit_void MCOPY [d; s; n])
Proof
  Cases_on `opc` >> simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_abi_decode_mutual:
  (!dst src opc bop hi info.
    gas_shadow_compiles (compile_abi_decode_to_buf dst src opc bop hi info)
      (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    gas_shadow_compiles (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)
      (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi info abi_sz mem_sz ip cnt.
    gas_shadow_compiles (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt)
      (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac
  >- (once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      match_mp_tac gas_shadow_compiles_bind >>
      simp[gas_shadow_compiles_abi_dec_addr] >> gen_tac >>
      irule gas_shadow_compiles_abi_decode_static >>
      simp[gas_shadow_compiles_abi_clamp_basetype])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- (once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[gas_shadow_compiles_return])
  >- suspend "elems"
  >> suspend "loop"
QED

Resume gas_shadow_compiles_abi_decode_mutual[bytes]:
  Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void, gas_shadow_compiles_return]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_abi_decode_copy, gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void]
QED

Resume gas_shadow_compiles_abi_decode_mutual[array]:
  strip_tac >> Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> asm_rewrite_tac[] >>
  gvs[] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void, gas_shadow_compiles_return,
               gas_shadow_compiles_alloc_buffer]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_abi_decode_copy, gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void]
QED

Resume gas_shadow_compiles_abi_decode_mutual[complex]:
  strip_tac >> Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_abi_decode_mutual[elems]:
  strip_tac >> gvs[] >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_getelemptr_abi]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_abi_decode_mutual[loop]:
  strip_tac >> gvs[] >> Cases_on `dec_info_needs_offset info` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block, gas_shadow_compiles_return,
               gas_shadow_compiles_abi_dec_addr, gas_shadow_compiles_abi_decode_range_check, gas_shadow_compiles_emit_void, gas_shadow_compiles_abi_decode_dyn_elem_ptr]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Finalise gas_shadow_compiles_abi_decode_mutual

Theorem gas_shadow_compiles_abi_decode_to_buf:
  gas_shadow_compiles (compile_abi_decode_to_buf dst src opc bop hi info)
    (compile_abi_decode_to_buf dst src opc bop hi info)
Proof
  metis_tac[gas_shadow_compiles_abi_decode_mutual]
QED

Theorem gas_shadow_compiles_abi_decode_complex_elems:
  gas_shadow_compiles (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)
    (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)
Proof
  metis_tac[gas_shadow_compiles_abi_decode_mutual]
QED

Theorem gas_shadow_compiles_abi_decode_dyn_loop:
  gas_shadow_compiles (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt)
    (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt)
Proof
  metis_tac[gas_shadow_compiles_abi_decode_mutual]
QED
