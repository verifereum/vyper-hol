Theory bodyIntCallCompilerDecoder
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval abiEncoder compileEnv

Theorem intcall_interval_abi_int_clamp:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_int_clamp op bits sg a))
Proof
  strip_tac >> Cases_on `sg` >> simp[compile_abi_int_clamp_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_abi_bytes_clamp:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_bytes_clamp op n a))
Proof
  strip_tac >> simp[compile_abi_bytes_clamp_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_abi_clamp:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_clamp_basetype op ci a))
Proof
  strip_tac >> Cases_on `ci` >>
  simp[compile_abi_clamp_basetype_def, intcall_interval_abi_int_clamp,
       intcall_interval_abi_bytes_clamp, intcall_interval_return] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_decode_static:
  (!v a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (clamp v a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_decode_static src dst opc clamp a))
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_dec_addr:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_dec_addr bop pos a))
Proof
  strip_tac >> simp[compile_abi_dec_addr_def] >>
  IF_CASES_TAC >> simp[intcall_interval_emit_op, intcall_interval_return]
QED

Theorem intcall_interval_decode_range:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_abi_decode_range_check lo hi lim a))
Proof
  strip_tac >> simp[compile_abi_decode_range_check_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_getelemptr_abi:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_getelemptr_abi src dyn off opc bop hi a))
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_dec_addr, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Theorem intcall_interval_decode_dyn_elem_ptr:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_abi_decode_dyn_elem_ptr opc bop es sd hi asz a))
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_dec_addr, intcall_interval_decode_range,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_decode_copy[local]:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND ((case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [dst; src; sz]
     | DLOAD => emit_void DLOADBYTES [dst; src; sz]
     | _ => emit_void MCOPY [dst; src; sz]) a))
Proof
  Cases_on `opc` >> simp[intcall_interval_emit_void]
QED

Theorem intcall_interval_decode_family:
  (!dst src opc bop hi info k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_decode_to_buf dst src opc bop hi info a))) /\
  (!dst src opc bop hi elems ao vo k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo a))) /\
  (!dst src opc bop hi info asz msz ip cnt k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_abi_decode_dyn_loop dst src opc bop hi info asz msz ip cnt a)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "dyn"
  >- suspend "complex"
  >- simp[Once compile_abi_decode_to_buf_def, intcall_interval_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume intcall_interval_decode_family[prim]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_decode_to_buf_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_dec_addr, intcall_interval_decode_static,
       intcall_interval_abi_clamp]
QED

Resume intcall_interval_decode_family[bytes]:
  rpt gen_tac >> strip_tac >> Cases_on `hi = Lit 0w` >>
  Cases_on `bop = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_decode_copy, intcall_interval_dec_addr, intcall_interval_decode_range,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Resume intcall_interval_decode_family[dyn]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >>
  rename1 `DecDynArray info asz msz dynb maxn` >>
  Cases_on `~dynb /\ ~dec_info_needs_clamp info` >>
  gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_decode_copy, intcall_interval_dec_addr, intcall_interval_decode_range,
            intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Resume intcall_interval_decode_family[complex]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_decode_range, intcall_interval_emit_op])
QED

Resume intcall_interval_decode_family[elems]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_getelemptr_abi, intcall_interval_emit_op])
QED

Resume intcall_interval_decode_family[loop]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `dec_info_needs_offset info` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_dec_addr, intcall_interval_decode_dyn_elem_ptr,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_emit_inst, intcall_interval_fresh_label,
            intcall_interval_new_block, intcall_interval_return])
QED
Finalise intcall_interval_decode_family
