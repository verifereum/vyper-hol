(* ABI operand exclusion, using the context/value preservation boundary. *)
Theory runtimeLabelABI
Ancestors
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant abiEncoder emitHelper compileEnv
  context venomInst list

Theorem rb_compile_abi_int_clamp:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_int_clamp op bits signed)
Proof
  strip_tac >> Cases_on `signed` >>
  pure_rewrite_tac[compile_abi_int_clamp_def, LET_THM] >> BETA_TAC >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_abi_bytes_clamp:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_bytes_clamp op m)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_bytes_clamp_def, LET_THM] >>
  BETA_TAC >> irule rb_bind_emit_op >> BETA_TAC >> simp[] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_emit_void]
QED

Theorem rb_compile_abi_clamp_basetype:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_clamp_basetype op info)
Proof
  Cases_on `info` >>
  simp[compile_abi_clamp_basetype_def, rb_compile_abi_int_clamp,
       rb_compile_abi_bytes_clamp, rb_step_return] >>
  strip_tac >> irule rb_bind_emit_op >> BETA_TAC >> simp[] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_emit_void]
QED

Theorem rb_compile_abi_zero_pad:
  rb_operand_ok p /\ rb_operand_ok len /\ rb_operand_ok cnt ==>
  rb_step (K T) (compile_abi_zero_pad p len cnt)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_zero_pad_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_get_element_ptr:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_get_element_ptr p n)
Proof
  simp[compile_get_element_ptr_def, rb_emit_op]
QED

Theorem rb_compile_get_dynarray_elem_ptr:
  rb_operand_ok p /\ rb_operand_ok idx ==>
  rb_step rb_operand_ok (compile_get_dynarray_elem_ptr p idx n)
Proof
  strip_tac >> pure_rewrite_tac[compile_get_dynarray_elem_ptr_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_abi_encode_static:
  rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step rb_operand_ok (compile_abi_encode_static dst src)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_encode_static_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_abi_decode_static:
  rb_operand_ok src /\ rb_operand_ok dst /\
  (!op. rb_operand_ok op ==> rb_step (K T) (clamp op)) ==>
  rb_step (K T) (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_decode_static_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void]
QED

Theorem rb_compile_abi_encode_static_info:
  rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step rb_operand_ok (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, rb_compile_abi_encode_static,
       rb_step_return] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_abi_dec_addr:
  rb_operand_ok bop /\ rb_operand_ok pos ==>
  rb_step rb_operand_ok (compile_abi_dec_addr bop pos)
Proof
  Cases_on `bop = Lit 0w` >>
  simp[compile_abi_dec_addr_def, rb_step_return, rb_emit_op]
QED

Theorem rb_compile_abi_decode_range_check:
  !sop eop hi. rb_operand_ok sop /\ rb_operand_ok eop /\ rb_operand_ok hi ==>
  rb_step (K T) (compile_abi_decode_range_check sop eop hi)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_abi_decode_range_check_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_bind_abi_dec_addr:
  rb_operand_ok bop /\ rb_operand_ok pos /\
  (!op. rb_operand_ok op ==> rb_step Q (f op)) ==>
  rb_step Q (comp_bind (compile_abi_dec_addr bop pos) f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_compile_abi_dec_addr]
QED

Theorem rb_compile_getelemptr_abi:
  rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
  rb_step rb_operand_ok (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  strip_tac >> pure_rewrite_tac[compile_getelemptr_abi_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `dyn` >> simp[rb_step_return] >>
  irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[rb_step_return] >>
  Cases_on `hi = Lit 0w` >> simp[rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_abi_decode_dyn_elem_ptr:
  rb_operand_ok bop /\ rb_operand_ok src /\ rb_operand_ok data_op /\
  rb_operand_ok hi ==>
  rb_step rb_operand_ok
    (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[rb_step_return] >>
  Cases_on `hi = Lit 0w` >> simp[rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_abi_decode_range_check]
QED

Theorem rb_bind_alloc_buffer:
  (!buf. rb_buffer_ok buf ==> rb_step Q (f buf)) ==>
  rb_step Q (comp_bind (compile_alloc_buffer n) f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  simp[rb_compile_alloc_buffer]
QED

Theorem rb_compile_abi_encode_dyn_static_loop:
  rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok len ==>
  rb_step rb_operand_ok
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  BETA_TAC >> irule rb_bind_alloc_buffer >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_ignore_bind >>
  conj_tac >- (qexists_tac `rb_operand_ok` >>
               simp[rb_compile_abi_encode_static_info]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_abi_encode:
  (!dst cp info dyn off dp.
    rb_operand_ok dst /\ rb_operand_ok cp /\ rb_operand_ok dp ==>
    rb_step rb_operand_ok (compile_abi_encode_child dst cp info dyn off dp)) /\
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok dp ==>
    rb_step rb_operand_ok (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src info asz msz len.
    rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok len ==>
    rb_step rb_operand_ok (compile_abi_encode_dyn_loop dst src info asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- simp[compile_abi_encode_child_def, rb_compile_abi_encode_static]
  >- suspend "bytes"
  >- (rpt strip_tac >> pure_rewrite_tac[compile_abi_encode_child_def] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >- suspend "array"
  >- simp[compile_abi_encode_child_def, rb_step_return]
  >- suspend "complex"
  >- simp[compile_abi_encode_child_def, rb_step_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume rb_abi_encode[child]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `dyn` >> simp[] >- (
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
    reverse conj_tac >- metis_tac[] >>
    gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  metis_tac[]
QED

Resume rb_abi_encode[bytes]:
  rpt strip_tac >> pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Resume rb_abi_encode[array]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_alloc_buffer >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_compile_abi_encode_dyn_static_loop] >>
    metis_tac[]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >> simp[rb_emit_op]
QED

Resume rb_abi_encode[complex]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >- (
    irule rb_bind_alloc_buffer >> BETA_TAC >>
    gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
    irule rb_step_ignore_bind >> conj_tac >-
      (qexists_tac `rb_operand_ok` >> metis_tac[]) >> simp[rb_emit_op]) >>
  irule rb_step_ignore_bind >> conj_tac >-
    (qexists_tac `rb_operand_ok` >> metis_tac[rb_operand_basic]) >>
  simp[rb_step_return]
QED

Resume rb_abi_encode[elems]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_ignore_bind >> conj_tac >-
    (qexists_tac `rb_operand_ok` >> metis_tac[]) >> gvs[arithmeticTheory.ADD_COMM]
QED

Resume rb_abi_encode[loop]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_alloc_buffer >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_alloc_buffer >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_step_ignore_bind >> conj_tac >-
    (qexists_tac `rb_operand_ok` >> simp[rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Finalise rb_abi_encode

Theorem rb_abi_decode:
  (!dst src opc bop hi info.
    rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
    rb_operand_ok hi ==>
    rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
    rb_operand_ok hi ==>
    rb_step (K T) (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi info asz msz ip cnt.
    rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
    rb_operand_ok hi /\ rb_operand_ok ip /\ rb_operand_ok cnt ==>
    rb_step (K T) (compile_abi_decode_dyn_loop dst src opc bop hi info asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
      irule rb_bind_abi_dec_addr >> BETA_TAC >>
      simp[rb_compile_abi_decode_static, rb_compile_abi_clamp_basetype])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- simp[compile_abi_decode_to_buf_def, rb_step_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume rb_abi_decode[complex]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >- metis_tac[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_abi_decode_range_check] >>
  metis_tac[]
QED

Resume rb_abi_decode[elems]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_getelemptr_abi] >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- metis_tac[] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Resume rb_abi_decode[bytes]:
  rpt strip_tac >> pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >>
  BETA_TAC >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return] >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_abi_decode_range_check, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return] >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_abi_decode_range_check]) >>
  IF_CASES_TAC >- (Cases_on `opc` >> simp[rb_emit_void]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Resume rb_abi_decode[array]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return] >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_abi_decode_range_check, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return] >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_abi_decode_range_check]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  IF_CASES_TAC >- (
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    Cases_on `opc` >> simp[rb_emit_void]) >>
  irule rb_bind_alloc_buffer >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >> metis_tac[]
QED

Resume rb_abi_decode[loop]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return, rb_compile_abi_decode_dyn_elem_ptr]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- metis_tac[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED

Finalise rb_abi_decode
