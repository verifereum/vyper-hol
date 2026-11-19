(* ABI operand exclusion, using the context/value preservation boundary. *)
Theory runtimeLabelABI
Ancestors
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant abiEncoder emitHelper compileEnv
  context venomInst list

Theorem rb_compile_abi_int_clamp_for:
  (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) (K T) (compile_abi_int_clamp op bits signed)
Proof
  strip_tac >> Cases_on `signed` >>
  pure_rewrite_tac[compile_abi_int_clamp_def, LET_THM] >> BETA_TAC >> simp[] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Theorem rb_compile_abi_bytes_clamp_for:
  (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) (K T) (compile_abi_bytes_clamp op m)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_bytes_clamp_def, LET_THM] >>
  BETA_TAC >> irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op_for >> BETA_TAC >>
  simp[rb_emit_void_for]
QED

Theorem rb_compile_abi_clamp_basetype_for:
  (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) (K T) (compile_abi_clamp_basetype op info)
Proof
  Cases_on `info` >>
  simp[compile_abi_clamp_basetype_def, rb_compile_abi_int_clamp_for,
       rb_compile_abi_bytes_clamp_for, rb_step_return_for] >>
  strip_tac >> irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op_for >> BETA_TAC >>
  simp[rb_emit_void_for]
QED

Theorem rb_compile_abi_zero_pad_for:
  (rb_operand_ok_for source_checks) p /\ (rb_operand_ok_for source_checks) len /\ (rb_operand_ok_for source_checks) cnt ==>
  (rb_step_for source_checks) (K T) (compile_abi_zero_pad p len cnt)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_zero_pad_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Theorem rb_compile_get_element_ptr_for:
  (rb_operand_ok_for source_checks) p ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_get_element_ptr p n)
Proof
  simp[compile_get_element_ptr_def, rb_emit_op_for]
QED

Theorem rb_compile_get_dynarray_elem_ptr_for:
  (rb_operand_ok_for source_checks) p /\ (rb_operand_ok_for source_checks) idx ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_get_dynarray_elem_ptr p idx n)
Proof
  strip_tac >> pure_rewrite_tac[compile_get_dynarray_elem_ptr_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Theorem rb_compile_abi_encode_static_for:
  (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_static dst src)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_encode_static_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_abi_decode_static_for:
  (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) dst /\
  source_codecopy_arity_ok source_checks opc [src] /\
  (!op. (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) (K T) (clamp op)) ==>
  (rb_step_for source_checks) (K T) (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_decode_static_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for]
QED

Theorem rb_compile_abi_encode_static_info_for:
  (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, rb_compile_abi_encode_static_for,
       rb_step_return_for] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_abi_dec_addr_for:
  (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) pos ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_dec_addr bop pos)
Proof
  Cases_on `bop = Lit 0w` >>
  simp[compile_abi_dec_addr_def, rb_step_return_for, rb_emit_op_for]
QED

Theorem rb_compile_abi_decode_range_check_for:
  !sop eop hi. (rb_operand_ok_for source_checks) sop /\ (rb_operand_ok_for source_checks) eop /\ (rb_operand_ok_for source_checks) hi ==>
  (rb_step_for source_checks) (K T) (compile_abi_decode_range_check sop eop hi)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_abi_decode_range_check_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Theorem rb_bind_abi_dec_addr_for:
  (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) pos /\
  (!op. (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) Q (f op)) ==>
  (rb_step_for source_checks) Q (comp_bind (compile_abi_dec_addr bop pos) f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >>
  simp[rb_compile_abi_dec_addr_for]
QED

Theorem rb_compile_getelemptr_abi_for:
  (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) hi /\
  (opc = CODECOPY ==> ~SND source_checks) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  strip_tac >> pure_rewrite_tac[compile_getelemptr_abi_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `dyn` >> simp[rb_step_return_for] >>
  irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> reverse conj_tac >- simp[rb_step_return_for] >>
  Cases_on `hi = Lit 0w` >> simp[rb_step_return_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Theorem rb_compile_abi_decode_dyn_elem_ptr_for:
  (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) data_op /\
  (rb_operand_ok_for source_checks) hi /\
  (opc = CODECOPY ==> ~SND source_checks) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> reverse conj_tac >- simp[rb_step_return_for] >>
  Cases_on `hi = Lit 0w` >> simp[rb_step_return_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_compile_abi_decode_range_check_for]
QED

Theorem rb_bind_alloc_buffer_for:
  (!buf. (rb_buffer_ok_for source_checks) buf ==> (rb_step_for source_checks) Q (f buf)) ==>
  (rb_step_for source_checks) Q (comp_bind (compile_alloc_buffer n) f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >>
  simp[rb_compile_alloc_buffer_for]
QED

Theorem rb_compile_abi_encode_dyn_static_loop_for:
  (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) len ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  strip_tac >> pure_rewrite_tac[compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  BETA_TAC >> irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_ignore_bind_for >>
  conj_tac >- (qexists_tac `(rb_operand_ok_for source_checks)` >>
               simp[rb_compile_abi_encode_static_info_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Theorem rb_abi_encode_for:
  (!dst cp info dyn off dp.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) cp /\ (rb_operand_ok_for source_checks) dp ==>
    (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_child dst cp info dyn off dp)) /\
  (!dst src info. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
    (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) dp ==>
    (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src info asz msz len.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) len ==>
    (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_dyn_loop dst src info asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- simp[compile_abi_encode_child_def, rb_compile_abi_encode_static_for]
  >- suspend "bytes"
  >- (rpt strip_tac >> pure_rewrite_tac[compile_abi_encode_child_def] >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for])
  >- suspend "array"
  >- simp[compile_abi_encode_child_def, rb_step_return_for]
  >- suspend "complex"
  >- simp[compile_abi_encode_child_def, rb_step_return_for]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume rb_abi_encode_for[child]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `dyn` >> simp[] >- (
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
    reverse conj_tac >- metis_tac[] >>
    gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  metis_tac[]
QED

Resume rb_abi_encode_for[bytes]:
  rpt strip_tac >> pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Resume rb_abi_encode_for[array]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_compile_abi_encode_dyn_static_loop_for] >>
    metis_tac[]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >> simp[rb_emit_op_for]
QED

Resume rb_abi_encode_for[complex]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >- (
    irule rb_bind_alloc_buffer_for >> BETA_TAC >>
    gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
    irule rb_step_ignore_bind_for >> conj_tac >-
      (qexists_tac `(rb_operand_ok_for source_checks)` >> metis_tac[]) >> simp[rb_emit_op_for]) >>
  irule rb_step_ignore_bind_for >> conj_tac >-
    (qexists_tac `(rb_operand_ok_for source_checks)` >> metis_tac[rb_operand_basic_for]) >>
  simp[rb_step_return_for]
QED

Resume rb_abi_encode_for[elems]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_ignore_bind_for >> conj_tac >-
    (qexists_tac `(rb_operand_ok_for source_checks)` >> metis_tac[]) >> gvs[arithmeticTheory.ADD_COMM]
QED

Resume rb_abi_encode_for[loop]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_encode_child_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_step_ignore_bind_for >> conj_tac >-
    (qexists_tac `(rb_operand_ok_for source_checks)` >> simp[rb_emit_op_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Finalise rb_abi_encode_for

Theorem rb_abi_decode_for:
  (!dst src opc bop hi info.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\
    (rb_operand_ok_for source_checks) hi /\
    (opc = CODECOPY ==> ~SND source_checks) ==>
    (rb_step_for source_checks) (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\
    (rb_operand_ok_for source_checks) hi /\
    (opc = CODECOPY ==> ~SND source_checks) ==>
    (rb_step_for source_checks) (K T) (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi info asz msz ip cnt.
    (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\
    (rb_operand_ok_for source_checks) hi /\ (rb_operand_ok_for source_checks) ip /\ (rb_operand_ok_for source_checks) cnt /\
    (opc = CODECOPY ==> ~SND source_checks) ==>
    (rb_step_for source_checks) (K T) (compile_abi_decode_dyn_loop dst src opc bop hi info asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
      irule rb_bind_abi_dec_addr_for >> BETA_TAC >>
      simp[rb_compile_abi_decode_static_for, rb_compile_abi_clamp_basetype_for])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- simp[compile_abi_decode_to_buf_def, rb_step_return_for]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume rb_abi_decode_for[complex]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >- metis_tac[] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_compile_abi_decode_range_check_for] >>
  metis_tac[]
QED

Resume rb_abi_decode_for[elems]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_getelemptr_abi_for] >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- metis_tac[] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Resume rb_abi_decode_for[bytes]:
  rpt strip_tac >> pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >>
  BETA_TAC >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return_for] >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_abi_decode_range_check_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return_for] >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_compile_abi_decode_range_check_for]) >>
  IF_CASES_TAC >- (Cases_on `opc` >> simp[rb_emit_void_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Resume rb_abi_decode_for[array]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return_for] >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_abi_decode_range_check_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return_for] >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_compile_abi_decode_range_check_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  IF_CASES_TAC >- (
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
    Cases_on `opc` >> simp[rb_emit_void_for]) >>
  irule rb_bind_alloc_buffer_for >> BETA_TAC >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >> metis_tac[]
QED

Resume rb_abi_decode_for[loop]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_abi_dec_addr_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (
    IF_CASES_TAC >> simp[rb_step_return_for, rb_compile_abi_decode_dyn_elem_ptr_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- metis_tac[] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED

Finalise rb_abi_decode_for

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_abi_int_clamp:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_int_clamp op bits signed)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_int_clamp_for))
QED

Theorem rb_compile_abi_bytes_clamp:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_bytes_clamp op m)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_bytes_clamp_for))
QED

Theorem rb_compile_abi_clamp_basetype:
  rb_operand_ok op ==> rb_step (K T) (compile_abi_clamp_basetype op info)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_clamp_basetype_for))
QED

Theorem rb_compile_abi_zero_pad:
  rb_operand_ok p /\ rb_operand_ok len /\ rb_operand_ok cnt ==>
  rb_step (K T) (compile_abi_zero_pad p len cnt)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_zero_pad_for))
QED

Theorem rb_compile_get_element_ptr:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_get_element_ptr p n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_get_element_ptr_for))
QED

Theorem rb_compile_get_dynarray_elem_ptr:
  rb_operand_ok p /\ rb_operand_ok idx ==>
  rb_step rb_operand_ok (compile_get_dynarray_elem_ptr p idx n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_get_dynarray_elem_ptr_for))
QED

Theorem rb_compile_abi_encode_static:
  rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step rb_operand_ok (compile_abi_encode_static dst src)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_encode_static_for))
QED

Theorem rb_compile_abi_decode_static:
  rb_operand_ok src /\ rb_operand_ok dst /\
  (!op. rb_operand_ok op ==> rb_step (K T) (clamp op)) ==>
  rb_step (K T) (compile_abi_decode_static src dst opc clamp)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_decode_static_for))
QED

Theorem rb_compile_abi_encode_static_info:
  rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step rb_operand_ok (compile_abi_encode_static_info dst src info)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_encode_static_info_for))
QED

Theorem rb_compile_abi_dec_addr:
  rb_operand_ok bop /\ rb_operand_ok pos ==>
  rb_step rb_operand_ok (compile_abi_dec_addr bop pos)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_dec_addr_for))
QED

Theorem rb_compile_abi_decode_range_check:
  !sop eop hi. rb_operand_ok sop /\ rb_operand_ok eop /\ rb_operand_ok hi ==>
  rb_step (K T) (compile_abi_decode_range_check sop eop hi)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_decode_range_check_for))
QED

Theorem rb_bind_abi_dec_addr:
  rb_operand_ok bop /\ rb_operand_ok pos /\
  (!op. rb_operand_ok op ==> rb_step Q (f op)) ==>
  rb_step Q (comp_bind (compile_abi_dec_addr bop pos) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_abi_dec_addr_for))
QED

Theorem rb_compile_getelemptr_abi:
  rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
  rb_step rb_operand_ok (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_getelemptr_abi_for))
QED

Theorem rb_compile_abi_decode_dyn_elem_ptr:
  rb_operand_ok bop /\ rb_operand_ok src /\ rb_operand_ok data_op /\
  rb_operand_ok hi ==>
  rb_step rb_operand_ok
    (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_decode_dyn_elem_ptr_for))
QED

Theorem rb_bind_alloc_buffer:
  (!buf. rb_buffer_ok buf ==> rb_step Q (f buf)) ==>
  rb_step Q (comp_bind (compile_alloc_buffer n) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_buffer_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_alloc_buffer_for))
QED

Theorem rb_compile_abi_encode_dyn_static_loop:
  rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok len ==>
  rb_step rb_operand_ok
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_abi_encode_dyn_static_loop_for))
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
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_abi_encode_for))
QED

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
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_abi_decode_for))
QED
