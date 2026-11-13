(* TOP-LEVEL: actual checked metadata supplies both element strides.
   Whole live-payload bounds and separation give non-wrapping, disjoint
   child footprints, including zero-sized element layouts. *)
Theory typedArrayLoopSafety
Ancestors
  typedDynLoopInvariant typedArrayCopyMemory typeLayoutProps typedCopyProducer
  compileVyper compileEnv vyperTypeContract vyperContext vyperValue valueEncoding
  venomState list words arithmetic

Theorem checked_array_copy_element_safety:
  !tops in_deploy layouts addr art cenv fty aty ftv atv (src_data:bytes32) (dst_data:bytes32) copy_count i.
    let src_word = src_data + n2w i * n2w (type_memory_bytes cenv aty) in
    let dst_word = dst_data + n2w i * n2w (type_memory_bytes cenv fty) in
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    i < copy_count /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) ==>
    type_memory_bytes cenv fty = type_memory_size ftv /\
    type_memory_bytes cenv aty = type_memory_size atv /\
    w2n src_word = w2n src_data + i * type_memory_size atv /\
    w2n dst_word = w2n dst_data + i * type_memory_size ftv /\
    w2n src_word + type_memory_size atv < dimword(:256) /\
    w2n dst_word + type_memory_size ftv < dimword(:256) /\
    (w2n src_word + type_memory_size atv <= w2n dst_word \/
      w2n dst_word + type_memory_size ftv <= w2n src_word)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `fty`, `ftv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `aty`, `atv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`(src_data:bytes32)`, `copy_count`, `i`, `type_memory_size atv`] array_copy_element_pointer_fit) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`(dst_data:bytes32)`, `copy_count`, `i`, `type_memory_size ftv`] array_copy_element_pointer_fit) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`w2n (src_data:bytes32)`, `w2n (dst_data:bytes32)`, `copy_count`,
    `type_memory_size atv`, `type_memory_size ftv`, `i`, `i`] array_copy_elements_disjoint) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (qpat_x_assum `w2n (src_data + _ * _) + _ < _` mp_tac >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `w2n (dst_data + _ * _) + _ < _` mp_tac >> asm_simp_tac bool_ss []
QED
