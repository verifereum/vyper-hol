(* Symbolic leaf probes for the retained encoder region. *)
Theory exprSimAbiEncodeProducer
Ancestors
  exprSimAbiEncodeControl exprSimAbiEncodeRegionTransfer abiEncoderObserverCode
  abiEncoderArrayLoopLayout abiEncoderPhi abiEncoderCounters
  fragExec compileEnv emitHelper venomInst list rich_list arithmetic

Definition encode_linear_region_def:
  encode_linear_region lbl lo hi = {(lbl,idx) | lo <= idx /\ idx <= hi}
End

Theorem encode_linear_certificate:
  EVERY (\i. MEM i.inst_opcode
    [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; AND; MCOPY] ) code ==>
  encode_region_certificate
    [<|bb_label := lbl; bb_instructions := pre ++ code ++ [mk_inst k STOP [] []]|>]
    (lbl,LENGTH code + LENGTH pre)
    (encode_linear_region lbl (LENGTH pre) (LENGTH code + LENGTH pre))
Proof
  strip_tac >> pure_rewrite_tac [encode_region_certificate_def] >> conj_tac
  >- (simp[lookup_block_def, FIND_thm, get_instruction_def, EL_APPEND_EQN] >>
      qexists_tac `k` >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> simp[encode_linear_region_def] >> strip_tac >>
      qexistsl_tac [`<|bb_label := lbl; bb_instructions := pre ++ code ++ [mk_inst k STOP [] []]|>`,
        `EL (idx - LENGTH pre) code`] >>
      simp[lookup_block_def, FIND_thm, get_instruction_def, EL_APPEND_EQN] >>
      `idx < LENGTH pre + LENGTH code /\ idx - LENGTH pre < LENGTH code` by (gvs[] >> decide_tac) >>
      gvs[EVERY_EL] >> first_x_assum (qspec_then `idx - LENGTH pre` mp_tac) >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(_,_) IN encode_linear_region _ _ _` mp_tac >>
  simp[encode_linear_region_def] >> strip_tac >> gvs[] >>
  `idx < LENGTH pre + LENGTH code` by (gvs[] >> decide_tac) >>
  gvs[lookup_block_def, FIND_thm, get_instruction_def, EL_APPEND_EQN] >>
  qpat_x_assum `EVERY _ code` mp_tac >> rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `idx - LENGTH pre` mp_tac) >>
  simp[] >> strip_tac >> gvs[is_terminator_def, encode_linear_region_def]
QED

Theorem encode_linear_producer:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\ code <> [] /\
  EVERY (\i. MEM i.inst_opcode
    [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; AND; MCOPY]) code ==>
  let obs = encode_retained_observer fn sa sb k in
  let cut = (sb.cs_current_bb,LENGTH sb.cs_current_insts) in
  let R = encode_linear_region sa.cs_current_bb (LENGTH sa.cs_current_insts)
    (LENGTH sb.cs_current_insts) in
    encode_region_certificate obs.fn_blocks cut R /\
    (sa.cs_current_bb,LENGTH sa.cs_current_insts) IN R /\
    fn_has_code sa sb obs /\
    (!idx. (sb.cs_current_bb,idx) IN R /\ (sb.cs_current_bb,idx) <> cut ==>
       idx < LENGTH sb.cs_current_insts) /\
    EXISTS (\i. i.inst_opcode <> PHI) sb.cs_current_insts
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >> rpt conj_tac
  >- (simp[encode_retained_observer_def, emitted_blocks_def] >>
      irule encode_linear_certificate >> simp[])
  >- simp[encode_linear_region_def]
  >- simp[fn_has_code_def, encode_retained_observer_def, emitted_blocks_def,
          lookup_block_def, FIND_thm, IS_PREFIX_APPEND]
  >- (simp[encode_linear_region_def] >> rpt strip_tac >> gvs[])
  >> Cases_on `code` >> gvs[] >>
  qpat_x_assum `EVERY _ _` mp_tac >> simp[mk_inst_def] >> strip_tac >> gvs[]
QED

Theorem encode_word_producer:
  compile_abi_encode_to_buf dst src AbiPrimWord sa = (out,sb) ==>
  let obs = encode_retained_observer fn sa sb k in
  let cut = (sb.cs_current_bb,LENGTH sb.cs_current_insts) in
  let R = encode_linear_region sa.cs_current_bb (LENGTH sa.cs_current_insts)
    (LENGTH sb.cs_current_insts) in
    encode_region_certificate obs.fn_blocks cut R /\
    (sa.cs_current_bb,LENGTH sa.cs_current_insts) IN R /\
    fn_has_code sa sb obs /\
    (!idx. (sb.cs_current_bb,idx) IN R /\ (sb.cs_current_bb,idx) <> cut ==>
       idx < LENGTH sb.cs_current_insts) /\
    EXISTS (\i. i.inst_opcode <> PHI) sb.cs_current_insts
Proof
  strip_tac >> drule abi_word_compiler_shape >> strip_tac >>
  irule encode_linear_producer >> simp[mk_inst_def] >> metis_tac[]
QED

Theorem encode_copy_bytes_shape:
  (ei = AbiCopy n \/ ei = AbiBytestring n) /\
  compile_abi_encode_to_buf dst src ei sa = (out,sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\ code <> [] /\
    EVERY (\i. MEM i.inst_opcode
      [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; AND; MCOPY]) code
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem encode_copy_bytes_producer:
  (ei = AbiCopy n \/ ei = AbiBytestring n) /\
  compile_abi_encode_to_buf dst src ei sa = (out,sb) ==>
  let obs = encode_retained_observer fn sa sb k in
  let cut = (sb.cs_current_bb,LENGTH sb.cs_current_insts) in
  let R = encode_linear_region sa.cs_current_bb (LENGTH sa.cs_current_insts)
    (LENGTH sb.cs_current_insts) in
    encode_region_certificate obs.fn_blocks cut R /\
    (sa.cs_current_bb,LENGTH sa.cs_current_insts) IN R /\
    fn_has_code sa sb obs /\
    (!idx. (sb.cs_current_bb,idx) IN R /\ (sb.cs_current_bb,idx) <> cut ==>
       idx < LENGTH sb.cs_current_insts) /\
    EXISTS (\i. i.inst_opcode <> PHI) sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >>
  drule_all encode_copy_bytes_shape >> strip_tac >>
  irule encode_linear_producer >> metis_tac[]
QED

(* Identity regions are essential: empty complex compilation emits no
   non-PHI instruction.  The general producer must not demand nonempty
   output or a non-PHI prefix from every recursive call. *)
Theorem encode_empty_complex_shape:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) ==>
    out = Lit 0w /\ sb = sa
Proof
  simp[Once abiEncoderTheory.compile_abi_encode_child_def, comp_return_def]
QED

Theorem encode_identity_certificate:
  encode_region_certificate
    [<|bb_label := lbl; bb_instructions := pre ++ [mk_inst k STOP [] []]|>]
    (lbl,LENGTH pre) (encode_linear_region lbl (LENGTH pre) (LENGTH pre))
Proof
  mp_tac (Q.INST [`code` |-> `[]`] encode_linear_certificate) >> simp[]
QED
