(* Syntactic label freedom of straight bounded return decoders. *)
Theory extcallReturnDecoderLabels
Ancestors
  extcallReturnDecoderCode abiDecoderAppend abiEncoder exprSafeOperand
  abiDecoderLoopEmit abiDecoderArraySetupInputs abiDecoderLoopSetup
  abiDecoderRecursiveLoopLayout extcallReturnStraightObserver
  exprLowering builtinSimple fragExec emitHelper emitHelperProps compileEnv
  context venomInst list rich_list

Theorem return_decode_bound_not_label:
  compile_return_value_decode mn mx st = (hi,en) ==> !l. hi <> Label l
Proof
  simp[compile_return_value_decode_def, compile_select_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emitted_insts_emit_op >> simp[]
QED

Theorem return_safe_operand_not_label:
  safe_operand st op ==> !l. op <> Label l
Proof
  Cases_on `op` >> simp[safe_operand_def]
QED

(* Compiler-only certificate: operand results, chronological code and block growth. *)
Definition return_label_syntax_def:
  return_label_syntax f R <=>
    cs_appends f /\ (!st. R (FST (f st))) /\
    !st. (SND (f st)).cs_blocks = st.cs_blocks ==>
      return_code (\i. !l. ~MEM (Label l) i.inst_operands) st (SND (f st))
End

Theorem return_label_blocks_mid[local]:
  cs_extends a b /\ cs_extends b c /\ c.cs_blocks = a.cs_blocks ==>
  b.cs_blocks = a.cs_blocks
Proof
  rw[cs_extends_def] >>
  `LENGTH new + LENGTH new' = 0` by
    (qpat_x_assum `_ = _ ++ _` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >> asm_simp_tac pure_ss [LENGTH_APPEND] >> decide_tac) >>
  gvs[]
QED

Theorem return_label_syntax_return:
  R v ==> return_label_syntax (comp_return v) R
Proof
  simp[return_label_syntax_def, cs_appends_return, comp_return_def,
    return_code_refl]
QED

Theorem return_label_syntax_bind:
  return_label_syntax f R /\
  (!v. R v ==> return_label_syntax (g v) Q) ==>
  return_label_syntax (comp_bind f g) Q
Proof
  rw[return_label_syntax_def]
  >- (rw[cs_appends_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
      irule cs_extends_trans >>
      metis_tac[cs_appends_def, pairTheory.FST, pairTheory.SND])
  >- (simp[comp_bind_def] >> pairarg_tac >> gvs[] >> metis_tac[pairTheory.FST]) >>
  fs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `f st = (v,s')` >>
  `R v` by (qpat_x_assum `!st. R _` (qspec_then `st` mp_tac) >> simp[]) >>
  qpat_x_assum `!v. R v ==> _` (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  `cs_extends st s' /\ cs_extends s' (SND (g v s'))` by
    (fs[cs_appends_def] >> metis_tac[pairTheory.PAIR]) >>
  `s'.cs_blocks = st.cs_blocks` by metis_tac[return_label_blocks_mid] >>
  irule return_code_trans >> metis_tac[pairTheory.SND]
QED

Overload return_nonlabel = ``\op. !l. op <> Label l``

Theorem return_label_syntax_emit_op:
  EVERY return_nonlabel ops ==>
  return_label_syntax (emit_op opc ops) return_nonlabel
Proof
  rw[return_label_syntax_def, cs_appends_emit_helpers]
  >- (Cases_on `emit_op opc ops st` >> drule emitted_insts_emit_op >> simp[]) >>
  irule return_code_emit_op >> gvs[mk_inst_def, EVERY_MEM] >> metis_tac[]
QED

Theorem return_label_syntax_emit_void:
  EVERY return_nonlabel ops ==>
  return_label_syntax (emit_void opc ops) (K T)
Proof
  rw[return_label_syntax_def, cs_appends_emit_helpers] >>
  irule return_code_emit_void >> gvs[mk_inst_def, EVERY_MEM] >> metis_tac[]
QED

Theorem return_label_syntax_ignore_bind:
  return_label_syntax f (K T) /\ return_label_syntax g Q ==>
  return_label_syntax (comp_ignore_bind f g) Q
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_label_syntax_bind >> qexists_tac `K T` >> simp[]
QED

Theorem return_label_syntax_addr:
  return_nonlabel base_op /\ return_nonlabel pos ==>
  return_label_syntax (compile_abi_dec_addr base_op pos) return_nonlabel
Proof
  rw[compile_abi_dec_addr_def] >>
  simp[return_label_syntax_return, return_label_syntax_emit_op]
QED

Theorem return_label_syntax_range:
  return_nonlabel src /\ return_nonlabel e /\ return_nonlabel hi ==>
  return_label_syntax (compile_abi_decode_range_check src e hi) (K T)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (irule return_label_syntax_bind >> qexists_tac `return_nonlabel` >>
    reverse conj_tac >- simp[return_label_syntax_emit_op] >>
    gen_tac >> strip_tac >> gvs[]) >>
  simp[return_label_syntax_emit_void]
QED

val label_simps = [return_label_syntax_return, return_label_syntax_emit_op,
  return_label_syntax_emit_void];
val LABEL_BIND = fn th =>
  irule return_label_syntax_bind >> qexists_tac `return_nonlabel` >>
  reverse conj_tac >- simp (th::label_simps) >>
  gen_tac >> strip_tac >> gvs[];
val LABEL_IGNORE = fn th =>
  ho_match_mp_tac return_label_syntax_ignore_bind >>
  conj_tac >- simp (th::label_simps) >> simp_tac pure_ss [combinTheory.K_THM];

Theorem return_label_syntax_clamp:
  !c v. return_nonlabel v ==>
    return_label_syntax (compile_abi_clamp_basetype v c) (K T)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
    return_label_syntax_return] >> rpt gen_tac >> strip_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (LABEL_BIND return_label_syntax_emit_op) >> simp label_simps
QED

Theorem return_label_syntax_static:
  return_nonlabel src /\ return_nonlabel dst /\
  (!v. return_nonlabel v ==> return_label_syntax (clamp v) (K T)) ==>
  return_label_syntax (compile_abi_decode_static src dst opc clamp) (K T)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  LABEL_BIND return_label_syntax_emit_op >>
  ho_match_mp_tac return_label_syntax_ignore_bind >>
  conj_tac >- simp[] >> simp label_simps
QED

Theorem return_label_syntax_member:
  return_nonlabel src /\ return_nonlabel base_op /\ return_nonlabel hi ==>
  return_label_syntax (compile_getelemptr_abi src dyn off opc base_op hi)
    return_nonlabel
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  LABEL_BIND return_label_syntax_emit_op >> Cases_on `dyn` >> simp label_simps >>
  LABEL_BIND return_label_syntax_addr >> ntac 2 (LABEL_BIND return_label_syntax_emit_op) >>
  ho_match_mp_tac return_label_syntax_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp label_simps >>
      ntac 2 (LABEL_BIND return_label_syntax_emit_op) >> simp label_simps) >>
  simp label_simps
QED

Theorem return_label_syntax_loop:
  abi_decode_source_opcode opc ==>
  return_label_syntax
    (compile_abi_decode_dyn_loop dst src opc base_op hi di asz msz ip cnt) (K T)
Proof
  strip_tac >> rw[return_label_syntax_def, cj 3 cs_appends_abi_decode_mutual] >>
  Cases_on `compile_abi_decode_dyn_loop dst src opc base_op hi di asz msz ip cnt st` >>
  gvs[] >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
    fresh_id_def, fresh_var_def, emit_def, new_block_def] >>
  strip_tac >> gvs[cs_extends_def] >>
  qpat_x_assum `_ = _ ++ _` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
  simp[]
QED

Theorem return_label_syntax_alloc:
  return_label_syntax (compile_alloc_buffer n) (\r. return_nonlabel r.buf_operand)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> LABEL_BIND return_label_syntax_emit_op >>
  simp label_simps
QED

Theorem return_label_syntax_mutual:
  (!dst src opc base_op hi info.
     abi_decode_source_opcode opc /\ return_nonlabel dst /\ return_nonlabel src /\
     return_nonlabel base_op /\ return_nonlabel hi ==>
     return_label_syntax (compile_abi_decode_to_buf dst src opc base_op hi info) (K T)) /\
  (!dst src opc base_op hi elems ao vo.
     abi_decode_source_opcode opc /\ return_nonlabel dst /\ return_nonlabel src /\
     return_nonlabel base_op /\ return_nonlabel hi ==>
     return_label_syntax (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo) (K T)) /\
  (!dst src opc base_op hi ei asz msz ip cnt.
     abi_decode_source_opcode opc /\ return_nonlabel dst /\ return_nonlabel src /\
     return_nonlabel base_op /\ return_nonlabel hi ==>
     return_label_syntax (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt) (K T))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> simp[return_label_syntax_loop]
QED

Resume return_label_syntax_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  LABEL_BIND return_label_syntax_addr >>
  irule return_label_syntax_static >> simp[return_label_syntax_clamp]
QED

Resume return_label_syntax_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule return_label_syntax_bind >> qexists_tac `return_nonlabel` >> reverse conj_tac
  >- (IF_CASES_TAC >> simp label_simps >>
      LABEL_BIND return_label_syntax_emit_op >> LABEL_IGNORE return_label_syntax_range >>
      simp label_simps) >>
  gen_tac >> strip_tac >> gvs[] >> LABEL_BIND return_label_syntax_addr >>
  ntac 3 (LABEL_BIND return_label_syntax_emit_op) >> LABEL_IGNORE return_label_syntax_emit_void >>
  ho_match_mp_tac return_label_syntax_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp label_simps >>
      LABEL_BIND return_label_syntax_emit_op >> simp[return_label_syntax_range]) >>
  IF_CASES_TAC
  >- (Cases_on `opc` >> simp label_simps) >>
  ntac 4 (LABEL_BIND return_label_syntax_emit_op) >> LABEL_IGNORE return_label_syntax_emit_void >>
  LABEL_BIND return_label_syntax_emit_op >> simp label_simps
QED

Resume return_label_syntax_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule return_label_syntax_bind >> qexists_tac `return_nonlabel` >> reverse conj_tac
  >- (IF_CASES_TAC >> simp label_simps >>
      LABEL_BIND return_label_syntax_emit_op >> LABEL_IGNORE return_label_syntax_range >>
      simp label_simps) >>
  gen_tac >> strip_tac >> gvs[] >> LABEL_BIND return_label_syntax_addr >>
  ntac 3 (LABEL_BIND return_label_syntax_emit_op) >> LABEL_IGNORE return_label_syntax_emit_void >>
  ho_match_mp_tac return_label_syntax_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp label_simps >>
      ntac 2 (LABEL_BIND return_label_syntax_emit_op) >> simp[return_label_syntax_range]) >>
  LABEL_BIND return_label_syntax_emit_op >> LABEL_IGNORE return_label_syntax_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (ntac 2 (LABEL_BIND return_label_syntax_emit_op) >> LABEL_BIND return_label_syntax_addr >>
      LABEL_BIND return_label_syntax_emit_op >> Cases_on `opc` >> simp label_simps) >>
  irule return_label_syntax_bind >>
  qexists_tac `\r. return_nonlabel r.buf_operand` >> reverse conj_tac
  >- simp[return_label_syntax_alloc] >>
  gen_tac >> strip_tac >> gvs[] >> LABEL_IGNORE return_label_syntax_emit_void >>
  simp[return_label_syntax_loop]
QED
Resume return_label_syntax_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  LABEL_BIND return_label_syntax_emit_op >> LABEL_IGNORE return_label_syntax_range >> simp[]
QED
Resume return_label_syntax_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp label_simps
QED
Resume return_label_syntax_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  LABEL_BIND return_label_syntax_member >> LABEL_BIND return_label_syntax_emit_op >>
  ho_match_mp_tac return_label_syntax_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED
Finalise return_label_syntax_mutual

Theorem return_decoder_frag_nonlabel:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) /\
  st.cs_blocks = en.cs_blocks /\
  (!l. dst <> Label l /\ src <> Label l /\ base_op <> Label l /\ hi <> Label l) ==>
  EVERY (\i. !l. ~MEM (Label l) i.inst_operands) (frag_code st en)
Proof
  strip_tac >>
  `return_label_syntax (compile_abi_decode_to_buf dst src MLOAD base_op hi info) (K T)` by
    (irule (cj 1 return_label_syntax_mutual) >>
     simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >> metis_tac[]) >>
  irule return_code_frag >>
  fs[return_label_syntax_def, cs_appends_def] >>
  metis_tac[pairTheory.SND]
QED

Theorem return_decoder_straight_gas_free:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) /\
  st.cs_blocks = en.cs_blocks /\
  (!l. dst <> Label l /\ src <> Label l /\ base_op <> Label l /\ hi <> Label l) ==>
  frag_gas_free st en
Proof
  strip_tac >>
  `cs_extends st en` by metis_tac[cs_extends_abi_decode] >>
  drule_all return_straight_shape >> strip_tac >>
  drule_all return_decoder_frag_nonlabel >> strip_tac >>
  drule return_decoder_frag_code >> strip_tac >>
  simp[exprSimAbiGasBridgeTheory.frag_gas_free_def, EVERY_MEM] >>
  gen_tac >> strip_tac >>
  fs[EVERY_MEM] >>
  first_x_assum drule >>
  simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
