Theory exprSimAbiDecodeCoverageMutual
Ancestors
  exprSimAbiDecodeCoverageActions exprSimAbiGasBridge abiEncoder builtinAbi
  compileEnv emitHelper context venomInst pair list arithmetic

val coverage_simps = [abi_decode_id_coverage_return, abi_decode_id_coverage_prims];
val COVERAGE_BIND_WITH = fn extra => ho_match_mp_tac abi_decode_id_coverage_bind >> conj_tac
  >- simp (extra @ coverage_simps) >> rpt gen_tac;
val COVERAGE_BIND = COVERAGE_BIND_WITH [];
val COVERAGE_IGNORE = ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- simp coverage_simps;

Theorem abi_decode_id_coverage_mutual:
  (!dst src opc base_op hi info. abi_decode_id_coverage (compile_abi_decode_to_buf dst src opc base_op hi info)) /\
  (!dst src opc base_op hi elems ao vo.
    abi_decode_id_coverage (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo)) /\
  (!dst src opc base_op hi ei asz msz ip cnt.
    abi_decode_id_coverage (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume abi_decode_id_coverage_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >>
  irule abi_decode_id_coverage_static >> simp[abi_decode_id_coverage_clamp]
QED

Resume abi_decode_id_coverage_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_head_check] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >>
  ntac 3 COVERAGE_BIND >> COVERAGE_IGNORE >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_id_coverage_return] >>
      COVERAGE_BIND >> simp[abi_decode_id_coverage_range_check]) >>
  IF_CASES_TAC
  >- (Cases_on `opc` >> simp coverage_simps) >>
  ntac 4 COVERAGE_BIND >> COVERAGE_IGNORE >> COVERAGE_BIND >> simp coverage_simps
QED

Resume abi_decode_id_coverage_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_head_check] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >>
  ntac 3 COVERAGE_BIND >> COVERAGE_IGNORE >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_id_coverage_return] >>
      ntac 2 COVERAGE_BIND >> simp[abi_decode_id_coverage_range_check]) >>
  COVERAGE_BIND >> COVERAGE_IGNORE >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 COVERAGE_BIND >> COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >>
      COVERAGE_BIND >> Cases_on `opc` >> simp coverage_simps) >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_alloc_buffer] >>
  COVERAGE_IGNORE >> first_x_assum irule >> simp[]
QED

Resume abi_decode_id_coverage_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
        mp_tac) >> simp[]) >>
  COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- simp[abi_decode_id_coverage_range_check] >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
    mp_tac) >> simp[]
QED

Resume abi_decode_id_coverage_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[abi_decode_id_coverage_return]
QED

Resume abi_decode_id_coverage_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_member_pointer] >>
  COVERAGE_BIND >> ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED

Resume abi_decode_id_coverage_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> ntac 3 COVERAGE_BIND >>
  COVERAGE_IGNORE >> COVERAGE_IGNORE >> COVERAGE_BIND >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >> ntac 3 COVERAGE_BIND >>
  COVERAGE_IGNORE >> COVERAGE_IGNORE >> ntac 4 COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_id_coverage_array_pointer, abi_decode_id_coverage_return]) >>
  rpt gen_tac >> ntac 3 COVERAGE_BIND >> ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  COVERAGE_BIND >> COVERAGE_IGNORE >> COVERAGE_IGNORE >> COVERAGE_IGNORE >>
  simp[abi_decode_id_coverage_return]
QED

Finalise abi_decode_id_coverage_mutual

Theorem abi_decode_id_coverage_lower:
  abi_decode_id_coverage (lower_abi_decode data info mn mx outsz)
Proof
  rewrite_tac[lower_abi_decode_def] >> ntac 2 COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (COVERAGE_BIND >> simp coverage_simps) >>
      ntac 5 COVERAGE_BIND >> simp coverage_simps) >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_alloc_buffer] >>
  COVERAGE_BIND >> ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- simp[abi_decode_id_coverage_mutual] >> simp coverage_simps
QED

Theorem abi_decode_lower_interval_instruction:
  lower_abi_decode data info mn mx outsz a = (out,b) /\
  a.cs_next_id <= id /\ id < b.cs_next_id ==>
  ?i. MEM i (frag_code a b) /\ i.inst_id = id
Proof
  mp_tac abi_decode_id_coverage_lower >>
  simp[abi_decode_id_coverage_def] >> metis_tac[]
QED
