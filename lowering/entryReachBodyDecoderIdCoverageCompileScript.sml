Theory entryReachBodyDecoderIdCoverageCompile
Ancestors
  entryReachBodyDecoderIdCoverage abiEncoder abiDecoderContract compileEnv
  emitHelper context venomInst

val coverage_simps = [entry_decoder_id_coverage_emit_op,
  entry_decoder_id_coverage_emit_void, entry_decoder_id_coverage_emit_inst,
  entry_decoder_id_coverage_return, entry_decoder_id_coverage_fresh_label,
  entry_decoder_id_coverage_new_block, entry_decoder_id_coverage_alloc_buffer];
val coverage_db = fn t => rpt gen_tac >>
  ho_match_mp_tac entry_decoder_id_coverage_bind >>
  conj_tac >- simp (t::coverage_simps) >> rpt strip_tac;
val coverage_dib = fn t =>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >>
  conj_tac >- simp (t::coverage_simps) >> rpt strip_tac;

Theorem entry_decoder_id_coverage_clamp:
  !c v st. entry_decoder_id_coverage st
    (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
      compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
      entry_decoder_id_coverage_return] >> rpt gen_tac
  >- (IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void])
  >- (ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void]) >>
  ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
  simp[entry_decoder_id_coverage_emit_void]
QED

Theorem entry_decoder_id_coverage_static:
  opc <> ALLOCA /\
  (!v st. entry_decoder_id_coverage st (SND (clamp v st))) ==>
  !st. entry_decoder_id_coverage st
    (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  coverage_db entry_decoder_id_coverage_emit_op >>
  coverage_dib entry_decoder_id_coverage_refl >>
  simp[entry_decoder_id_coverage_emit_void]
QED

Theorem entry_decoder_id_coverage_getelemptr:
  opc <> ALLOCA ==>
  !st. entry_decoder_id_coverage st
    (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st))
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  coverage_db entry_decoder_id_coverage_emit_op >> Cases_on `dyn` >>
  simp[entry_decoder_id_coverage_return] >>
  ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[entry_decoder_id_coverage_return] >>
      ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void]) >>
  simp[entry_decoder_id_coverage_return]
QED

Theorem entry_decoder_id_coverage_dyn_elem_ptr:
  opc <> ALLOCA ==>
  !st. entry_decoder_id_coverage st
    (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[entry_decoder_id_coverage_return] >>
      ntac 2 (coverage_db entry_decoder_id_coverage_emit_op) >>
      coverage_dib entry_decoder_id_coverage_emit_void >>
      ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void]) >>
  simp[entry_decoder_id_coverage_return]
QED

Theorem entry_decoder_id_coverage_mutual:
  (!dst src opc hi info. opc <> ALLOCA ==>
     !st. entry_decoder_id_coverage st
       (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st))) /\
  (!dst src opc hi elems ao vo. opc <> ALLOCA ==>
     !st. entry_decoder_id_coverage st
       (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st))) /\
  (!dst src opc hi ei asz msz ip cnt. opc <> ALLOCA ==>
     !st. entry_decoder_id_coverage st
       (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)))
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

Resume entry_decoder_id_coverage_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule entry_decoder_id_coverage_static >> simp[entry_decoder_id_coverage_clamp]
QED
Resume entry_decoder_id_coverage_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[entry_decoder_id_coverage_return] >>
      ntac 4 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void]) >>
  rpt strip_tac >> Cases_on `opc` >> simp[entry_decoder_id_coverage_emit_void]
QED
Resume entry_decoder_id_coverage_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[entry_decoder_id_coverage_return] >>
      ntac 5 (coverage_db entry_decoder_id_coverage_emit_op) >>
      simp[entry_decoder_id_coverage_emit_void]) >>
  rpt strip_tac >> coverage_db entry_decoder_id_coverage_emit_op >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
      Cases_on `opc` >> simp[entry_decoder_id_coverage_emit_void]) >>
  coverage_db entry_decoder_id_coverage_alloc_buffer >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume entry_decoder_id_coverage_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume entry_decoder_id_coverage_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[entry_decoder_id_coverage_return]
QED
Resume entry_decoder_id_coverage_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  coverage_db entry_decoder_id_coverage_getelemptr >>
  coverage_db entry_decoder_id_coverage_emit_op >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume entry_decoder_id_coverage_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (coverage_db entry_decoder_id_coverage_fresh_label) >>
  coverage_dib entry_decoder_id_coverage_emit_inst >>
  coverage_dib entry_decoder_id_coverage_new_block >>
  ntac 4 (coverage_db entry_decoder_id_coverage_emit_op) >>
  coverage_dib entry_decoder_id_coverage_emit_inst >>
  coverage_dib entry_decoder_id_coverage_new_block >>
  ntac 4 (coverage_db entry_decoder_id_coverage_emit_op) >>
  ho_match_mp_tac entry_decoder_id_coverage_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[entry_decoder_id_coverage_dyn_elem_ptr,
                          entry_decoder_id_coverage_return]) >>
  rpt strip_tac >> ntac 3 (coverage_db entry_decoder_id_coverage_emit_op) >>
  ho_match_mp_tac entry_decoder_id_coverage_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> coverage_db entry_decoder_id_coverage_emit_op >>
  coverage_dib entry_decoder_id_coverage_emit_void >>
  coverage_dib entry_decoder_id_coverage_emit_inst >>
  coverage_dib entry_decoder_id_coverage_new_block >>
  simp[entry_decoder_id_coverage_return]
QED
Finalise entry_decoder_id_coverage_mutual

Theorem entry_decoder_to_buf_id_coverage:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st = ((),st') /\
  abi_decode_source_opcode opc ==>
  entry_decoder_id_coverage st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 1 entry_decoder_id_coverage_mutual, pairTheory.SND]
QED

Theorem entry_decoder_complex_elems_id_coverage:
  compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st = ((),st') /\
  abi_decode_source_opcode opc ==>
  entry_decoder_id_coverage st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 2 entry_decoder_id_coverage_mutual, pairTheory.SND]
QED

Theorem entry_decoder_dyn_loop_id_coverage:
  compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st = ((),st') /\
  abi_decode_source_opcode opc ==>
  entry_decoder_id_coverage st st'
Proof
  strip_tac >> `opc <> ALLOCA` by gvs[abi_decode_source_opcode_def] >>
  metis_tac[cj 3 entry_decoder_id_coverage_mutual, pairTheory.SND]
QED
