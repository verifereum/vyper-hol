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
    (SND (compile_getelemptr_abi src dyn off opc hi st))
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
    (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st))
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
