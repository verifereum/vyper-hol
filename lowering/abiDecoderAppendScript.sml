(* Recursive ABI decoder code only appends to the surrounding CFG. *)
Theory abiDecoderAppend
Ancestors
  abiEncoder fragExec compileEnv emitHelper venomInst context

val append_simps = [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers];
val APPEND_BIND_WITH = fn extra => ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp (extra @ append_simps) >> rpt gen_tac;
val APPEND_BIND = APPEND_BIND_WITH [];
val APPEND_IGNORE = ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp append_simps;

Theorem cs_appends_abi_clamp:
  !c v. cs_appends (compile_abi_clamp_basetype v c)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, cs_appends_return] >>
  rpt gen_tac >> TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 APPEND_BIND >> simp append_simps
QED

Theorem cs_appends_abi_static:
  (!v. cs_appends (clamp v)) ==>
  cs_appends (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  APPEND_BIND >> APPEND_IGNORE >> simp append_simps
QED

Theorem cs_appends_abi_alloc_buffer:
  cs_appends (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> APPEND_BIND >> simp append_simps
QED

Theorem cs_appends_abi_member_pointer:
  cs_appends (compile_getelemptr_abi src dyn off opc hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> APPEND_BIND >> Cases_on `dyn` >>
  simp[cs_appends_return] >> ntac 2 APPEND_BIND >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      ntac 2 APPEND_BIND >> simp append_simps) >>
  simp[cs_appends_return]
QED

Theorem cs_appends_abi_array_pointer:
  cs_appends (compile_abi_decode_dyn_elem_ptr opc src data hi sz)
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >> ntac 2 APPEND_BIND >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      ntac 2 APPEND_BIND >> APPEND_IGNORE >>
      ntac 3 APPEND_BIND >> simp append_simps) >>
  simp[cs_appends_return]
QED

Theorem cs_appends_abi_decode_mutual:
  (!dst src opc hi info. cs_appends (compile_abi_decode_to_buf dst src opc hi info)) /\
  (!dst src opc hi elems ao vo.
    cs_appends (compile_abi_decode_complex_elems dst src opc hi elems ao vo)) /\
  (!dst src opc hi ei asz msz ip cnt.
    cs_appends (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt))
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

Resume cs_appends_abi_decode_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule cs_appends_abi_static >> simp[cs_appends_abi_clamp]
QED

Resume cs_appends_abi_decode_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 APPEND_BIND >> APPEND_IGNORE >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      ntac 4 APPEND_BIND >> simp append_simps) >>
  Cases_on `opc` >> simp append_simps
QED

Resume cs_appends_abi_decode_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 APPEND_BIND >> APPEND_IGNORE >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      ntac 5 APPEND_BIND >> simp append_simps) >>
  APPEND_BIND >> APPEND_IGNORE >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 3 APPEND_BIND >> Cases_on `opc` >> simp append_simps) >>
  APPEND_BIND_WITH [cs_appends_abi_alloc_buffer] >>
  APPEND_IGNORE >> first_x_assum irule >> simp[]
QED

Resume cs_appends_abi_decode_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
        mp_tac) >> simp[]) >>
  ntac 3 APPEND_BIND >> APPEND_IGNORE >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
    mp_tac) >> simp[]
QED

Resume cs_appends_abi_decode_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[cs_appends_return]
QED

Resume cs_appends_abi_decode_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  APPEND_BIND_WITH [cs_appends_abi_member_pointer] >>
  APPEND_BIND >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED

Resume cs_appends_abi_decode_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> ntac 3 APPEND_BIND >>
  APPEND_IGNORE >> APPEND_IGNORE >> ntac 4 APPEND_BIND >>
  APPEND_IGNORE >> APPEND_IGNORE >> ntac 4 APPEND_BIND >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_abi_array_pointer, cs_appends_return]) >>
  rpt gen_tac >> ntac 3 APPEND_BIND >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  APPEND_BIND >> APPEND_IGNORE >> APPEND_IGNORE >> APPEND_IGNORE >>
  simp[cs_appends_return]
QED

Finalise cs_appends_abi_decode_mutual

Theorem cs_extends_abi_decode:
  compile_abi_decode_to_buf dst src opc hi info st = ((),st') ==> cs_extends st st'
Proof
  metis_tac[cj 1 cs_appends_abi_decode_mutual, cs_appends_def]
QED
