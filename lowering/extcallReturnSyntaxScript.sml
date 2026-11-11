(* Compiler-only closure facts for counted return decoding. *)
Theory extcallReturnSyntax
Ancestors
  extcallReturnDecoderCode abiDecoderVarSequence exprSimAbiGasBridge abiEncoder
  abiDecoderAppend
  exprLoweringProps compileEnv venomInst emitHelper context fragExec list rich_list

Theorem return_decoder_ops_free:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) ==>
  frag_ops_free st en
Proof
  strip_tac >> drule return_decoder_frag_code >>
  simp[frag_ops_free_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[abi_decoder_reentry_opcode_def] >>
  strip_tac >> gvs[]
QED

(* Chronological instruction supply; initial prefixes may be arbitrary. *)
Definition return_id_trace_def:
  return_id_trace st en <=>
    st.cs_next_id <= en.cs_next_id /\
    MAP (\i. i.inst_id) (return_code_trace en) =
      MAP (\i. i.inst_id) (return_code_trace st) ++
      GENLIST (\k. st.cs_next_id + k) (en.cs_next_id - st.cs_next_id)
End

Theorem return_id_trace_refl:
  return_id_trace st st
Proof
  simp[return_id_trace_def]
QED

Theorem return_id_trace_trans:
  return_id_trace st mid /\ return_id_trace mid en ==>
  return_id_trace st en
Proof
  rw[return_id_trace_def] >>
  `en.cs_next_id - st.cs_next_id =
    (en.cs_next_id - mid.cs_next_id) +
    (mid.cs_next_id - st.cs_next_id)` by decide_tac >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[listTheory.GENLIST_APPEND] >>
  simp[arithmeticTheory.ADD_ASSOC]
QED

Theorem return_id_trace_return:
  return_id_trace st (SND (comp_return v st))
Proof
  simp[comp_return_def, return_id_trace_refl]
QED

Theorem return_id_trace_bind:
  (!st. return_id_trace st (SND (f st))) /\
  (!v st. return_id_trace st (SND (g v st))) ==>
  return_id_trace st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule return_id_trace_trans >> metis_tac[pairTheory.SND]
QED

Theorem return_id_trace_ignore_bind:
  (!st. return_id_trace st (SND (f st))) /\
  (!st. return_id_trace st (SND (g st))) ==>
  return_id_trace st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_id_trace_bind >> simp[]
QED

Theorem return_id_trace_emit_op:
  return_id_trace st (SND (emit_op opc ops st))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, return_id_trace_def,
    return_code_trace_def, mk_inst_def]
QED

Theorem return_id_trace_emit_void:
  return_id_trace st (SND (emit_void opc ops st))
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, return_id_trace_def, return_code_trace_def, mk_inst_def]
QED

Theorem return_id_trace_emit_inst:
  return_id_trace st (SND (emit_inst opc ops outs st))
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, return_id_trace_def, return_code_trace_def, mk_inst_def]
QED

Theorem return_id_trace_fresh_label:
  return_id_trace st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, return_id_trace_def, return_code_trace_def]
QED

Theorem return_id_trace_new_block:
  return_id_trace st (SND (new_block name st))
Proof
  simp[new_block_def, return_id_trace_def, return_code_trace_def,
    MAP_APPEND, FLAT_APPEND]
QED

Theorem return_id_trace_alloc_buffer:
  return_id_trace st (SND (compile_alloc_buffer sz st))
Proof
  rewrite_tac[compile_alloc_buffer_def] >> irule return_id_trace_bind >>
  simp[return_id_trace_emit_op, return_id_trace_return]
QED

val id_simps = [return_id_trace_emit_op, return_id_trace_emit_void,
  return_id_trace_emit_inst, return_id_trace_return, return_id_trace_fresh_label,
  return_id_trace_new_block, return_id_trace_alloc_buffer];
val id_db = fn t => rpt gen_tac >> ho_match_mp_tac return_id_trace_bind >>
  conj_tac >- simp (t::id_simps) >> rpt strip_tac;
val id_dib = fn t => ho_match_mp_tac return_id_trace_ignore_bind >>
  conj_tac >- simp (t::id_simps) >> rpt strip_tac;

Theorem return_id_trace_addr:
  !st. return_id_trace st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp id_simps
QED

Theorem return_id_trace_range:
  !st. return_id_trace st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (id_db return_id_trace_emit_op) >> simp id_simps
QED

Theorem return_id_trace_clamp:
  !c v st. return_id_trace st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, return_id_trace_return] >>
  rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (id_db return_id_trace_emit_op) >> simp id_simps
QED

Theorem return_id_trace_static:
  (!v st. return_id_trace st (SND (clamp v st))) ==>
  !st. return_id_trace st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >> gen_tac >>
  id_db return_id_trace_emit_op >> id_dib return_id_trace_refl >> simp id_simps
QED

Theorem return_id_trace_getelemptr:
  !st. return_id_trace st
    (SND (compile_getelemptr_abi src dyn off opc base_op hi st))
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  id_db return_id_trace_emit_op >> Cases_on `dyn` >> simp[return_id_trace_return] >>
  id_db return_id_trace_addr >> ntac 2 (id_db return_id_trace_emit_op) >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_id_trace_return] >>
      ntac 2 (id_db return_id_trace_emit_op) >> simp id_simps) >>
  simp[return_id_trace_return]
QED

Theorem return_id_trace_dyn_elem_ptr:
  !st. return_id_trace st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  id_db return_id_trace_addr >> ntac 2 (id_db return_id_trace_emit_op) >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_id_trace_return] >>
      ntac 2 (id_db return_id_trace_emit_op) >> id_dib return_id_trace_emit_void >>
      id_db return_id_trace_emit_op >> simp[return_id_trace_range]) >>
  simp[return_id_trace_return]
QED

Theorem return_id_trace_decoder_mutual:
  (!dst src opc base_op hi info st. return_id_trace st
       (SND (compile_abi_decode_to_buf dst src opc base_op hi info st))) /\
  (!dst src opc base_op hi elems ao vo st. return_id_trace st
       (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st))) /\
  (!dst src opc base_op hi ei asz msz ip cnt st. return_id_trace st
       (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)))
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

Resume return_id_trace_decoder_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  id_db return_id_trace_addr >>
  irule return_id_trace_static >> simp[return_id_trace_clamp]
QED
Resume return_id_trace_decoder_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_id_trace_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_id_trace_return] >>
      id_db return_id_trace_emit_op >> id_dib return_id_trace_range >>
      simp[return_id_trace_return]) >>
  rpt strip_tac >> id_db return_id_trace_addr >>
  ntac 3 (id_db return_id_trace_emit_op) >> id_dib return_id_trace_emit_void >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_id_trace_return] >>
      id_db return_id_trace_emit_op >> simp[return_id_trace_range]) >>
  rpt strip_tac >> IF_CASES_TAC
  >- (Cases_on `opc` >> simp id_simps) >>
  ntac 4 (id_db return_id_trace_emit_op) >> id_dib return_id_trace_emit_void >>
  id_db return_id_trace_emit_op >> simp id_simps
QED
Resume return_id_trace_decoder_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_id_trace_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_id_trace_return] >>
      id_db return_id_trace_emit_op >> id_dib return_id_trace_range >>
      simp[return_id_trace_return]) >>
  rpt strip_tac >> id_db return_id_trace_addr >>
  ntac 3 (id_db return_id_trace_emit_op) >> id_dib return_id_trace_emit_void >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_id_trace_return] >>
      ntac 2 (id_db return_id_trace_emit_op) >> simp[return_id_trace_range]) >>
  rpt strip_tac >> id_db return_id_trace_emit_op >> id_dib return_id_trace_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (id_db return_id_trace_emit_op) >> id_db return_id_trace_addr >>
      id_db return_id_trace_emit_op >> Cases_on `opc` >> simp id_simps) >>
  id_db return_id_trace_alloc_buffer >> id_dib return_id_trace_emit_void >>
  first_x_assum irule
QED
Resume return_id_trace_decoder_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  id_db return_id_trace_emit_op >> id_dib return_id_trace_range >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume return_id_trace_decoder_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[return_id_trace_return]
QED
Resume return_id_trace_decoder_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  id_db return_id_trace_getelemptr >> id_db return_id_trace_emit_op >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume return_id_trace_decoder_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (id_db return_id_trace_fresh_label) >>
  id_dib return_id_trace_emit_inst >> id_dib return_id_trace_new_block >>
  id_db return_id_trace_emit_op >> id_db return_id_trace_addr >>
  ntac 3 (id_db return_id_trace_emit_op) >>
  id_dib return_id_trace_emit_inst >> id_dib return_id_trace_new_block >>
  ntac 4 (id_db return_id_trace_emit_op) >>
  ho_match_mp_tac return_id_trace_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_id_trace_dyn_elem_ptr, return_id_trace_return]) >>
  rpt strip_tac >> ntac 3 (id_db return_id_trace_emit_op) >>
  ho_match_mp_tac return_id_trace_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> id_db return_id_trace_emit_op >>
  id_dib return_id_trace_emit_void >> id_dib return_id_trace_emit_inst >>
  id_dib return_id_trace_new_block >> simp[return_id_trace_return]
QED
Finalise return_id_trace_decoder_mutual

Theorem return_id_trace_distinct:
  cs_extends st en /\ return_id_trace st en ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code st en))
Proof
  simp_tac bool_ss [cs_extends_def, return_id_trace_def, return_code_trace_def] >>
  strip_tac >>
  `ALL_DISTINCT (GENLIST (\k. st.cs_next_id + k)
    (en.cs_next_id - st.cs_next_id))` by simp[ALL_DISTINCT_GENLIST] >>
  Cases_on `new = []`
  >- (gvs[frag_code_def, emitted_blocks_def, emitted_insts_def,
          IS_PREFIX_APPEND, DROP_LENGTH_APPEND]) >>
  gvs[frag_code_def, emitted_blocks_def, TAKE_LENGTH_APPEND, NULL_EQ,
      MAP_APPEND, FLAT_APPEND, REVERSE_APPEND, IS_PREFIX_APPEND] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[listTheory.APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  gvs[DROP_LENGTH_APPEND] >>
  qpat_x_assum `_ = GENLIST _ _` (fn th =>
    qpat_x_assum `ALL_DISTINCT (GENLIST _ _)`
      (mp_tac o PURE_REWRITE_RULE [GSYM th])) >>
  simp[MAP_FLAT, MAP_REVERSE, ALL_DISTINCT_APPEND,
       MEM_FLAT, MEM_MAP, MEM_REVERSE] >> metis_tac[]
QED

Theorem return_decoder_fragment_ids:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code st en))
Proof
  strip_tac >> irule return_id_trace_distinct >>
  metis_tac[cj 1 return_id_trace_decoder_mutual,
    cs_extends_abi_decode, pairTheory.SND]
QED
