Theory extcallReturnDecoderOwnership
Ancestors
  abiMalformedRecursiveInterface localPtrsProps extcallReturnDecoderCode extcallReturnSyntax exprSimAbiGasBridge abiEncoder compileEnv exprLoweringProps fragExec emitHelper
  abiDecoderCode abiDecoderAppend abiDecoderVarSequence exprLowering context venomInst list rich_list

Definition return_alloca_owned_def:
  return_alloca_owned k i <=>
    (i.inst_opcode = ALLOCA ==>
     ?n. k <= n /\ i.inst_outputs = ["%" ++ toString n])
End

Definition return_owned_def:
  return_owned k st en <=>
    (k <= st.cs_next_var ==>
     k <= en.cs_next_var /\ return_code (return_alloca_owned k) st en)
End

Theorem return_owned_return:
  return_owned k st (SND (comp_return v st))
Proof
  simp[return_owned_def, comp_return_def, return_code_refl]
QED

Theorem return_owned_bind:
  (!st. return_owned k st (SND (f st))) /\
  (!v st. return_owned k st (SND (g v st))) ==>
  return_owned k st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> gvs[return_owned_def] >>
  metis_tac[return_code_trans, pairTheory.SND]
QED

Theorem return_owned_ignore_bind:
  (!st. return_owned k st (SND (f st))) /\
  (!st. return_owned k st (SND (g st))) ==>
  return_owned k st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule return_owned_bind >> simp[]
QED

Theorem return_owned_emit_op:
  return_owned k st (SND (emit_op opc ops st))
Proof
  rw[return_owned_def] >-
    simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  irule return_code_emit_op >> simp[return_alloca_owned_def, mk_inst_def] >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem return_owned_alloc_buffer:
  return_owned k st (SND (compile_alloc_buffer sz st))
Proof
  simp[compile_alloc_buffer_def] >> irule return_owned_bind >>
  simp[return_owned_emit_op, return_owned_return]
QED

Theorem return_owned_emit_void:
  opc <> ALLOCA ==> return_owned k st (SND (emit_void opc ops st))
Proof
  rw[return_owned_def] >-
    simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, emit_def] >>
  irule return_code_emit_void >> simp[return_alloca_owned_def, mk_inst_def]
QED

Theorem return_owned_emit_inst:
  opc <> ALLOCA ==> return_owned k st (SND (emit_inst opc ops outs st))
Proof
  rw[return_owned_def] >-
    simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, emit_def] >>
  irule return_code_emit_inst >> simp[return_alloca_owned_def, mk_inst_def]
QED

Theorem return_owned_fresh_label:
  return_owned k st (SND (fresh_label name st))
Proof
  simp[return_owned_def, fresh_label_def, return_code_def, return_code_trace_def] >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED

Theorem return_owned_new_block:
  return_owned k st (SND (new_block name st))
Proof
  simp[return_owned_def, new_block_def, return_code_def, return_code_trace_def] >>
  strip_tac >> qexists_tac `[]` >> simp[MAP_APPEND, FLAT_APPEND]
QED

val owned_simps = [return_owned_emit_op, return_owned_emit_void,
  return_owned_emit_inst, return_owned_return, return_owned_fresh_label,
  return_owned_new_block, return_owned_alloc_buffer];
val owned_db = fn t => rpt gen_tac >> ho_match_mp_tac return_owned_bind >>
  conj_tac >- simp (t::owned_simps) >> rpt strip_tac;
val owned_dib = fn t => ho_match_mp_tac return_owned_ignore_bind >>
  conj_tac >- simp (t::owned_simps) >> rpt strip_tac;

Theorem return_owned_addr:
  !st. return_owned k st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp owned_simps
QED

Theorem return_owned_range:
  !st. return_owned k st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (owned_db return_owned_emit_op) >> simp owned_simps
QED

Theorem return_owned_clamp:
  !c v st. return_owned k st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, return_owned_return] >>
  rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (owned_db return_owned_emit_op) >> simp owned_simps
QED

Theorem return_owned_static:
  (!v st. return_owned k st (SND (clamp v st))) ==>
  !st. return_owned k st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  owned_db return_owned_emit_op >>
  owned_dib return_owned_return >> simp owned_simps
QED

Theorem return_owned_getelemptr:
  !st. return_owned k st
    (SND (compile_getelemptr_abi src dyn off opc base_op hi st))
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  owned_db return_owned_emit_op >> Cases_on `dyn` >> simp[return_owned_return] >>
  owned_db return_owned_addr >> ntac 2 (owned_db return_owned_emit_op) >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_owned_return] >>
      ntac 2 (owned_db return_owned_emit_op) >> simp owned_simps) >>
  simp[return_owned_return]
QED

Theorem return_owned_dyn_elem_ptr:
  !st. return_owned k st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  owned_db return_owned_addr >> ntac 2 (owned_db return_owned_emit_op) >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_owned_return] >>
      ntac 2 (owned_db return_owned_emit_op) >> owned_dib return_owned_emit_void >>
      owned_db return_owned_emit_op >> simp[return_owned_range]) >>
  simp[return_owned_return]
QED

Theorem return_owned_mutual:
  (!dst src opc base_op hi info. opc <> ALLOCA ==>
     !st. return_owned k st
       (SND (compile_abi_decode_to_buf dst src opc base_op hi info st))) /\
  (!dst src opc base_op hi elems ao vo. opc <> ALLOCA ==>
     !st. return_owned k st
       (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st))) /\
  (!dst src opc base_op hi ei asz msz ip cnt. opc <> ALLOCA ==>
     !st. return_owned k st
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

Resume return_owned_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  owned_db return_owned_addr >>
  irule return_owned_static >> simp[return_owned_clamp]
QED
Resume return_owned_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_owned_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_owned_return] >>
      owned_db return_owned_emit_op >> owned_dib return_owned_range >>
      simp[return_owned_return]) >>
  rpt strip_tac >> owned_db return_owned_addr >>
  ntac 3 (owned_db return_owned_emit_op) >> owned_dib return_owned_emit_void >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_owned_return] >>
      owned_db return_owned_emit_op >> simp[return_owned_range]) >>
  rpt strip_tac >> IF_CASES_TAC
  >- (Cases_on `opc` >> simp owned_simps) >>
  ntac 4 (owned_db return_owned_emit_op) >> owned_dib return_owned_emit_void >>
  owned_db return_owned_emit_op >> simp owned_simps
QED
Resume return_owned_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_owned_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_owned_return] >>
      owned_db return_owned_emit_op >> owned_dib return_owned_range >>
      simp[return_owned_return]) >>
  rpt strip_tac >> owned_db return_owned_addr >>
  ntac 3 (owned_db return_owned_emit_op) >> owned_dib return_owned_emit_void >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_owned_return] >>
      ntac 2 (owned_db return_owned_emit_op) >> simp[return_owned_range]) >>
  rpt strip_tac >> owned_db return_owned_emit_op >> owned_dib return_owned_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (owned_db return_owned_emit_op) >> owned_db return_owned_addr >>
      owned_db return_owned_emit_op >> Cases_on `opc` >> simp owned_simps) >>
  owned_db return_owned_alloc_buffer >> owned_dib return_owned_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume return_owned_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  owned_db return_owned_emit_op >> owned_dib return_owned_range >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume return_owned_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[return_owned_return]
QED
Resume return_owned_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  owned_db return_owned_getelemptr >> owned_db return_owned_emit_op >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume return_owned_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (owned_db return_owned_fresh_label) >>
  owned_dib return_owned_emit_inst >> owned_dib return_owned_new_block >>
  owned_db return_owned_emit_op >> owned_db return_owned_addr >>
  ntac 3 (owned_db return_owned_emit_op) >>
  owned_dib return_owned_emit_inst >> owned_dib return_owned_new_block >>
  ntac 4 (owned_db return_owned_emit_op) >>
  ho_match_mp_tac return_owned_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_owned_dyn_elem_ptr, return_owned_return]) >>
  rpt strip_tac >> ntac 3 (owned_db return_owned_emit_op) >>
  ho_match_mp_tac return_owned_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> owned_db return_owned_emit_op >>
  owned_dib return_owned_emit_void >> owned_dib return_owned_emit_inst >>
  owned_dib return_owned_new_block >> simp[return_owned_return]
QED
Finalise return_owned_mutual

Theorem return_owned_fragment:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) ==>
  EVERY (return_alloca_owned st.cs_next_var) (frag_code st en)
Proof
  strip_tac >> irule return_code_frag >>
  conj_tac >- metis_tac[cs_extends_abi_decode] >>
  `return_owned st.cs_next_var st en` suffices_by simp[return_owned_def] >>
  `MLOAD <> ALLOCA` by simp[] >>
  metis_tac[cj 1 return_owned_mutual, pairTheory.SND]
QED

Theorem return_fragment_ids:
  cs_extends st en /\ return_id_trace st en ==>
  (MEM aid (MAP (\i. i.inst_id) (frag_code st en)) <=>
   st.cs_next_id <= aid /\ aid < en.cs_next_id)
Proof
  simp_tac bool_ss [cs_extends_def, return_id_trace_def, return_code_trace_def] >>
  strip_tac >> Cases_on `new = []`
  >- (gvs[frag_code_def, emitted_blocks_def, emitted_insts_def,
          IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
      qpat_x_assum `_ = GENLIST _ _` (fn th => rewrite_tac[th]) >>
      simp[MEM_GENLIST] >> intLib.COOPER_TAC) >>
  gvs[frag_code_def, emitted_blocks_def, TAKE_LENGTH_APPEND, NULL_EQ,
      MAP_APPEND, FLAT_APPEND, REVERSE_APPEND, IS_PREFIX_APPEND] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  gvs[DROP_LENGTH_APPEND] >>
  qpat_x_assum `_ = GENLIST _ _` (mp_tac o Q.AP_TERM `MEM aid`) >>
  simp[MAP_FLAT, MAP_REVERSE, MEM_APPEND, MEM_FLAT, MEM_MAP, MEM_REVERSE,
       MEM_GENLIST] >>
  strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
  intLib.COOPER_TAC
QED

Theorem return_fragment_host_member:
  fn_has_code st en func /\ MEM inst (frag_code st en) ==>
  MEM inst (fn_insts func)
Proof
  rw[frag_code_def, fn_has_code_def, emitted_insts_def,
     MEM_APPEND, MEM_FLAT, MEM_MAP]
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      gvs[IS_PREFIX_APPEND] >> metis_tac[MEM_DROP_IMP, MEM_APPEND])
  >- (`MEM (LAST (emitted_blocks st en)) (emitted_blocks st en)` by
        gvs[NULL_EQ, MEM_LAST_NOT_NIL] >>
      irule lookup_block_fn_insts >>
      first_x_assum drule >> disch_then (irule_at Any) >>
      metis_tac[MEM_DROP_IMP])
  >- (irule lookup_block_fn_insts >>
      `MEM bb' (emitted_blocks st en)` by metis_tac[MEM_FRONT_NOT_NIL, NULL_EQ] >>
      first_x_assum drule >> disch_then (irule_at Any) >> simp[])
  >> irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     gvs[IS_PREFIX_APPEND]
QED

Theorem return_decoder_scratch_owned:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st ==>
  !aid. aid IN abi_malformed_scratch_sites st en func ==>
  ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = aid /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr ce scopes q
Proof
  rpt strip_tac >>
  `cs_extends st en` by metis_tac[cs_extends_abi_decode] >>
  `return_id_trace st en` by
    metis_tac[cj 1 return_id_trace_decoder_mutual, pairTheory.SND] >>
  drule return_owned_fragment >> strip_tac >>
  gvs[abi_malformed_scratch_sites_def] >>
  `MEM inst.inst_id (MAP (\i. i.inst_id) (frag_code st en))` by
    metis_tac[return_fragment_ids] >>
  gvs[MEM_MAP] >>
  `MEM i (fn_insts func)` by metis_tac[return_fragment_host_member] >>
  `inst = i` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[EVERY_MEM, return_alloca_owned_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl_tac [`i`, `"%" ++ toString n`] >>
  simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]
QED
