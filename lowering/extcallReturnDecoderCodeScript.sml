(* Opcode certificates use chronological code traces, independent of IDs. *)
Theory extcallReturnDecoderCode
Ancestors
  abiDecoderCode abiDecoderAppend abiDecoderVarSequence exprSimAbiGasBridge abiEncoder
  compileEnv exprLoweringProps fragExec emitHelper context venomInst list rich_list

Definition return_code_trace_def:
  return_code_trace st =
    FLAT (MAP (\bb. bb.bb_instructions) (REVERSE st.cs_blocks)) ++
    st.cs_current_insts
End

Definition return_code_def:
  return_code P st en <=>
    ?code. return_code_trace en = return_code_trace st ++ code /\ EVERY P code
End

Theorem return_code_refl:
  return_code P st st
Proof
  simp[return_code_def] >> qexists_tac `[]` >> simp[]
QED

Theorem return_code_trans:
  return_code P st mid /\ return_code P mid en ==> return_code P st en
Proof
  rw[return_code_def] >> qexists_tac `code ++ code'` >> simp[]
QED

Theorem return_code_return:
  return_code P st (SND (comp_return v st))
Proof
  simp[comp_return_def, return_code_refl]
QED

Theorem return_code_bind:
  (!st. return_code P st (SND (f st))) /\
  (!v st. return_code P st (SND (g v st))) ==>
  return_code P st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule return_code_trans >> metis_tac[pairTheory.SND]
QED

Theorem return_code_ignore_bind:
  (!st. return_code P st (SND (f st))) /\
  (!st. return_code P st (SND (g st))) ==>
  return_code P st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule return_code_bind >> simp[]
QED

Theorem return_code_emit_op:
  P (mk_inst st.cs_next_id opc ops ["%" ++ toString st.cs_next_var]) ==>
  return_code P st (SND (emit_op opc ops st))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, return_code_def, return_code_trace_def] >>
  strip_tac >> qexists_tac `[mk_inst st.cs_next_id opc ops ["%" ++ toString st.cs_next_var]]` >> simp[]
QED

Theorem return_code_emit_void:
  P (mk_inst st.cs_next_id opc ops []) ==>
  return_code P st (SND (emit_void opc ops st))
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, return_code_def, return_code_trace_def] >>
  strip_tac >> qexists_tac `[mk_inst st.cs_next_id opc ops []]` >> simp[]
QED

Theorem return_code_emit_inst:
  P (mk_inst st.cs_next_id opc ops outs) ==>
  return_code P st (SND (emit_inst opc ops outs st))
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, return_code_def, return_code_trace_def] >>
  strip_tac >> qexists_tac `[mk_inst st.cs_next_id opc ops outs]` >> simp[]
QED

Theorem return_code_fresh_label:
  return_code P st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, return_code_def, return_code_trace_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem return_code_new_block:
  return_code P st (SND (new_block name st))
Proof
  simp[new_block_def, return_code_def, return_code_trace_def] >>
  qexists_tac `[]` >> simp[MAP_APPEND, FLAT_APPEND]
QED

Overload return_decoder_code =
  ``return_code (\i. abi_decoder_reentry_opcode i.inst_opcode)``

Theorem return_code_alloc_buffer:
  return_decoder_code st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >> irule return_code_bind >>
  simp[return_code_emit_op, return_code_return,
    abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem return_decoder_opcodes[local]:
  abi_decoder_reentry_opcode ADD /\ abi_decoder_reentry_opcode MUL /\
  abi_decoder_reentry_opcode AND /\ abi_decoder_reentry_opcode NOT /\
  abi_decoder_reentry_opcode EQ /\ abi_decoder_reentry_opcode LT /\
  abi_decoder_reentry_opcode GT /\ abi_decoder_reentry_opcode ISZERO /\
  abi_decoder_reentry_opcode SHL /\ abi_decoder_reentry_opcode SHR /\
  abi_decoder_reentry_opcode SIGNEXTEND /\ abi_decoder_reentry_opcode MLOAD /\
  abi_decoder_reentry_opcode MSTORE /\ abi_decoder_reentry_opcode MCOPY /\
  abi_decoder_reentry_opcode CALLDATACOPY /\ abi_decoder_reentry_opcode DLOADBYTES /\
  abi_decoder_reentry_opcode ASSERT /\ abi_decoder_reentry_opcode ALLOCA /\
  abi_decoder_reentry_opcode JMP /\ abi_decoder_reentry_opcode JNZ
Proof
  simp[abi_decoder_reentry_opcode_def]
QED

val code_simps = [return_code_emit_op, return_code_emit_void,
  return_code_emit_inst, return_code_return, return_code_fresh_label,
  return_code_new_block, return_code_alloc_buffer,
  return_decoder_opcodes, mk_inst_def];
val code_db = fn t => rpt gen_tac >> ho_match_mp_tac return_code_bind >>
  conj_tac >- simp (t::code_simps) >> rpt strip_tac;
val code_dib = fn t => ho_match_mp_tac return_code_ignore_bind >>
  conj_tac >- simp (t::code_simps) >> rpt strip_tac;

Theorem return_decoder_code_addr:
  !st. return_decoder_code st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp code_simps
QED

Theorem return_decoder_code_range:
  !st. return_decoder_code st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (code_db return_code_emit_op) >> simp code_simps
QED

Theorem return_decoder_code_clamp:
  !c v st. return_decoder_code st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, return_code_return] >>
  rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (code_db return_code_emit_op) >> simp code_simps
QED

Theorem return_decoder_code_static:
  abi_decoder_reentry_opcode opc /\
  (!v st. return_decoder_code st (SND (clamp v st))) ==>
  !st. return_decoder_code st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >> gen_tac >>
  ho_match_mp_tac return_code_bind >> conj_tac
  >- (rpt gen_tac >> irule return_code_emit_op >> simp[mk_inst_def]) >>
  rpt strip_tac >> code_dib return_code_refl >> simp code_simps
QED

Theorem return_decoder_code_getelemptr:
  abi_decoder_reentry_opcode opc ==>
  !st. return_decoder_code st
    (SND (compile_getelemptr_abi src dyn off opc base_op hi st))
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  code_db return_code_emit_op >> Cases_on `dyn` >> simp[return_code_return] >>
  code_db return_decoder_code_addr >> ntac 2 (code_db return_code_emit_op) >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_code_return] >>
      ntac 2 (code_db return_code_emit_op) >> simp code_simps) >>
  simp[return_code_return]
QED

Theorem return_decoder_code_dyn_elem_ptr:
  abi_decoder_reentry_opcode opc ==>
  !st. return_decoder_code st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  code_db return_decoder_code_addr >> ntac 2 (code_db return_code_emit_op) >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_code_return] >>
      ntac 2 (code_db return_code_emit_op) >> code_dib return_code_emit_void >>
      code_db return_code_emit_op >> simp[return_decoder_code_range]) >>
  simp[return_code_return]
QED

Theorem return_decoder_code_mutual:
  (!dst src opc base_op hi info. abi_decoder_reentry_opcode opc ==>
     !st. return_decoder_code st
       (SND (compile_abi_decode_to_buf dst src opc base_op hi info st))) /\
  (!dst src opc base_op hi elems ao vo. abi_decoder_reentry_opcode opc ==>
     !st. return_decoder_code st
       (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st))) /\
  (!dst src opc base_op hi ei asz msz ip cnt. abi_decoder_reentry_opcode opc ==>
     !st. return_decoder_code st
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

Resume return_decoder_code_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  code_db return_decoder_code_addr >>
  irule return_decoder_code_static >> simp[return_decoder_code_clamp]
QED
Resume return_decoder_code_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_code_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_code_return] >>
      code_db return_code_emit_op >> code_dib return_decoder_code_range >>
      simp[return_code_return]) >>
  rpt strip_tac >> code_db return_decoder_code_addr >>
  ntac 3 (code_db return_code_emit_op) >> code_dib return_code_emit_void >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_code_return] >>
      code_db return_code_emit_op >> simp[return_decoder_code_range]) >>
  rpt strip_tac >> IF_CASES_TAC
  >- (Cases_on `opc` >> simp code_simps) >>
  ntac 4 (code_db return_code_emit_op) >> code_dib return_code_emit_void >>
  code_db return_code_emit_op >> simp code_simps
QED
Resume return_decoder_code_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_code_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_code_return] >>
      code_db return_code_emit_op >> code_dib return_decoder_code_range >>
      simp[return_code_return]) >>
  rpt strip_tac >> code_db return_decoder_code_addr >>
  ntac 3 (code_db return_code_emit_op) >> code_dib return_code_emit_void >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_code_return] >>
      ntac 2 (code_db return_code_emit_op) >> simp[return_decoder_code_range]) >>
  rpt strip_tac >> code_db return_code_emit_op >> code_dib return_code_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (code_db return_code_emit_op) >> code_db return_decoder_code_addr >>
      code_db return_code_emit_op >> Cases_on `opc` >> simp code_simps) >>
  code_db return_code_alloc_buffer >> code_dib return_code_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume return_decoder_code_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  code_db return_code_emit_op >> code_dib return_decoder_code_range >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume return_decoder_code_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[return_code_return]
QED
Resume return_decoder_code_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  code_db return_decoder_code_getelemptr >> code_db return_code_emit_op >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume return_decoder_code_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (code_db return_code_fresh_label) >>
  code_dib return_code_emit_inst >> code_dib return_code_new_block >>
  code_db return_code_emit_op >> code_db return_decoder_code_addr >>
  ntac 3 (code_db return_code_emit_op) >>
  code_dib return_code_emit_inst >> code_dib return_code_new_block >>
  ntac 4 (code_db return_code_emit_op) >>
  ho_match_mp_tac return_code_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_decoder_code_dyn_elem_ptr, return_code_return]) >>
  rpt strip_tac >> ntac 3 (code_db return_code_emit_op) >>
  ho_match_mp_tac return_code_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> code_db return_code_emit_op >>
  code_dib return_code_emit_void >> code_dib return_code_emit_inst >>
  code_dib return_code_new_block >> simp[return_code_return]
QED
Finalise return_decoder_code_mutual

Theorem return_code_frag:
  cs_extends st en /\ return_code P st en ==> EVERY P (frag_code st en)
Proof
  simp_tac bool_ss [cs_extends_def, return_code_def, return_code_trace_def] >>
  strip_tac >>
  Cases_on `new = []`
  >- (gvs[frag_code_def, emitted_blocks_def, emitted_insts_def,
          IS_PREFIX_APPEND, DROP_LENGTH_APPEND]) >>
  gvs[frag_code_def, emitted_blocks_def, TAKE_LENGTH_APPEND, NULL_EQ,
      MAP_APPEND, FLAT_APPEND, REVERSE_APPEND, IS_PREFIX_APPEND] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  gvs[DROP_LENGTH_APPEND, EVERY_REVERSE, EVERY_FLAT, EVERY_MAP]
QED

Theorem return_decoder_frag_code:
  compile_abi_decode_to_buf dst src MLOAD base_op hi info st = ((),en) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code st en)
Proof
  strip_tac >> irule return_code_frag >>
  metis_tac[cj 1 return_decoder_code_mutual, return_decoder_opcodes,
    cs_extends_abi_decode, pairTheory.SND]
QED
