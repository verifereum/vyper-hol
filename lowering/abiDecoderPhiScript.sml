(* Decoder emissions preserve PHI-free heads, relative to arbitrary old blocks. *)
Theory abiDecoderPhi
Ancestors
  abiEncoder abiDecoderContract compileEnv emitHelper context venomInst
  venomExecSemantics list rich_list

Theorem abi_decoder_phi_append:
  phi_prefix_length xs = 0 /\ phi_prefix_length ys = 0 ==>
  phi_prefix_length (xs ++ ys) = 0
Proof
  Cases_on `xs` >- simp[phi_prefix_length_def] >>
  rename1 `phi_prefix_length (inst::rest) = 0` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Definition abi_decoder_phi_safe_def:
  abi_decoder_phi_safe base st <=>
    (?new. st.cs_blocks = new ++ base /\
      EVERY (\bb. phi_prefix_length bb.bb_instructions = 0) new) /\
    phi_prefix_length st.cs_current_insts = 0
End

Definition abi_decoder_phi_def:
  abi_decoder_phi st st' <=>
    (!base. abi_decoder_phi_safe base st ==> abi_decoder_phi_safe base st') /\
    (st.cs_blocks = st'.cs_blocks \/ phi_prefix_length st'.cs_current_insts = 0)
End

Theorem abi_decoder_phi_safe_head:
  (!base. abi_decoder_phi_safe base st ==> abi_decoder_phi_safe base st') /\
  phi_prefix_length st.cs_current_insts = 0 ==>
  phi_prefix_length st'.cs_current_insts = 0
Proof
  strip_tac >>
  `abi_decoder_phi_safe st.cs_blocks st` by
    (simp[abi_decoder_phi_safe_def] >> qexists_tac `[]` >> simp[]) >>
  `abi_decoder_phi_safe st.cs_blocks st'` by metis_tac[] >>
  fs[abi_decoder_phi_safe_def]
QED

Theorem abi_decoder_phi_refl:
  abi_decoder_phi st st
Proof
  simp[abi_decoder_phi_def]
QED

Theorem abi_decoder_phi_trans:
  abi_decoder_phi st st1 /\ abi_decoder_phi st1 st2 ==> abi_decoder_phi st st2
Proof
  simp_tac bool_ss [abi_decoder_phi_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  metis_tac[abi_decoder_phi_safe_head]
QED

Theorem abi_decoder_phi_return:
  abi_decoder_phi st (SND (comp_return v st))
Proof
  simp[comp_return_def, abi_decoder_phi_refl]
QED

Theorem abi_decoder_phi_bind:
  (!st. abi_decoder_phi st (SND (f st))) /\
  (!v st. abi_decoder_phi st (SND (g v st))) ==>
  abi_decoder_phi st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule abi_decoder_phi_trans >> metis_tac[pairTheory.SND]
QED

Theorem abi_decoder_phi_ignore_bind:
  (!st. abi_decoder_phi st (SND (f st))) /\
  (!st. abi_decoder_phi st (SND (g st))) ==>
  abi_decoder_phi st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_decoder_phi_bind >> simp[]
QED

Theorem abi_decoder_phi_emit_op:
  opc <> PHI ==> abi_decoder_phi st (SND (emit_op opc ops st))
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, abi_decoder_phi_def, abi_decoder_phi_safe_def] >>
  irule abi_decoder_phi_append >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_phi_emit_void:
  opc <> PHI ==> abi_decoder_phi st (SND (emit_void opc ops st))
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, abi_decoder_phi_def, abi_decoder_phi_safe_def] >>
  irule abi_decoder_phi_append >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_phi_emit_inst:
  opc <> PHI ==> abi_decoder_phi st (SND (emit_inst opc ops outs st))
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, abi_decoder_phi_def, abi_decoder_phi_safe_def] >>
  irule abi_decoder_phi_append >> simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_phi_fresh_label:
  abi_decoder_phi st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, abi_decoder_phi_def, abi_decoder_phi_safe_def]
QED

Theorem abi_decoder_phi_new_block:
  abi_decoder_phi st (SND (new_block name st))
Proof
  rw[new_block_def, abi_decoder_phi_def, abi_decoder_phi_safe_def] >>
  simp[phi_prefix_length_def] >> rename1 `st.cs_blocks = created ++ old_blocks` >>
  qexists_tac `<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|> :: created` >>
  simp[]
QED

Theorem abi_decoder_phi_alloc_buffer:
  abi_decoder_phi st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >> irule abi_decoder_phi_bind >>
  simp[abi_decoder_phi_emit_op, abi_decoder_phi_return]
QED

val phi_simps = [abi_decoder_phi_emit_op, abi_decoder_phi_emit_void,
  abi_decoder_phi_emit_inst, abi_decoder_phi_return,
  abi_decoder_phi_fresh_label, abi_decoder_phi_new_block, abi_decoder_phi_alloc_buffer];
val phi_db = fn t => rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >>
  conj_tac >- simp (t::phi_simps) >> rpt strip_tac;
val phi_dib = fn t => ho_match_mp_tac abi_decoder_phi_ignore_bind >>
  conj_tac >- simp (t::phi_simps) >> rpt strip_tac;

Theorem abi_decoder_phi_clamp:
  !c v st. abi_decoder_phi st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
      compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
      abi_decoder_phi_return] >> rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (phi_db abi_decoder_phi_emit_op) >>
  simp[abi_decoder_phi_emit_void]
QED

Theorem abi_decoder_phi_static:
  opc <> PHI /\
  (!v st. abi_decoder_phi st (SND (clamp v st))) ==>
  !st. abi_decoder_phi st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  phi_db abi_decoder_phi_emit_op >> phi_dib abi_decoder_phi_refl >>
  simp[abi_decoder_phi_emit_void]
QED

Theorem abi_decoder_phi_getelemptr:
  opc <> PHI ==>
  !st. abi_decoder_phi st
    (SND (compile_getelemptr_abi src dyn off opc hi st))
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  phi_db abi_decoder_phi_emit_op >> Cases_on `dyn` >>
  simp[abi_decoder_phi_return] >>
  ntac 2 (phi_db abi_decoder_phi_emit_op) >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
      ntac 2 (phi_db abi_decoder_phi_emit_op) >>
      simp[abi_decoder_phi_emit_void]) >>
  simp[abi_decoder_phi_return]
QED

Theorem abi_decoder_phi_dyn_elem_ptr:
  opc <> PHI ==>
  !st. abi_decoder_phi st
    (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  ntac 2 (phi_db abi_decoder_phi_emit_op) >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
      ntac 2 (phi_db abi_decoder_phi_emit_op) >>
      phi_dib abi_decoder_phi_emit_void >>
      ntac 3 (phi_db abi_decoder_phi_emit_op) >>
      simp[abi_decoder_phi_emit_void]) >>
  simp[abi_decoder_phi_return]
QED

(* The source opcode cannot introduce a PHI instruction. *)
Theorem abi_decoder_phi_mutual:
  (!dst src opc hi info. opc <> PHI ==>
     !st. abi_decoder_phi st
       (SND (compile_abi_decode_to_buf dst src opc hi info st))) /\
  (!dst src opc hi elems ao vo. opc <> PHI ==>
     !st. abi_decoder_phi st
       (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st))) /\
  (!dst src opc hi ei asz msz ip cnt. opc <> PHI ==>
     !st. abi_decoder_phi st
       (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)))
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

Resume abi_decoder_phi_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule abi_decoder_phi_static >> simp[abi_decoder_phi_clamp]
QED
Resume abi_decoder_phi_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 (phi_db abi_decoder_phi_emit_op) >>
  phi_dib abi_decoder_phi_emit_void >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
      ntac 4 (phi_db abi_decoder_phi_emit_op) >>
      simp[abi_decoder_phi_emit_void]) >>
  rpt strip_tac >> Cases_on `opc` >> simp[abi_decoder_phi_emit_void]
QED
Resume abi_decoder_phi_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 (phi_db abi_decoder_phi_emit_op) >>
  phi_dib abi_decoder_phi_emit_void >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_phi_return] >>
      ntac 5 (phi_db abi_decoder_phi_emit_op) >>
      simp[abi_decoder_phi_emit_void]) >>
  rpt strip_tac >> phi_db abi_decoder_phi_emit_op >>
  phi_dib abi_decoder_phi_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 3 (phi_db abi_decoder_phi_emit_op) >>
      Cases_on `opc` >> simp[abi_decoder_phi_emit_void]) >>
  phi_db abi_decoder_phi_alloc_buffer >> phi_dib abi_decoder_phi_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume abi_decoder_phi_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  ntac 3 (phi_db abi_decoder_phi_emit_op) >> phi_dib abi_decoder_phi_emit_void >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume abi_decoder_phi_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[abi_decoder_phi_return]
QED
Resume abi_decoder_phi_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  phi_db abi_decoder_phi_getelemptr >> phi_db abi_decoder_phi_emit_op >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume abi_decoder_phi_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (phi_db abi_decoder_phi_fresh_label) >>
  phi_dib abi_decoder_phi_emit_inst >> phi_dib abi_decoder_phi_new_block >>
  ntac 4 (phi_db abi_decoder_phi_emit_op) >>
  phi_dib abi_decoder_phi_emit_inst >> phi_dib abi_decoder_phi_new_block >>
  ntac 4 (phi_db abi_decoder_phi_emit_op) >>
  ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_phi_dyn_elem_ptr, abi_decoder_phi_return]) >>
  rpt strip_tac >> ntac 3 (phi_db abi_decoder_phi_emit_op) >>
  ho_match_mp_tac abi_decoder_phi_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> phi_db abi_decoder_phi_emit_op >>
  phi_dib abi_decoder_phi_emit_void >> phi_dib abi_decoder_phi_emit_inst >>
  phi_dib abi_decoder_phi_new_block >> simp[abi_decoder_phi_return]
QED
Finalise abi_decoder_phi_mutual

Theorem abi_decoder_to_buf_phi:
  compile_abi_decode_to_buf dst src opc hi info st = ((),st') /\
  abi_decode_source_opcode opc /\ phi_prefix_length st.cs_current_insts = 0 ==>
  phi_prefix_length st'.cs_current_insts = 0 /\
  ?new. st'.cs_blocks = new ++ st.cs_blocks /\
    EVERY (\bb. phi_prefix_length bb.bb_instructions = 0) new
Proof
  strip_tac >> `opc <> PHI` by gvs[abi_decode_source_opcode_def] >>
  `abi_decoder_phi st st'` by metis_tac[cj 1 abi_decoder_phi_mutual, pairTheory.SND] >>
  `abi_decoder_phi_safe st.cs_blocks st` by
    (simp[abi_decoder_phi_safe_def] >> qexists_tac `[]` >> simp[]) >>
  `abi_decoder_phi_safe st.cs_blocks st'` by
    (qpat_x_assum `abi_decoder_phi _ _`
      (mp_tac o Q.SPEC `st.cs_blocks` o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_phi_def]) >>
     asm_simp_tac bool_ss []) >>
  fs[abi_decoder_phi_safe_def] >> metis_tac[]
QED

(* An entry block may contain old PHIs: only a newly reached exit needs a
   PHI-free head. Linear decoders keep using the already-entered block. *)
Theorem abi_decoder_to_buf_exit_phi:
  compile_abi_decode_to_buf dst src opc hi info st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st.cs_blocks = st'.cs_blocks \/ phi_prefix_length st'.cs_current_insts = 0
Proof
  strip_tac >> `opc <> PHI` by gvs[abi_decode_source_opcode_def] >>
  `abi_decoder_phi st st'` by metis_tac[cj 1 abi_decoder_phi_mutual, pairTheory.SND] >>
  fs[abi_decoder_phi_def]
QED
