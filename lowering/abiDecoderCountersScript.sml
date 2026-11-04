(* SSA variable counters never decrease in any recursive decoder action. *)
Theory abiDecoderCounters
Ancestors
  abiEncoder compileEnv emitHelper context venomInst arithmetic pair

Definition abi_decoder_vars_mono_def:
  abi_decoder_vars_mono (action : 'a compiler) <=>
    !st. st.cs_next_var <= (SND (action st)).cs_next_var
End

Theorem abi_decoder_vars_mono_bind:
  abi_decoder_vars_mono action /\ (!v. abi_decoder_vars_mono (next v)) ==>
  abi_decoder_vars_mono (comp_bind action next)
Proof
  rw[abi_decoder_vars_mono_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[LESS_EQ_TRANS, SND]
QED

Theorem abi_decoder_vars_mono_ignore_bind:
  abi_decoder_vars_mono action /\ abi_decoder_vars_mono next ==>
  abi_decoder_vars_mono (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_decoder_vars_mono_bind >> simp[]
QED

Theorem abi_decoder_vars_mono_return:
  abi_decoder_vars_mono (comp_return v)
Proof
  simp[abi_decoder_vars_mono_def, comp_return_def]
QED

Theorem abi_decoder_vars_mono_prims:
  (!opc ops. abi_decoder_vars_mono (emit_op opc ops)) /\
  (!opc ops. abi_decoder_vars_mono (emit_void opc ops)) /\
  (!opc ops outs. abi_decoder_vars_mono (emit_inst opc ops outs)) /\
  (!prefix. abi_decoder_vars_mono (fresh_label prefix)) /\
  (!lbl. abi_decoder_vars_mono (new_block lbl))
Proof
  simp[abi_decoder_vars_mono_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM]
QED

val vars_simps = [abi_decoder_vars_mono_return, abi_decoder_vars_mono_prims];
val VARS_BIND_WITH = fn extra => ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp (extra @ vars_simps) >> rpt gen_tac;
val VARS_BIND = VARS_BIND_WITH [];
val VARS_IGNORE = ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- simp vars_simps;

Theorem abi_decoder_vars_mono_abi_clamp:
  !c v. abi_decoder_vars_mono (compile_abi_clamp_basetype v c)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, abi_decoder_vars_mono_return] >>
  rpt gen_tac >> TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 VARS_BIND >> simp vars_simps
QED

Theorem abi_decoder_vars_mono_abi_static:
  (!v. abi_decoder_vars_mono (clamp v)) ==>
  abi_decoder_vars_mono (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  VARS_BIND >> VARS_IGNORE >> simp vars_simps
QED

Theorem abi_decoder_vars_mono_abi_alloc_buffer:
  abi_decoder_vars_mono (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> VARS_BIND >> simp vars_simps
QED

Theorem abi_decoder_vars_mono_abi_member_pointer:
  abi_decoder_vars_mono (compile_getelemptr_abi src dyn off opc hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> VARS_BIND >> Cases_on `dyn` >>
  simp[abi_decoder_vars_mono_return] >> ntac 2 VARS_BIND >>
  ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_vars_mono_return] >>
      ntac 2 VARS_BIND >> simp vars_simps) >>
  simp[abi_decoder_vars_mono_return]
QED

Theorem abi_decoder_vars_mono_abi_array_pointer:
  abi_decoder_vars_mono (compile_abi_decode_dyn_elem_ptr opc src data hi sz)
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >> ntac 2 VARS_BIND >>
  ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_vars_mono_return] >>
      ntac 2 VARS_BIND >> VARS_IGNORE >>
      ntac 3 VARS_BIND >> simp vars_simps) >>
  simp[abi_decoder_vars_mono_return]
QED

Theorem abi_decoder_vars_mono_mutual:
  (!dst src opc hi info. abi_decoder_vars_mono (compile_abi_decode_to_buf dst src opc hi info)) /\
  (!dst src opc hi elems ao vo.
    abi_decoder_vars_mono (compile_abi_decode_complex_elems dst src opc hi elems ao vo)) /\
  (!dst src opc hi ei asz msz ip cnt.
    abi_decoder_vars_mono (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt))
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

Resume abi_decoder_vars_mono_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule abi_decoder_vars_mono_abi_static >> simp[abi_decoder_vars_mono_abi_clamp]
QED

Resume abi_decoder_vars_mono_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 VARS_BIND >> VARS_IGNORE >>
  ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_vars_mono_return] >>
      ntac 4 VARS_BIND >> simp vars_simps) >>
  Cases_on `opc` >> simp vars_simps
QED

Resume abi_decoder_vars_mono_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ntac 3 VARS_BIND >> VARS_IGNORE >>
  ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_vars_mono_return] >>
      ntac 5 VARS_BIND >> simp vars_simps) >>
  VARS_BIND >> VARS_IGNORE >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 3 VARS_BIND >> Cases_on `opc` >> simp vars_simps) >>
  VARS_BIND_WITH [abi_decoder_vars_mono_abi_alloc_buffer] >>
  VARS_IGNORE >> first_x_assum irule >> simp[]
QED

Resume abi_decoder_vars_mono_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
        mp_tac) >> simp[]) >>
  ntac 3 VARS_BIND >> VARS_IGNORE >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
    mp_tac) >> simp[]
QED

Resume abi_decoder_vars_mono_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[abi_decoder_vars_mono_return]
QED

Resume abi_decoder_vars_mono_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  VARS_BIND_WITH [abi_decoder_vars_mono_abi_member_pointer] >>
  VARS_BIND >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED

Resume abi_decoder_vars_mono_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> ntac 3 VARS_BIND >>
  VARS_IGNORE >> VARS_IGNORE >> ntac 4 VARS_BIND >>
  VARS_IGNORE >> VARS_IGNORE >> ntac 4 VARS_BIND >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decoder_vars_mono_abi_array_pointer, abi_decoder_vars_mono_return]) >>
  rpt gen_tac >> ntac 3 VARS_BIND >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  VARS_BIND >> VARS_IGNORE >> VARS_IGNORE >> VARS_IGNORE >>
  simp[abi_decoder_vars_mono_return]
QED

Finalise abi_decoder_vars_mono_mutual

Theorem abi_decoder_variable_counter:
  compile_abi_decode_to_buf dst src opc hi info st = ((),st') ==>
  st.cs_next_var <= st'.cs_next_var
Proof
  metis_tac[cj 1 abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, SND]
QED
