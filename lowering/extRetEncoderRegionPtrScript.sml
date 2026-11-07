(* Function-owned coverage of the encoder's fresh instruction interval. *)
Theory extRetEncoderRegionPtr
Ancestors
  fragExec abiEncoder compileEnv emitHelper context arithmetic abiEncoderWindowArray venomInst localPtrsProps

Definition encoder_region_def:
  encoder_region st en <=>
    cs_extends st en /\
    st.cs_next_id <= en.cs_next_id /\
    st.cs_next_var <= en.cs_next_var /\
    !fn id. fn_has_code st en fn /\
      st.cs_next_id <= id /\ id < en.cs_next_id ==>
      ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
        (i.inst_opcode = ALLOCA ==>
          i.inst_operands = [Lit 32w] /\
          ?k. st.cs_next_var <= k /\ k < en.cs_next_var /\
            i.inst_outputs = ["%" ++ toString k])
End

Theorem encoder_region_refl:
  encoder_region st st
Proof
  simp[encoder_region_def, cs_extends_refl]
QED

Theorem encoder_region_trans:
  encoder_region st mid /\ encoder_region mid en ==>
  encoder_region st en
Proof
  simp_tac std_ss [encoder_region_def] >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code st mid fn /\ fn_has_code mid en fn` by
    metis_tac[fn_has_code_split] >>
  Cases_on `id < mid.cs_next_id`
  >- (qpat_x_assum `!fn id. fn_has_code st mid fn /\ _ ==> _`
        drule_all >> strip_tac >> qexists `i` >> simp[] >>
      strip_tac >> first_x_assum drule >> strip_tac >>
      qexists `k` >> simp[] >> decide_tac) >>
  `mid.cs_next_id <= id` by decide_tac >>
  qpat_x_assum `!fn id. fn_has_code mid en fn /\ _ ==> _`
    drule_all >> strip_tac >> qexists `i` >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists `k` >> simp[] >> decide_tac
QED

Theorem encoder_region_return:
  encoder_region st (SND (comp_return v st))
Proof
  simp[comp_return_def, encoder_region_refl]
QED

Theorem encoder_region_bind:
  (!st. encoder_region st (SND (f st))) /\
  (!v st. encoder_region st (SND (g v st))) ==>
  encoder_region st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule encoder_region_trans >> metis_tac[pairTheory.SND]
QED

Theorem encoder_region_ignore_bind:
  (!st. encoder_region st (SND (f st))) /\
  (!st. encoder_region st (SND (g st))) ==>
  encoder_region st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule encoder_region_bind >> simp[]
QED

Theorem encoder_region_emit_op:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  encoder_region st (SND (emit_op opc ops st))
Proof
  disch_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, encoder_region_def] >>
  conj_tac >- simp[cs_extends_def] >>
  rpt gen_tac >> strip_tac >>
  `id = st.cs_next_id` by decide_tac >> gvs[] >>
  qexists `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >>
  conj_tac
  >- (irule window_array_code_member >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def] >> strip_tac >> qexists `st.cs_next_var` >> simp[]
QED

Theorem encoder_region_emit_inst:
  opc <> ALLOCA ==>
  encoder_region st (SND (emit_inst opc ops outs st))
Proof
  disch_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, encoder_region_def] >>
  conj_tac >- simp[cs_extends_def] >>
  rpt gen_tac >> strip_tac >>
  `id = st.cs_next_id` by decide_tac >> gvs[] >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  conj_tac
  >- (irule window_array_code_member >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def]
QED

Theorem encoder_region_emit_void:
  opc <> ALLOCA ==>
  encoder_region st (SND (emit_void opc ops st))
Proof
  disch_tac >>
  `emit_void opc ops = emit_inst opc ops []` by
    simp[emit_void_def, emit_inst_def] >>
  simp[encoder_region_emit_inst]
QED

Theorem encoder_region_fresh_label:
  encoder_region st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, encoder_region_def, cs_extends_def]
QED

Theorem encoder_region_new_block:
  encoder_region st (SND (new_block name st))
Proof
  simp[new_block_def, encoder_region_def] >>
  irule cs_extends_new_block >> qexists `name` >> simp[new_block_def]
QED

Theorem encoder_region_alloc_buffer:
  encoder_region st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >> irule encoder_region_bind >>
  simp[encoder_region_emit_op, encoder_region_return]
QED

val region_simps = [encoder_region_emit_op, encoder_region_emit_void,
  encoder_region_emit_inst, encoder_region_return,
  encoder_region_fresh_label, encoder_region_new_block,
  encoder_region_alloc_buffer];
val region_db = fn t => rpt gen_tac >> ho_match_mp_tac encoder_region_bind >>
  conj_tac >- simp (t::region_simps) >> rpt strip_tac;
val region_dib = fn t => ho_match_mp_tac encoder_region_ignore_bind >>
  conj_tac >- simp (t::region_simps) >> rpt strip_tac;

Theorem encoder_static_region:
  encoder_region st (SND (compile_abi_encode_static dst src st))
Proof
  rewrite_tac[compile_abi_encode_static_def] >>
  region_db encoder_region_emit_op >>
  region_dib encoder_region_emit_void >> simp[encoder_region_return]
QED

Theorem encoder_static_info_region:
  !ei dst src st.
    encoder_region st (SND (compile_abi_encode_static_info dst src ei st))
Proof
  Cases >> simp[compile_abi_encode_static_info_def,
    encoder_static_region, encoder_region_return] >> rpt gen_tac >>
  region_dib encoder_region_emit_void >> simp[encoder_region_return]
QED

Theorem encoder_static_loop_region:
  encoder_region st
    (SND (compile_abi_encode_dyn_static_loop dst src ei asz msz len st))
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  region_db encoder_region_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  region_dib encoder_region_emit_void >>
  ntac 3 (region_db encoder_region_fresh_label) >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  ntac 3 (region_db encoder_region_emit_op) >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  ntac 7 (region_db encoder_region_emit_op) >>
  region_dib encoder_static_info_region >>
  region_db encoder_region_emit_op >> region_dib encoder_region_emit_void >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  ntac 2 (region_db encoder_region_emit_op) >> simp[encoder_region_emit_op]
QED

Theorem encoder_region_mutual:
  (!dst cp ci dyn off dp st.
    encoder_region st (SND (compile_abi_encode_child dst cp ci dyn off dp st))) /\
  (!dst src ei st.
    encoder_region st (SND (compile_abi_encode_to_buf dst src ei st))) /\
  (!dst src elems so ho dp st.
    encoder_region st (SND (compile_abi_encode_complex_elems dst src elems so ho dp st))) /\
  (!dst src ei asz msz len st.
    encoder_region st (SND (compile_abi_encode_dyn_loop dst src ei asz msz len st)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume encoder_region_mutual[child]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  region_db encoder_region_emit_op >> IF_CASES_TAC >> fs[] >>
  ntac 2 (region_db encoder_region_emit_op) >>
  ho_match_mp_tac encoder_region_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule) >>
  rpt gen_tac >> region_dib encoder_region_emit_void >>
  region_db encoder_region_emit_op >>
  region_dib encoder_region_emit_void >> simp[encoder_region_return]
QED
Resume encoder_region_mutual[word]:
  rewrite_tac[Once compile_abi_encode_child_def] >> simp[encoder_static_region]
QED
Resume encoder_region_mutual[bytes]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  ntac 4 (region_db encoder_region_emit_op) >>
  region_dib encoder_region_emit_void >> region_db encoder_region_emit_op >>
  region_dib encoder_region_emit_void >>
  ntac 2 (region_db encoder_region_emit_op) >> simp[encoder_region_emit_op]
QED
Resume encoder_region_mutual[copy]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  region_dib encoder_region_emit_void >> simp[encoder_region_return]
QED
Resume encoder_region_mutual[array]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  region_db encoder_region_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  region_dib encoder_region_emit_void >> region_db encoder_region_emit_op >>
  region_dib encoder_region_emit_void >>
  ho_match_mp_tac encoder_region_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC
      >- simp[encoder_static_loop_region] >> gvs[] >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> ntac 2 (region_db encoder_region_emit_op) >>
  region_dib encoder_region_emit_void >> simp[encoder_region_emit_op]
QED
Resume encoder_region_mutual[empty]:
  rewrite_tac[Once compile_abi_encode_child_def] >> simp[encoder_region_return]
QED
Resume encoder_region_mutual[complex]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gnvs[]
  >- (region_db encoder_region_alloc_buffer >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >>
      region_dib encoder_region_emit_void >>
      ho_match_mp_tac encoder_region_ignore_bind >> conj_tac
      >- (rpt gen_tac >> first_x_assum irule) >> simp[encoder_region_emit_op]) >>
  rpt gen_tac >> ho_match_mp_tac encoder_region_ignore_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule) >> simp[encoder_region_return]
QED
Resume encoder_region_mutual[nil]:
  rewrite_tac[Once compile_abi_encode_child_def] >> simp[encoder_region_return]
QED
Resume encoder_region_mutual[cons]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  region_db encoder_region_emit_op >>
  ho_match_mp_tac encoder_region_ignore_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule) >> rpt gen_tac >> first_x_assum irule
QED
Resume encoder_region_mutual[loop]:
  rewrite_tac[Once compile_abi_encode_child_def] >>
  region_db encoder_region_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> region_dib encoder_region_emit_void >>
  region_db encoder_region_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  region_db encoder_region_emit_op >> region_dib encoder_region_emit_void >>
  ntac 3 (region_db encoder_region_fresh_label) >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  ntac 3 (region_db encoder_region_emit_op) >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  ntac 9 (region_db encoder_region_emit_op) >>
  ho_match_mp_tac encoder_region_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> region_dib encoder_region_emit_void >>
  region_db encoder_region_emit_op >> region_dib encoder_region_emit_void >>
  region_db encoder_region_emit_op >> region_dib encoder_region_emit_void >>
  region_dib encoder_region_emit_inst >> region_dib encoder_region_new_block >>
  region_dib encoder_region_emit_op >> region_db encoder_region_emit_op >>
  simp[encoder_region_emit_op]
QED
Finalise encoder_region_mutual

Theorem encoder_region_alloca_fresh:
  encoder_region st en /\ fn_has_code st en fn /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < en.cs_next_id /\
  inst.inst_opcode = ALLOCA ==>
  inst.inst_operands = [Lit 32w] /\
  ?out. inst.inst_outputs = [out] /\ ~not_fresh_at st out
Proof
  simp_tac std_ss [encoder_region_def] >> strip_tac >>
  qpat_x_assum `!fn id. _` drule_all >> strip_tac >>
  `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[] >>
  simp[not_fresh_at_def] >> metis_tac[]
QED
