(* Fresh block-switch histories, independent of arbitrary initial labels. *)
Theory extcallReturnLabelSyntax
Ancestors
  extcallReturnSyntax emitHelperProps abiDecoderAppend abiEncoder fragExec
  compileEnv emitHelper context venomInst list rich_list arithmetic

Definition return_label_history_def:
  return_label_history st =
    MAP (\bb. bb.bb_label) (REVERSE st.cs_blocks) ++ [st.cs_current_bb]
End

Definition return_labels_between_def:
  return_labels_between lo hi ls <=>
    EVERY (\l. ?suffix k. l = fresh_label_output suffix k /\ lo <= k /\ k < hi) ls
End

Definition return_label_trace_def:
  return_label_trace st en <=>
    st.cs_next_label <= en.cs_next_label /\
    ?ls. return_label_history en = return_label_history st ++ ls /\
         ALL_DISTINCT ls /\
         return_labels_between st.cs_next_label en.cs_next_label ls
End

Theorem return_labels_between_append:
  return_labels_between lo hi (xs ++ ys) <=>
  return_labels_between lo hi xs /\ return_labels_between lo hi ys
Proof
  simp[return_labels_between_def]
QED

Theorem return_labels_between_widen:
  return_labels_between a b xs /\ lo <= a /\ b <= hi ==>
  return_labels_between lo hi xs
Proof
  rw[return_labels_between_def, EVERY_MEM] >> first_x_assum drule >>
  rpt strip_tac >> qexistsl_tac [`suffix`,`k`] >> simp[]
QED

Theorem return_labels_between_apart:
  return_labels_between a b xs /\ return_labels_between b c ys ==>
  !l. MEM l xs ==> ~MEM l ys
Proof
  simp[return_labels_between_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[] >> drule fresh_label_output_inj >> strip_tac >> gvs[]
QED

Theorem return_label_trace_refl:
  return_label_trace st st
Proof
  simp[return_label_trace_def, return_labels_between_def]
QED

Theorem return_label_trace_trans:
  return_label_trace st mid /\ return_label_trace mid en ==>
  return_label_trace st en
Proof
  rw[return_label_trace_def] >> qexists_tac `ls ++ ls'` >>
  simp[] >> conj_tac
  >- (simp[ALL_DISTINCT_APPEND] >>
      metis_tac[return_labels_between_apart]) >>
  simp[return_labels_between_append] >> conj_tac >>
  irule return_labels_between_widen >> metis_tac[LESS_EQ_REFL]
QED

Theorem return_label_trace_same:
  st.cs_blocks = en.cs_blocks /\ st.cs_current_bb = en.cs_current_bb /\
  st.cs_next_label <= en.cs_next_label ==>
  return_label_trace st en
Proof
  rw[return_label_trace_def] >> qexists_tac `[]` >>
  simp[return_label_history_def, return_labels_between_def]
QED

Theorem return_label_trace_return:
  return_label_trace st (SND (comp_return v st))
Proof
  simp[comp_return_def, return_label_trace_refl]
QED

Theorem return_label_trace_bind:
  (!st. return_label_trace st (SND (f st))) /\
  (!v st. return_label_trace st (SND (g v st))) ==>
  return_label_trace st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule return_label_trace_trans >> metis_tac[pairTheory.SND]
QED

Theorem return_label_trace_ignore_bind:
  (!st. return_label_trace st (SND (f st))) /\
  (!st. return_label_trace st (SND (g st))) ==>
  return_label_trace st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_label_trace_bind >> simp[]
QED

Theorem return_label_trace_emit_op:
  return_label_trace st (SND (emit_op opc ops st))
Proof
  irule return_label_trace_same >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def]
QED

Theorem return_label_trace_emit_void:
  return_label_trace st (SND (emit_void opc ops st))
Proof
  irule return_label_trace_same >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def]
QED

Theorem return_label_trace_emit_inst:
  return_label_trace st (SND (emit_inst opc ops outs st))
Proof
  irule return_label_trace_same >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def]
QED

Theorem return_label_trace_fresh_label:
  return_label_trace st (SND (fresh_label name st))
Proof
  irule return_label_trace_same >> simp[fresh_label_def]
QED

Theorem return_label_trace_alloc_buffer:
  return_label_trace st (SND (compile_alloc_buffer sz st))
Proof
  rewrite_tac[compile_alloc_buffer_def] >> irule return_label_trace_bind >>
  simp[return_label_trace_emit_op, return_label_trace_return]
QED

val label_simps = [return_label_trace_emit_op, return_label_trace_emit_void,
  return_label_trace_emit_inst, return_label_trace_return,
  return_label_trace_fresh_label, return_label_trace_alloc_buffer];
val label_db = fn t => rpt gen_tac >> ho_match_mp_tac return_label_trace_bind >>
  conj_tac >- simp (t::label_simps) >> rpt strip_tac;
val label_dib = fn t => ho_match_mp_tac return_label_trace_ignore_bind >>
  conj_tac >- simp (t::label_simps) >> rpt strip_tac;

Theorem return_label_trace_addr:
  !st. return_label_trace st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp label_simps
QED

Theorem return_label_trace_range:
  !st. return_label_trace st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (label_db return_label_trace_emit_op) >> simp label_simps
QED

Theorem return_label_trace_clamp:
  !c v st. return_label_trace st (SND (compile_abi_clamp_basetype v c st))
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, return_label_trace_return] >>
  rpt gen_tac >>
  TRY (IF_CASES_TAC >> simp_tac pure_ss [LET_THM]) >>
  ntac 2 (label_db return_label_trace_emit_op) >> simp label_simps
QED

Theorem return_label_trace_static:
  (!v st. return_label_trace st (SND (clamp v st))) ==>
  !st. return_label_trace st (SND (compile_abi_decode_static src dst opc clamp st))
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >> gen_tac >>
  label_db return_label_trace_emit_op >> label_dib return_label_trace_refl >>
  simp label_simps
QED

Theorem return_label_trace_getelemptr:
  !st. return_label_trace st
    (SND (compile_getelemptr_abi src dyn off opc base_op hi st))
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  label_db return_label_trace_emit_op >> Cases_on `dyn` >>
  simp[return_label_trace_return] >>
  label_db return_label_trace_addr >> ntac 2 (label_db return_label_trace_emit_op) >>
  ho_match_mp_tac return_label_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_label_trace_return] >>
      ntac 2 (label_db return_label_trace_emit_op) >> simp label_simps) >>
  simp[return_label_trace_return]
QED

Theorem return_label_trace_dyn_elem_ptr:
  !st. return_label_trace st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  label_db return_label_trace_addr >> ntac 2 (label_db return_label_trace_emit_op) >>
  ho_match_mp_tac return_label_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_label_trace_return] >>
      ntac 2 (label_db return_label_trace_emit_op) >> label_dib return_label_trace_emit_void >>
      label_db return_label_trace_emit_op >> simp[return_label_trace_range]) >>
  simp[return_label_trace_return]
QED

Theorem return_label_trace_reserved:
  pre.cs_next_label = st.cs_next_label + 3 /\
  return_label_history pre = return_label_history st ++
    [fresh_label_output "dec_dyn_hdr" st.cs_next_label;
     fresh_label_output "dec_dyn_body" (st.cs_next_label + 1)] /\
  return_label_trace pre post /\
  en.cs_next_label = post.cs_next_label /\
  return_label_history en = return_label_history post ++
    [fresh_label_output "dec_dyn_exit" (st.cs_next_label + 2)] ==>
  return_label_trace st en
Proof
  rw[return_label_trace_def] >>
  qexists_tac `[fresh_label_output "dec_dyn_hdr" st.cs_next_label;
    fresh_label_output "dec_dyn_body" (st.cs_next_label + 1)] ++ ls ++
    [fresh_label_output "dec_dyn_exit" (st.cs_next_label + 2)]` >>
  simp[] >> conj_tac
  >- (gvs[return_labels_between_def, EVERY_MEM, ALL_DISTINCT_APPEND] >>
      rpt conj_tac >> rpt strip_tac >>
      imp_res_tac fresh_label_output_inj >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule fresh_label_output_inj >> simp[]) >>
  simp[return_labels_between_def, EVERY_APPEND] >>
  conj_tac
  >- (qexistsl_tac [`"dec_dyn_hdr"`,`st.cs_next_label`] >> simp[]) >>
  conj_tac
  >- (qexistsl_tac [`"dec_dyn_body"`,`st.cs_next_label + 1`] >> simp[]) >>
  conj_tac
  >- (gvs[return_labels_between_def, EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [`suffix`,`k`] >> simp[]) >>
  qexistsl_tac [`"dec_dyn_exit"`,`st.cs_next_label + 2`] >> simp[]
QED

Definition return_label_quiet_def:
  return_label_quiet st en <=>
    return_label_history en = return_label_history st /\
    en.cs_next_label = st.cs_next_label
End

Theorem return_label_quiet_bind:
  (!st. return_label_quiet st (SND (f st))) /\
  (!v st. return_label_quiet st (SND (g v st))) ==>
  return_label_quiet st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >>
  gvs[return_label_quiet_def] >> metis_tac[pairTheory.SND]
QED

Theorem return_label_quiet_ignore_bind:
  (!st. return_label_quiet st (SND (f st))) /\
  (!st. return_label_quiet st (SND (g st))) ==>
  return_label_quiet st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_label_quiet_bind >> simp[]
QED

Theorem return_label_quiet_primitives:
  return_label_quiet st (SND (emit_op opc ops st)) /\
  return_label_quiet st (SND (emit_void opc ops st)) /\
  return_label_quiet st (SND (emit_inst opc ops outs st)) /\
  return_label_quiet st (SND (comp_return v st))
Proof
  simp[return_label_quiet_def, return_label_history_def,
    emit_op_def, emit_void_def, emit_inst_def, comp_return_def,
    comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def]
QED

val quiet_simps = [return_label_quiet_primitives];
val quiet_db = fn t => rpt gen_tac >> ho_match_mp_tac return_label_quiet_bind >>
  conj_tac >- simp (t::quiet_simps) >> rpt strip_tac;
val quiet_dib = fn t => ho_match_mp_tac return_label_quiet_ignore_bind >>
  conj_tac >- simp (t::quiet_simps) >> rpt strip_tac;

Theorem return_label_quiet_addr:
  !st. return_label_quiet st (SND (compile_abi_dec_addr base_op pos st))
Proof
  gen_tac >> rewrite_tac[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp quiet_simps
QED

Theorem return_label_quiet_range:
  !st. return_label_quiet st (SND (compile_abi_decode_range_check src e hi st))
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (quiet_db return_label_quiet_primitives) >> simp quiet_simps
QED

Theorem return_label_quiet_dyn_elem_ptr:
  !st. return_label_quiet st
    (SND (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz st))
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  quiet_db return_label_quiet_addr >> ntac 2 (quiet_db return_label_quiet_primitives) >>
  ho_match_mp_tac return_label_quiet_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp quiet_simps >>
      ntac 2 (quiet_db return_label_quiet_primitives) >> quiet_dib return_label_quiet_primitives >>
      quiet_db return_label_quiet_primitives >> simp[return_label_quiet_range]) >>
  simp quiet_simps
QED

Theorem return_label_trace_loop_skeleton[local]:
  (!h b e st. return_label_quiet st (SND (p h b e st))) /\
  (!h b e v st. return_label_quiet st (SND (q h b e v st))) /\
  (!h b e v w st. return_label_trace st (SND (d h b e v w st))) /\
  (!h b e v w st. return_label_quiet st (SND (r h b e v w st))) ==>
  return_label_trace st (SND ((do
    h <- fresh_label "dec_dyn_hdr";
    b <- fresh_label "dec_dyn_body";
    e <- fresh_label "dec_dyn_exit";
    emit_inst JMP [Label h] [];
    new_block h;
    v <- p h b e;
    new_block b;
    w <- q h b e v;
    d h b e v w;
    r h b e v w;
    new_block e;
    comp_return ()
  od) st))
Proof
  strip_tac >>
  simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_label_def, emit_inst_def, fresh_id_def, emit_def, new_block_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[LET_THM]) >>
  qmatch_asmsub_abbrev_tac `p _ _ _ s1` >>
  qmatch_asmsub_abbrev_tac `q _ _ _ _ s3` >>
  rename1 `p _ _ _ _ = (v,s2)` >>
  rename1 `q _ _ _ _ _ = (w,s4)` >>
  rename1 `d _ _ _ _ _ _ = (_,s5)` >>
  rename1 `r _ _ _ _ _ _ = (_,s6)` >>
  `return_label_quiet s1 s2` by metis_tac[pairTheory.SND] >>
  `return_label_quiet s3 s4` by metis_tac[pairTheory.SND] >>
  `return_label_trace s4 s5` by metis_tac[pairTheory.SND] >>
  `return_label_quiet s5 s6` by metis_tac[pairTheory.SND] >>
  irule return_label_trace_reserved >>
  qexistsl_tac [`s5`,`s4`] >>
  gvs[return_label_quiet_def, return_label_history_def] >>
  simp[Abbr `s3`] >> simp[Abbr `s1`]
QED

(* Compiler-only stages: expose the three delayed block bindings without
   unfolding recursive decoding or the straight-line address checks. *)
Definition return_loop_header_def:
  return_loop_header opc base_op src ip exit bdy = do
    i <- emit_op MLOAD [ip];
    addr <- compile_abi_dec_addr base_op src;
    cnt <- emit_op opc [addr];
    cmp <- emit_op LT [i; cnt];
    done <- emit_op ISZERO [cmp];
    emit_inst JNZ [done; Label exit; Label bdy] []
  od
End

Definition return_loop_body_def:
  return_loop_body dst src opc base_op hi ei asz msz ip = do
    i <- emit_op MLOAD [ip];
    data <- emit_op ADD [src; Lit 32w];
    off <- emit_op MUL [i; Lit (n2w asz)];
    es <- emit_op ADD [data; off];
    actual <- (if dec_info_needs_offset ei then
      compile_abi_decode_dyn_elem_ptr opc base_op es data hi asz
      else comp_return es);
    dd <- emit_op ADD [dst; Lit 32w];
    doff <- emit_op MUL [i; Lit (n2w msz)];
    ed <- emit_op ADD [dd; doff];
    comp_return (i,actual,ed)
  od
End

Definition return_loop_tail_def:
  return_loop_tail ip hdr triple =
    (case triple of (i,actual,ed) => do
      ni <- emit_op ADD [i; Lit 1w];
      emit_void MSTORE [ip; ni];
      emit_inst JMP [Label hdr] []
    od)
End

Theorem return_loop_stages_quiet[local]:
  (!st. return_label_quiet st
    (SND (return_loop_header opc base_op src ip exit bdy st))) /\
  (!st. return_label_quiet st
    (SND (return_loop_body dst src opc base_op hi ei asz msz ip st))) /\
  (!triple st. return_label_quiet st
    (SND (return_loop_tail ip hdr triple st)))
Proof
  conj_tac
  >- (rewrite_tac[return_loop_header_def] >>
      quiet_db return_label_quiet_primitives >> quiet_db return_label_quiet_addr >>
      ntac 3 (quiet_db return_label_quiet_primitives) >> simp quiet_simps) >>
  conj_tac
  >- (rewrite_tac[return_loop_body_def] >>
      ntac 4 (quiet_db return_label_quiet_primitives) >>
      ho_match_mp_tac return_label_quiet_bind >> conj_tac
      >- (rpt gen_tac >> IF_CASES_TAC >>
          simp[return_label_quiet_dyn_elem_ptr, return_label_quiet_primitives]) >>
      rpt gen_tac >> ntac 3 (quiet_db return_label_quiet_primitives) >>
      simp quiet_simps) >>
  Cases >> Cases_on `r` >> simp_tac (srw_ss()) [return_loop_tail_def] >>
  quiet_db return_label_quiet_primitives >>
  quiet_dib return_label_quiet_primitives >> simp quiet_simps
QED

Theorem return_loop_stages_equation[local]:
  compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt =
  (do h <- fresh_label "dec_dyn_hdr";
      b <- fresh_label "dec_dyn_body";
      e <- fresh_label "dec_dyn_exit";
      emit_inst JMP [Label h] [];
      new_block h;
      v <- return_loop_header opc base_op src ip e b;
      new_block b;
      triple <- return_loop_body dst src opc base_op hi ei asz msz ip;
      (case triple of (i,actual,ed) =>
        compile_abi_decode_to_buf ed actual opc base_op hi ei);
      return_loop_tail ip h triple;
      new_block e;
      comp_return ()
   od)
Proof
  rewrite_tac[Once compile_abi_decode_to_buf_def, return_loop_header_def,
    return_loop_body_def, return_loop_tail_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, FUN_EQ_THM] >>
  gen_tac >> simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM])
QED

Theorem return_label_trace_loop:
  (!ed actual st. return_label_trace st
    (SND (compile_abi_decode_to_buf ed actual opc base_op hi ei st))) ==>
  !st. return_label_trace st
    (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st))
Proof
  strip_tac >> gen_tac >> rewrite_tac[return_loop_stages_equation] >>
  ho_match_mp_tac return_label_trace_loop_skeleton >>
  simp[return_loop_stages_quiet] >>
  rpt gen_tac >> PairCases_on `triple` >> simp[]
QED

Theorem return_label_trace_decoder_mutual:
  (!dst src opc base_op hi info st. return_label_trace st
       (SND (compile_abi_decode_to_buf dst src opc base_op hi info st))) /\
  (!dst src opc base_op hi elems ao vo st. return_label_trace st
       (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st))) /\
  (!dst src opc base_op hi ei asz msz ip cnt st. return_label_trace st
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

Resume return_label_trace_decoder_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  label_db return_label_trace_addr >>
  irule return_label_trace_static >> simp[return_label_trace_clamp]
QED
Resume return_label_trace_decoder_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_label_trace_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_label_trace_return] >>
      label_db return_label_trace_emit_op >> label_dib return_label_trace_range >>
      simp[return_label_trace_return]) >>
  rpt strip_tac >> label_db return_label_trace_addr >>
  ntac 3 (label_db return_label_trace_emit_op) >> label_dib return_label_trace_emit_void >>
  ho_match_mp_tac return_label_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_label_trace_return] >>
      label_db return_label_trace_emit_op >> simp[return_label_trace_range]) >>
  rpt strip_tac >> IF_CASES_TAC
  >- (Cases_on `opc` >> simp label_simps) >>
  ntac 4 (label_db return_label_trace_emit_op) >> label_dib return_label_trace_emit_void >>
  label_db return_label_trace_emit_op >> simp label_simps
QED
Resume return_label_trace_decoder_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  ho_match_mp_tac return_label_trace_bind >> conj_tac
  >- (rpt gen_tac >> IF_CASES_TAC >> simp[return_label_trace_return] >>
      label_db return_label_trace_emit_op >> label_dib return_label_trace_range >>
      simp[return_label_trace_return]) >>
  rpt strip_tac >> label_db return_label_trace_addr >>
  ntac 3 (label_db return_label_trace_emit_op) >> label_dib return_label_trace_emit_void >>
  ho_match_mp_tac return_label_trace_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[return_label_trace_return] >>
      ntac 2 (label_db return_label_trace_emit_op) >> simp[return_label_trace_range]) >>
  rpt strip_tac >> label_db return_label_trace_emit_op >> label_dib return_label_trace_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (label_db return_label_trace_emit_op) >> label_db return_label_trace_addr >>
      label_db return_label_trace_emit_op >> Cases_on `opc` >> simp label_simps) >>
  label_db return_label_trace_alloc_buffer >> label_dib return_label_trace_emit_void >>
  first_x_assum irule
QED
Resume return_label_trace_decoder_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[]) >>
  label_db return_label_trace_emit_op >> label_dib return_label_trace_range >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz,_) acc. abi_sz + acc) 0 elems` mp_tac) >>
  simp[]
QED
Resume return_label_trace_decoder_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[return_label_trace_return]
QED
Resume return_label_trace_decoder_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  label_db return_label_trace_getelemptr >> label_db return_label_trace_emit_op >>
  ho_match_mp_tac return_label_trace_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >> first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume return_label_trace_decoder_mutual[loop]:
  irule return_label_trace_loop >> rpt gen_tac >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED
Finalise return_label_trace_decoder_mutual

Theorem return_label_trace_endpoint:
  cs_extends st en /\ return_label_trace st en ==>
  ~MEM en.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st en)))
Proof
  simp_tac bool_ss [cs_extends_def, return_label_trace_def,
    return_label_history_def] >> strip_tac >>
  Cases_on `new = []`
  >- gvs[emitted_blocks_def] >>
  gvs[emitted_blocks_def, TAKE_LENGTH_APPEND] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[listTheory.APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  gvs[REVERSE_APPEND, MAP_APPEND] >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP, MEM_REVERSE]
QED

Theorem return_decoder_endpoint_label:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),en) ==>
  ~MEM en.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st en)))
Proof
  strip_tac >> irule return_label_trace_endpoint >>
  metis_tac[cj 1 return_label_trace_decoder_mutual,
    cs_extends_abi_decode, pairTheory.SND]
QED
