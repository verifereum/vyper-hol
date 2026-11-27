Theory bodyAbiDecodeLoopBodyContentMods
Ancestors
  abiStaticAggregateProps exprSimProps robustCopyTransportPtr
  valueEncodingProps venomState arithmetic pred_set
Libs
  bodyFullAbiDecodeLoopObservedSyntaxLib

Theorem loop_content_slice[local]:
  !k i d msz m m'.
    i < k /\
    mem_bytes_at d (32+k*msz) m = mem_bytes_at d (32+k*msz) m' ==>
    mem_bytes_at (d+32+i*msz) msz m =
    mem_bytes_at (d+32+i*msz) msz m'
Proof
  rpt gen_tac >> strip_tac >>
  `i*msz+msz <= k*msz` by
    (qpat_assum `i < k` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[GSYM (CONJUNCT2 MULT), LE_MULT_RCANCEL] >> decide_tac) >>
  rewrite_tac[GSYM ADD_ASSOC] >> irule mem_bytes_at_translated_window >>
  qexists_tac `32+k*msz` >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Theorem loop_content_header[local]:
  mem_bytes_at d (32+n) m = mem_bytes_at d (32+n) m' ==>
  mem_word_at d m = mem_word_at d m'
Proof
  strip_tac >> rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  AP_TERM_TAC >>
  drule_then (qspecl_then [`0`,`32`] mp_tac) mem_bytes_at_translated_window >>
  simp[]
QED

Theorem loop_content_robust_transport[local]:
  !msz tv a b old tb told.
    msz = type_memory_size tv /\
    mem_bytes_at a msz (b:venom_state).vs_memory =
      mem_bytes_at a msz (old:venom_state).vs_memory /\
    (!h. h < msz /\ a+h IN tb.t_mem ==> a+h IN told.t_mem) /\
    (^robust_at_typed) tv a old told ==>
    (^robust_at_typed) tv a b tb
Proof
  BETA_TAC >> ntac 7 gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `val_in_memory tv v a old.vs_memory` by
    (irule val_in_memory_mem_agree >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`msz`,`b.vs_memory`] >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `val_footprint tv v <= msz` by simp[exprSimPropsTheory.val_footprint_le] >>
  `!m. mem_agree_outside told.t_mem old.vs_memory m ==> val_in_memory tv v a m` by
    (qpat_assum `!x. value_has_type tv x /\ _ ==> _` (qspec_then `v` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  irule robust_val_in_memory_decreasing_taint_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`old.vs_memory`,`b.vs_memory`,`msz`,`a`,`told.t_mem`,`tb.t_mem`] >>
  asm_rewrite_tac[]
QED

Theorem abi_decode_loop_body_content_transport:
  ^(close_statement ``msz = type_memory_size tv /\
    SUC k*msz <= n*msz /\ output_base <= d /\
    d+32+n*msz <= output_base+output_cap /\
    (^completed_robust_typed) j0 k s tn /\
    (^robust_at_typed) tv (d+32+k*msz) t tr /\
    mem_bytes_at d (32+k*msz) t.vs_memory = mem_bytes_at d (32+k*msz) s.vs_memory /\
    mem_bytes_at d (32+SUC k*msz) b.vs_memory = mem_bytes_at d (32+SUC k*msz) t.vs_memory /\
    tb.t_mem SUBSET tr.t_mem /\ (^taint_decreases) tn tb /\
    mem_word_at d s.vs_memory = (w:256 word) ==>
    (^completed_robust_typed) j0 (SUC k) b tb /\ mem_word_at d b.vs_memory = w``)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (CONV_TAC LIST_BETA_CONV >> qx_gen_tac `i` >> strip_tac >>
      `mem_bytes_at (d+32+i*msz) msz b.vs_memory =
       mem_bytes_at (d+32+i*msz) msz t.vs_memory` by
        (match_mp_tac loop_content_slice >> qexists_tac `SUC k` >> asm_rewrite_tac[]) >>
      match_mp_tac loop_content_robust_transport >> Cases_on `i = k`
      >- (qexistsl_tac [`msz`,`t`,`tr`] >> asm_rewrite_tac[] >>
          conj_tac >-
            (gen_tac >> strip_tac >>
             qpat_assum `tb.t_mem SUBSET tr.t_mem` (irule o REWRITE_RULE[SUBSET_DEF]) >>
             first_assum ACCEPT_TAC) >>
          qpat_assum `msz = type_memory_size tv`
            (fn th => PURE_REWRITE_TAC[GSYM th]) >>
          BETA_TAC >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
      `i < k` by decide_tac >>
      `mem_bytes_at (d+32+i*msz) msz t.vs_memory =
       mem_bytes_at (d+32+i*msz) msz s.vs_memory` by
        (match_mp_tac loop_content_slice >> qexists_tac `k` >> asm_rewrite_tac[]) >>
      `i*msz+msz <= SUC k*msz` by
        (qpat_assum `i < SUC k` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         rewrite_tac[GSYM (CONJUNCT2 MULT), LE_MULT_RCANCEL] >> decide_tac) >>
      qexistsl_tac [`msz`,`s`,`tn`] >> asm_rewrite_tac[] >>
      qpat_assum `msz = type_memory_size tv`
        (fn th => PURE_REWRITE_TAC[GSYM th]) >>
      conj_tac >-
        (qx_gen_tac `h` >> strip_tac >>
         qpat_assum `(^taint_decreases) tn tb` (irule o BETA_RULE) >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
      qpat_assum `(^completed_robust_typed) j0 k s tn`
        (qspec_then `i` mp_tac o CONV_RULE LIST_BETA_CONV) >>
      asm_rewrite_tac[])
  >- (`mem_word_at d b.vs_memory = mem_word_at d t.vs_memory` by
        (irule loop_content_header >> qexists_tac `SUC k*msz` >> first_assum ACCEPT_TAC) >>
      `mem_word_at d t.vs_memory = mem_word_at d s.vs_memory` by
        (irule loop_content_header >> qexists_tac `k*msz` >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[])
QED
