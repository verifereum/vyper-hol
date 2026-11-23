Theory bodyFullAbiDecodeRecursiveConditional
Ancestors
  abiEncoder bodyFullAbiDecodeArrayLoopLength bodyFullAbiDecodeClampObserved
  bodyFullAbiDecodeWordCasesObserved bodyFullAbiDecodeFiniteCasesObserved
  bodyFullAbiDecodeMemberCasesObserved
Libs
  bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyFullAbiDecodeRuntimeLoopLengthObservedLib

(* Use the generated compiler clauses, including the entire array step. *)
val compiler_ind = abiEncoderTheory.compile_abi_decode_to_buf_ind;
fun specialize loop = ISPECL [guarded_plus_typed, bounded_complex_plus_typed, loop]
  compiler_ind;
val length_ind = specialize repaired_loop_length_plus_typed;
val (length_steps, length_mutual) = dest_imp (concl length_ind);
val array_clause = close_statement (List.nth (strip_conj length_steps, 2));
val public_mutual = snd (dest_imp (concl (specialize repaired_loop_plus_typed)));
val normalize = REDEPTH_CONV BETA_CONV THENC
  REWRITE_CONV [GSYM CONJ_ASSOC];

val unpack_observed = qx_choose_then `r` (qx_choose_then `G'`
  (qx_choose_then `tn'` (MAP_EVERY assume_tac o CONJUNCTS)));
val unpack_result = DISJ_CASES_THEN
  (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS));

Theorem abi_decode_joint_mutual_length_from_array[local]:
  ^array_clause ==> ^length_mutual
Proof
  disch_then (mk_asm "array") >>
  MATCH_MP_TAC length_ind >>
  rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- (asm "array" MATCH_ACCEPT_TAC)
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> BETA_TAC >> ACCEPT_TAC abi_decode_dyn_loop_length_observed_conditional
QED

Resume abi_decode_joint_mutual_length_from_array[word]:
  asm_x "array" kall_tac >>
  CONV_TAC normalize >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE abi_decode_word_case_observed_conditional) >>
  (impl_tac >-
    MATCH_ACCEPT_TAC abi_decode_clamp_joint_observed) >>
  disch_then (mp_tac o Q.SPECL
    [`dst`,`src_op`,`load_opc`,`base_op`,`hi_op`,`clamp_info`,`env`,`sf`,`ty`,
     `tv`,`live`,`protected`,`start`,`finish'`,`s`,`G`,`tn`,`d`] o
    CONV_RULE normalize) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then unpack_observed >>
  qexistsl [`r`, `G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(?t. r = OK t /\ _) \/ _` unpack_result
  >- (disj1_tac >> qexists `t` >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[])
  >> disj2_tac >> qexists `t` >> first_assum ACCEPT_TAC
QED

Resume abi_decode_joint_mutual_length_from_array[bytes]:
  CONV_TAC normalize >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  MATCH_MP_TAC (CONV_RULE normalize (Q.SPECL
    [`dst`,`src_op`,`load_opc`,`base_op`,`hi_op`,`max_len`,`env`,`sf`,`ty`,
     `tv`,`live`,`protected`,`start`,`finish'`,`s`,`G`,`tn`,`d`]
    abi_decode_bytes_case_observed_conditional)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_joint_mutual_length_from_array[complex]:
  asm_x "array" kall_tac >>
  CONV_TAC normalize >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "bounded") kall_tac) >>
  MATCH_MP_TAC (CONV_RULE normalize abi_decode_complex_observed_conditional) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "bounded" (mp_tac o Q.SPEC
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (elems:(abi_dec_info # num # num) list)`) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => MATCH_MP_TAC (SPEC_ALL th)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_joint_mutual_length_from_array[nil]:
  asm_x "array" kall_tac >>
  CONV_TAC normalize >> rpt gen_tac >>
  MATCH_MP_TAC (CONV_RULE normalize abi_decode_member_observed_conditional) >>
  disj1_tac >> REFL_TAC
QED

Resume abi_decode_joint_mutual_length_from_array[cons]:
  asm_x "array" kall_tac >>
  CONV_TAC normalize >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "head") (mk_asm "tail")) >>
  MATCH_MP_TAC (CONV_RULE normalize abi_decode_member_observed_conditional) >>
  disj2_tac >> qexistsl [`ei`, `abi_sz`, `mem_sz`, `rest`] >>
  conj_tac >- REFL_TAC >>
  conj_tac
  >- (asm "head" (qspec_then `dec_info_needs_offset ei` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then MATCH_ACCEPT_TAC) >>
  asm "tail" (qspec_then `dec_info_needs_offset ei` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then MATCH_ACCEPT_TAC
QED

Finalise abi_decode_joint_mutual_length_from_array[local]

Theorem abi_decode_joint_mutual_from_array_clause:
  ^array_clause ==> ^public_mutual
Proof
  disch_then (mp_tac o MATCH_MP abi_decode_joint_mutual_length_from_array) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "guarded")
    (CONJUNCTS_THEN2 (mk_asm "complex") (mk_asm "loop"))) >>
  conj_tac >- asm "guarded" ACCEPT_TAC >>
  conj_tac >- asm "complex" ACCEPT_TAC >>
  CONV_TAC normalize >> rpt gen_tac >>
  asm_x "loop" (fn th =>
    disch_then (unpack_observed o MATCH_MP (CONV_RULE normalize th))) >>
  qexistsl [`r`, `G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(?t. r = OK t /\ _) \/ _` unpack_result
  >- (disj1_tac >> qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >> disj2_tac >> qexists `t` >> first_assum ACCEPT_TAC
QED
