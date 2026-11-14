Theory bodyFullBuiltinECArithSourceMatch
Ancestors
  exprSimECArith bodyPtrPrecompileBuiltinsArithmeticValue
  valueEncodingProofs venomCallOracleDefs

Theorem ec_arith_staged_source_match:
  (bt = ECAdd \/ bt = ECMul) /\
  addr = (if bt = ECAdd then 6w else 7w) /\
  an = (if bt = ECAdd then 128w else 96w) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (if bt = ECAdd then ArrayTV (BaseTV (UintT 256)) (Fixed 2)
                  else BaseTV (UintT 256)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t /\
  expr_val_rel cx (if bt = ECAdd then ArrayT (BaseT (UintT 256)) (Fixed 2)
                   else BaseT (UintT 256)) v2 y t /\
  eval_operand x t = SOME p /\ eval_operand y t = SOME q /\
  mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n p) t.vs_memory /\
  mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n p+32) t.vs_memory /\
  (if bt = ECAdd then
     mem_word_at (w2n wi+64) u.vs_memory = mem_word_at (w2n q) t.vs_memory /\
     mem_word_at (w2n wi+96) u.vs_memory = mem_word_at (w2n q+32) t.vs_memory
   else mem_word_at (w2n wi+64) u.vs_memory = q) ==>
  ?r.
    (if bt = ECAdd then evaluate_ecadd [v1;v2] else evaluate_ecmul [v1;v2]) =
      (case r of NONE => INR (RuntimeError
         (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))
       | SOME xy => INL (mk_ec_result xy)) /\
    precompile_result (venom_call_request u addr 0w wi an T).cr_target
      (venom_call_request u addr 0w wi an T).cr_data =
      SOME (OPTION_MAP (\(rx,ry).
        word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T) r) /\
    (!ann tys es res es'. ec_source_tail cx ann bt tys [v1;v2] es = (res,es') ==>
       !g. ec_source_tail cx ann bt tys [v1;v2] (es with gas_obs := g) =
         (res,es' with gas_obs := g))
Proof
  strip_tac >>
  Cases_on `bt = ECAdd` >> gvs[]
  >- (qpat_assum `value_has_type _ v1`
        (mp_then Any mp_tac bodyPtrPrecompileBuiltinsArithmeticSourceTheory.ecadd_memory_semantics) >>
      disch_then (qspec_then `v2` mp_tac) >>
      disch_then (qspecl_then [`t`,`y`,`x`,`cx`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `option_CASE r` >>
      qexists `r` >> simp[] >>
      reverse conj_tac
      >- (rpt strip_tac >> irule ec_source_tail_gas_obs >> simp[]) >>
      simp[venom_call_request_def, venomStateTheory.read_memory_def,
        GSYM valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2w_n2w,
        fcpLib.INDEX_CONV ``dimindex(:160)``] >>
      simp[wordsTheory.dimword_def] >>
      rewrite_tac[SRULE [] (Q.SPECL [`w2n wi`,`64`,`64`] mem_bytes_at_split_padded),
        SRULE [] (Q.SPECL [`w2n wi`,`32`,`32`] mem_bytes_at_split_padded),
        SRULE [] (Q.SPECL [`w2n wi+64`,`32`,`32`] mem_bytes_at_split_padded)] >>
      simp[mem_bytes_at_word, arithmeticTheory.ADD_ASSOC,
        bodyPtrPrecompileBuiltinsArithmeticValueTheory.ec_precompile_words] >>
      Cases_on `r` >- simp[] >>
      rename1 `SOME xy` >> PairCases_on `xy` >>
      `xy0 < 2 ** 256 /\ xy1 < 2 ** 256` by
        (fs[markerTheory.Abbrev_def] >>
         qpat_assum `SOME _ = ecadd _ _`
           (mp_then Any mp_tac bodyPtrPrecompileBuiltinsArithmeticValueTheory.ecadd_success_bounds o GSYM) >>
         simp[]) >>
      simp[exprSimPrecompilesTheory.padded_num_to_be_bytes_word32]) >>
  qpat_assum `value_has_type _ v1`
    (mp_then Any mp_tac bodyPtrPrecompileBuiltinsArithmeticSourceTheory.ecmul_memory_semantics) >>
  disch_then (qspec_then `v2` mp_tac) >>
  disch_then (qspecl_then [`t`,`y`,`x`,`cx`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `option_CASE r` >>
  qexists `r` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule ec_source_tail_gas_obs >> simp[]) >>
  simp[venom_call_request_def, venomStateTheory.read_memory_def,
    GSYM valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2w_n2w,
    fcpLib.INDEX_CONV ``dimindex(:160)``, wordsTheory.dimword_def] >>
  rewrite_tac[SRULE [] (Q.SPECL [`w2n wi`,`64`,`32`] mem_bytes_at_split_padded),
    SRULE [] (Q.SPECL [`w2n wi`,`32`,`32`] mem_bytes_at_split_padded)] >>
  simp[mem_bytes_at_word, arithmeticTheory.ADD_ASSOC,
    bodyPtrPrecompileBuiltinsArithmeticValueTheory.ec_precompile_words] >>
  Cases_on `r` >- simp[] >>
  rename1 `SOME xy` >> PairCases_on `xy` >>
  `xy0 < 2 ** 256 /\ xy1 < 2 ** 256` by
    (fs[markerTheory.Abbrev_def] >>
     qpat_assum `SOME _ = ecmul _ _`
       (mp_then Any mp_tac bodyPtrPrecompileBuiltinsArithmeticValueTheory.ecmul_success_bounds o GSYM) >>
     simp[]) >>
  simp[exprSimPrecompilesTheory.padded_num_to_be_bytes_word32]
QED
