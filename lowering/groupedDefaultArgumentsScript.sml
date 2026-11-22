Theory groupedDefaultArguments
Ancestors
  groupedKeywordDecode calldataSourceSize abiDecoderCoherence compileVyper compileEnv vyperCalldata vyperABIEntries vyperTypeABI vyperMisc
  list rich_list arithmetic

Theorem calldata_decode_args_length:
  !tvs cd off vals.
    calldata_decode_args cd tvs off = SOME vals ==> LENGTH vals = LENGTH tvs
Proof
  Induct >- simp[calldata_decode_args_def] >>
  rpt gen_tac >> simp[Once calldata_decode_args_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem opt_mmap_take_some:
  !xs ys n. OPT_MMAP f xs = SOME ys ==>
    OPT_MMAP f (TAKE n xs) = SOME (TAKE n ys)
Proof
  Induct >- simp[OPT_MMAP_def] >>
  rpt gen_tac >> Cases_on `n` >>
  simp[OPT_MMAP_def, TAKE_def] >>
  Cases_on `f h` >> Cases_on `OPT_MMAP f xs` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem grouped_default_decode_split:
  LENGTH dflts <= LENGTH args /\
  MEM (prefix,k) (abi_entries args dflts) /\
  OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
  OPT_MMAP (evaluate_type tenv) (MAP SND prefix) = SOME provided /\
  calldata_decode_args cd provided 0 = SOME vals ==>
  provided = TAKE (LENGTH args - LENGTH dflts) tvs ++
             TAKE k (DROP (LENGTH args - LENGTH dflts) tvs) /\
  LENGTH vals = LENGTH args - LENGTH dflts + k /\
  calldata_decode_args cd (TAKE (LENGTH args - LENGTH dflts) tvs) 0 =
    SOME (TAKE (LENGTH args - LENGTH dflts) vals) /\
  calldata_decode_args cd (TAKE k (DROP (LENGTH args - LENGTH dflts) tvs))
    (SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH dflts) tvs))) =
    SOME (DROP (LENGTH args - LENGTH dflts) vals)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `MEM (prefix,k) (abi_entries args dflts)`
    (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
  qabbrev_tac `pos = LENGTH args - LENGTH dflts` >>
  `pos + k <= LENGTH args` by fs[Abbr `pos`] >>
  `LENGTH tvs = LENGTH args` by metis_tac[OPT_MMAP_LENGTH, LENGTH_MAP] >>
  `LENGTH provided = pos + k` by
    (drule_then assume_tac (Q.INST [`ys` |-> `provided`] (SPEC_ALL OPT_MMAP_LENGTH)) >>
     fs[LENGTH_TAKE]) >>
  `provided = TAKE (pos+k) tvs` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME tvs`
       (qspec_then `pos+k` mp_tac o MATCH_MP opt_mmap_take_some) >>
     qpat_assum `OPT_MMAP _ (MAP SND prefix) = SOME provided` mp_tac >>
     qpat_assum `prefix = TAKE _ _` (fn th => REWRITE_TAC [th]) >>
     simp[MAP_TAKE]) >>
  `LENGTH vals = pos+k` by metis_tac[calldata_decode_args_length] >>
  `provided = TAKE pos tvs ++ TAKE k (DROP pos tvs)` by simp[GSYM TAKE_SUM] >>
  `LENGTH (TAKE pos tvs) = pos` by (simp[LENGTH_TAKE] >> decide_tac) >>
  qpat_assum `provided = TAKE pos tvs ++ _` (SUBST_ALL_TAC) >>
  drule calldata_decode_args_split >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE]
QED

Theorem grouped_argument_abi_head_sizes:
  !args tvs.
    LIST_REL (\arg tv. abi_decoder_coherent ce env ce.ce_struct_fields (SND arg) tv)
      args tvs ==>
    MAP (\(_,ty). abi_embedded_static_size ce.ce_struct_fields ty) args =
    MAP tv_abi_size tvs
Proof
  Induct >- (Cases >> simp[]) >>
  gen_tac >> PairCases_on `h` >> Cases >> simp[] >>
  metis_tac[calldata_coherent_embedded_size]
QED

Theorem grouped_argument_min_calldata_size:
  LIST_REL (\arg tv. abi_decoder_coherent ce env ce.ce_struct_fields (SND arg) tv)
    args tvs ==>
  min_calldata_size ce (TAKE n args) 0 = 4 + SUM (MAP tv_abi_size (TAKE n tvs))
Proof
  disch_then (mp_tac o Q.SPEC `n:num` o MATCH_MP LIST_REL_TAKE) >>
  disch_then (assume_tac o MATCH_MP grouped_argument_abi_head_sizes) >>
  simp[min_calldata_size_def, TAKE_LENGTH_ID_rwt]
QED
