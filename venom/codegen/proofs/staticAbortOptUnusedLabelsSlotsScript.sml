Theory staticAbortOptUnusedLabelsSlots
Ancestors
  asmSplice asmIR asmSem list option finite_map pred_set words

Theorem unused_label_one_retained_slots:
  !p pre tail cc (V:(num#num)->bool) pc height need tag boolean.
  let d = LENGTH pre in
  let q = pre++tail in
  let r = splice_pc d 1 0 in
  let C = \s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w in
  let P = OPTION_MAP (\(n,j). (n,r j)) in
  let T = \x k. P (tag x k) in
  let K = {x | x IN V /\ pc x <> d} in
  let Slots = \s cc h need tg boolean.
    (need ==> cc.cc_static) /\
    (!k. boolean k ==> k < h /\ tg k=NONE) /\
    (!k n j. tg k=SOME(n,j) ==>
       k < h /\ j < LENGTH s /\
       (EL j s = AsmPushLabel n \/ EL j s = AsmPushOfst n 0) /\
       ?w. C s n w)
  in
  (!x. x IN V ==> Slots p cc (height x) (need x) (tag x) (boolean x)) /\
  (!x k n j. x IN V /\ tag x k = SOME(n,j) ==>
      j <> d /\ j < LENGTH p /\ r j < LENGTH q /\ EL (r j) q = EL j p /\
      T x k = SOME(n,r j) /\
      !w. C p n w ==> w <> d /\ INDEX_OF (AsmLabel n) p = SOME w /\
        INDEX_OF (AsmLabel n) q = SOME(r w) /\ C q n (r w)) ==>
  !x. x IN K ==> Slots q cc (height x) (need x) (T x) (boolean x)
Proof
  rpt gen_tac >>
  map_every (fn pat => qmatch_goalsub_abbrev_tac pat >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ d`, `LET _ q`, `LET _ r`, `LET _ C`] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  strip_tac >> qx_gen_tac `x` >>
  simp[GSPECIFICATION, Excl "OPTION_MAP_EQ_SOME"] >> strip_tac >>
  qpat_x_assum `!x. x IN V ==> _` (qspec_then `x` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  conj_tac >- gvs[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> rewrite_tac[OPTION_MAP_EQ_SOME] >> strip_tac >>
  rename1 `tag x k = SOME z` >> PairCases_on `z` >> gvs[] >>
  metis_tac[]
QED
