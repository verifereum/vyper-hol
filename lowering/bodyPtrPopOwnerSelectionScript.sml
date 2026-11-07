Theory bodyPtrPopOwnerSelection
Ancestors vyperState vyperPlaceResultTyping list

Theorem pop_owner_read_decompose:
  !hs rt q v. read_popped rt q hs = SOME v ==>
  ?pre p old post ptv.
    hs = pre ++ (p,old)::post /\ read_popped rt q pre = NONE /\
    IS_PREFIX q p /\ subscripts_type rt p = SOME ptv /\
    evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL v
Proof
  Induct >> simp[read_popped_def] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[read_popped_def] >>
  Cases_on `IS_PREFIX q h0`
  >- (Cases_on `subscripts_type rt h0`
      >- (simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
          qexistsl_tac [`(h0,h1)::pre`,`p`,`old`,`post`,`ptv`] >> simp[read_popped_def]) >>
      rename1 `subscripts_type rt h0 = SOME ty` >>
      Cases_on `evaluate_subscripts ty h1 (DROP (LENGTH h0) q)`
      >- (simp[] >> strip_tac >> qexistsl_tac [`[]`,`h0`,`h1`,`hs`,`ty`] >>
          simp[read_popped_def]) >>
      simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
      qexistsl_tac [`(h0,h1)::pre`,`p`,`old`,`post`,`ptv`] >> simp[read_popped_def]) >>
  simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`(h0,h1)::pre`,`p`,`old`,`post`,`ptv`] >> simp[read_popped_def]
QED

Theorem pop_owner_read_skip:
  !pre rt q post. read_popped rt q pre = NONE ==>
    read_popped rt q (pre ++ post) = read_popped rt q post
Proof
  Induct >> simp[read_popped_def] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[read_popped_def] >>
  Cases_on `IS_PREFIX q h0` >> simp[] >>
  Cases_on `subscripts_type rt h0` >> simp[] >>
  rename1 `subscripts_type rt h0 = SOME ty` >>
  Cases_on `evaluate_subscripts ty h1 (DROP (LENGTH h0) q)` >> simp[]
QED

Theorem pop_owner_read_reconstruct:
  read_popped rt q pre = NONE /\ IS_PREFIX q p /\
  subscripts_type rt p = SOME ptv /\
  evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL v ==>
  read_popped rt q (pre ++ (p,old)::post) = SOME v
Proof
  strip_tac >> drule pop_owner_read_skip >> simp[read_popped_def]
QED

Theorem pop_owner_replace_skip:
  !pre rt q replacement post.
  read_popped rt q pre = NONE ==>
  replace_popped rt q replacement (pre ++ post) =
    OPTION_MAP (APPEND pre) (replace_popped rt q replacement post)
Proof
  Induct
  >- (rpt gen_tac >> simp[] >> Cases_on `replace_popped rt q replacement post` >> simp[]) >>
  simp[read_popped_def] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[read_popped_def, replace_popped_def] >>
  Cases_on `IS_PREFIX q h0` >> simp[]
  >- (Cases_on `subscripts_type rt h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] >>
      Cases_on `replace_popped rt q replacement post` >> simp[]) >>
      rename1 `subscripts_type rt h0 = SOME ty` >>
      Cases_on `evaluate_subscripts ty h1 (DROP (LENGTH h0) q)` >> simp[] >>
      strip_tac >> first_x_assum drule >> simp[optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] >>
      Cases_on `replace_popped rt q replacement post` >> simp[]) >>
  strip_tac >> first_x_assum drule >> simp[optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] >>
      Cases_on `replace_popped rt q replacement post` >> simp[]
QED

Theorem pop_owner_replace_exact:
  read_popped rt q pre = NONE /\ IS_PREFIX q p /\
  subscripts_type rt p = SOME ptv /\
  evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL v ==>
  (replace_popped rt q replacement (pre ++ (p,old)::post) = SOME hs' <=>
    ?updated. assign_subscripts ptv old (DROP (LENGTH p) q) (Replace replacement) = INL updated /\
      hs' = pre ++ (p,updated)::post)
Proof
  strip_tac >> drule pop_owner_replace_skip >>
  disch_then (qspecl_then [`replacement`,`(p,old)::post`] mp_tac) >>
  simp[replace_popped_def] >> disch_then SUBST1_TAC >>
  Cases_on `assign_subscripts ptv old (DROP (LENGTH p) q) (Replace replacement)` >> simp[] >>
  metis_tac[]
QED
