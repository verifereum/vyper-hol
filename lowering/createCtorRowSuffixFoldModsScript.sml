(* Fold completed linked constructor rows at their observed cuts. *)
Theory createCtorRowSuffixFoldMods
Ancestors
  createExprSizeExitDefsMods list rich_list

Theorem ctor_rows_suffix_fold_by_step_mods:
  LENGTH svs = LENGTH args /\ LENGTH vs = LENGTH args /\
  (!i. SUC i < LENGTH args ==> ?K. valid_horizon cx st0 K (E (SUC i)).storage_trace) /\
  (!i g h. i < LENGTH args /\ J i g h ==>
    expr_body_pre_mods mods ce cx env (EL i args) (E i) /\
    ?a b. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception)
        (E (SUC i)) a b (St (SUC i))) /\
  (!i g h a b. i < LENGTH args /\
    (?K. valid_horizon cx st0 K (E (SUC i)).storage_trace) /\
    (!K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception)
        (E (SUC i)) a b (St (SUC i))) ==>
    J (SUC i) a b) /\
  (!i g h a b G tn. SUC i < LENGTH args /\ J i g h /\
    expr_body_pre_mods mods ce cx env (EL i args) (E i) /\
    (!K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception)
        (E (SUC i)) a b (St (SUC i))) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        [] (DROP (SUC i) args) (DROP (SUC i) svs) (C (SUC i)) (C (LENGTH args))
        (E (SUC i)) (St (SUC i)) a b K (INL (DROP (SUC i) vs) : value list + exception)
        (E (LENGTH args)) G tn (St (LENGTH args))) ==>
    !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        [] (EL i args :: DROP (SUC i) args) (EL i svs :: DROP (SUC i) svs)
        (C i) (C (LENGTH args)) (E i) (St i) g h K
        (INL (EL i vs :: DROP (SUC i) vs) : value list + exception)
        (E (LENGTH args)) G tn (St (LENGTH args))) ==>
  !i. i < LENGTH args ==> !g h. J i g h ==>
    ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        [] (DROP i args) (DROP i svs) (C i) (C (LENGTH args)) (E i) (St i) g h K
        (INL (DROP i vs) : value list + exception) (E (LENGTH args)) G tn (St (LENGTH args))
Proof
  strip_tac >> gen_tac >> measureInduct_on `LENGTH args - i` >> rpt strip_tac >>
  qpat_assum `!j p q. j < LENGTH args /\ J j p q ==> _`
    (qspecl_then [`i`,`g`,`h`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`a`,`b`] assume_tac)) >>
  `DROP i args = EL i args :: DROP (SUC i) args` by simp[DROP_CONS_EL] >>
  `DROP i svs = EL i svs :: DROP (SUC i) svs` by simp[DROP_CONS_EL] >>
  `DROP i vs = EL i vs :: DROP (SUC i) vs` by simp[DROP_CONS_EL] >>
  Cases_on `SUC i = LENGTH args`
  >- (qexistsl_tac [`a`,`b`] >> fs[DROP_LENGTH_NIL_rwt]) >>
  `SUC i < LENGTH args` by decide_tac >>
  qpat_assum `!j. SUC j < LENGTH args ==> _` (drule_then assume_tac) >>
  `J (SUC i) a b` by
    (first_x_assum irule >> simp[] >> qexistsl_tac [`g`,`h`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!j. LENGTH args - j < LENGTH args - i ==> _`
    (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[] >>
  disch_then (qspecl_then [`a`,`b`] (drule_then (qx_choosel_then [`G`,`tn`] assume_tac))) >>
  qexistsl_tac [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> qexistsl_tac [`a`,`b`] >> simp[]
QED
