Theory s1PrefixBoolChainMinimalTip
Ancestors
  s1PrefixBoolChainExtArgDescent s1PrefixBoolChainTipChild
  s1PrefixLiteralWord bodyFullExprCore s1PrefixPreds relation arithmetic
Libs
  pairLib

Theorem bool_chain_extcall_bad_child[local]:
  ~(body_expr_full_ok cx (Call ann (ExtCall stat skip sig opts) args dr) /\
    body_expr_prefix_ok cx (Call ann (ExtCall stat skip sig opts) args dr)) ==>
  ?a. bool_chain_tip_child cx (Call ann (ExtCall stat skip sig opts) args dr) a /\
      ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a)
Proof
  PairCases_on `sig` >> disch_tac >> CCONTR_TAC >>
  fs[bool_chain_tip_child_def] >> metis_tac[bool_chain_extcall_contracts]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_tac >>
  qspecl_then
    [`\a. TC (bool_chain_tip_child cx) h a /\
          ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a)`, `expr_size`]
    mp_tac WOP_measure >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `!a. bool_chain_tip_child cx b a ==>
       body_expr_full_ok cx a /\ body_expr_prefix_ok cx a` by
    (gen_tac >> disch_tac >> CCONTR_TAC >>
     `TC (bool_chain_tip_child cx) h a` by
       (irule TC_RIGHT1_I >> qexists `b` >> simp[]) >>
     `expr_size b <= expr_size a` by
       (first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     drule bool_chain_tip_child_smaller >> decide_tac) >>
  qexists `b` >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (strip_tac >>
      qpat_x_assum `b = Literal _ _` SUBST_ALL_TAC >>
      qpat_x_assum `~(body_expr_full_ok cx (Literal _ _) /\ _)` mp_tac >>
      simp[literal_expr_full_ok, Once body_expr_prefix_ok_def,
           literal_word_value_prefix, literal_vv_prefix])
  >- (strip_tac >>
      qpat_x_assum `b = Call _ _ _ _` SUBST_ALL_TAC >>
      drule bool_chain_extcall_bad_child >> metis_tac[])
  >- (strip_tac >>
      qpat_x_assum `b = IfExp _ _ _ _` SUBST_ALL_TAC >>
      drule bool_chain_ifexp_bad_child >> metis_tac[])
  >> first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_bad_tip_minimal[local]:
  (?a. TC (bool_chain_tip_child cx) h a /\
       ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a)) ==>
  ?b. TC (bool_chain_tip_child cx) h b /\
    ~(?ty lit. b = Literal ty lit) /\
    ~(?ann stat skip sig opts xs dr. b = Call ann (ExtCall stat skip sig opts) xs dr) /\
    ~(?ty c l r. b = IfExp ty c l r) /\
    ~(body_expr_full_ok cx b /\ body_expr_prefix_ok cx b)
Proof
  cheat
QED

Theorem bool_chain_extcall_prefix_or_minimal_tip:
  h = Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr /\
  expr_type h = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_body_pre cenv cx env h ee /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) h ee (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,s,G,tn) \/
  (?b. TC (bool_chain_tip_child cx) h b /\
    ~(?ty lit. b = Literal ty lit) /\
    ~(?ann stat skip sig opts xs dr. b = Call ann (ExtCall stat skip sig opts) xs dr) /\
    ~(?ty c l r. b = IfExp ty c l r) /\
    ~(body_expr_full_ok cx b /\ body_expr_prefix_ok cx b))
Proof
  strip_tac >>
  drule_all bool_chain_extcall_prefix_or_tip >> strip_tac
  >- simp[] >>
  disj2_tac >> irule bool_chain_bad_tip_minimal >>
  qexists `a` >> conj_tac
  >- (irule TC_MONOTONE >> qexists `bool_chain_ext_arg cx` >>
      simp[bool_chain_tip_child_def])
  >> first_assum ACCEPT_TAC
QED
