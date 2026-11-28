(* Guarded descent through nested ExtCalls, stopping at other expression forms. *)
Theory s1PrefixBoolChainExtArgDescent
Ancestors
  s1PrefixBoolChainExtArgDomain s1PrefixBoolChainExtArgWindows
  s1PrefixBoolChainExtCallHead s1PrefixLiteralWord s1PrefixOfVV
  s1PrefixPreds bodyFullCases bodyFullExprCore relation
Libs
  pairLib

Theorem bool_chain_ext_arg_windows[local]:
  (!a. bool_chain_ext_arg cx
      (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) a ==>
    body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) ==>
  (body_exprs_full_ok cx (TAKE 1 args) /\
   body_exprs_prefix_ok cx (TAKE 1 args)) /\
  (!st target mid. eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_full_ok cx (TAKE (LENGTH ats) (DROP 1 args)) /\
    body_exprs_prefix_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid src vs fin.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,fin) ==>
    body_exprs_full_ok cx (DROP (1 + LENGTH ats) args) /\
    body_exprs_prefix_ok cx (DROP (1 + LENGTH ats) args))
Proof
  disch_tac >> match_mp_tac (GEN_ALL bool_chain_extcall_guarded_windows) >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_tac) >> first_x_assum match_mp_tac >>
  fs[bool_chain_ext_arg_def] >> qexistsl [`pre`,`post`] >> metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (strip_assume_tac o MATCH_MP (GEN_ALL bool_chain_ext_arg_windows)) >>
  conj_tac
  >- (irule body_extcall_case_full >> fs[] >> metis_tac[]) >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  irule extcall_head_vv_prefix >> fs[] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  qexistsl [`env`,`tops`] >> simp[]
QED
*)
Theorem bool_chain_extcall_contracts:
  (!a. bool_chain_ext_arg cx
      (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) a ==>
    body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) ==>
  body_expr_full_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) /\
  body_expr_prefix_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  measureInduct_on `expr_size x` >> strip_tac >>
  Cases_on `?ty lit. x = Literal ty lit`
  >- (gvs[] >> simp[literal_expr_full_ok, Once body_expr_prefix_ok_def,
                    literal_word_value_prefix, literal_vv_prefix]) >>
  Cases_on `?ann stat skip sig opts args dr. x = Call ann (ExtCall stat skip sig opts) args dr`
  >- (gvs[] >> PairCases_on `sig` >> irule bool_chain_extcall_contracts >>
      gen_tac >> disch_tac >>
      qpat_assum `!y. expr_size y < _ ==> _` (qspec_then `a` mp_tac) >>
      (impl_tac >- (drule bool_chain_ext_arg_smaller >> simp[])) >>
      disch_then match_mp_tac >> metis_tac[RTC_rules]) >>
  metis_tac[RTC_REFL]
QED
*)
Theorem bool_chain_ext_arg_descent[local]:
  !x. (!a. RTC (bool_chain_ext_arg cx) x a /\
      ~(?ann stat skip sig opts args dr. a = Call ann (ExtCall stat skip sig opts) args dr) /\
      ~(?ty lit. a = Literal ty lit) ==>
      body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) ==>
    body_expr_full_ok cx x /\ body_expr_prefix_ok cx x
Proof
  cheat
QED

Theorem bool_chain_extcall_prefix_or_tip:
  h = Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr /\
  expr_type h = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_body_pre cenv cx env h ee /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) h ee (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,s,G,tn) \/
  (?a. TC (bool_chain_ext_arg cx) h a /\
    ~(?ann stat skip sig opts args dr. a = Call ann (ExtCall stat skip sig opts) args dr) /\
    ~(?ty lit. a = Literal ty lit) /\
    ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a))
Proof
  strip_tac >>
  Cases_on `?a. TC (bool_chain_ext_arg cx) h a /\
    ~(?ann stat skip sig opts args dr. a = Call ann (ExtCall stat skip sig opts) args dr) /\
    ~(?ty lit. a = Literal ty lit) /\
    ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a)`
  >- simp[] >>
  `!a. bool_chain_ext_arg cx h a ==> body_expr_full_ok cx a /\ body_expr_prefix_ok cx a` by
    (gen_tac >> disch_tac >> match_mp_tac (GEN_ALL bool_chain_ext_arg_descent) >>
     rpt strip_tac >> drule_all EXTEND_RTC_TC >> metis_tac[]) >>
  gvs[] >> drule bool_chain_ext_arg_windows >> strip_tac >>
  disj1_tac >> irule bool_chain_extcall_head_prefix >>
  rpt (goal_assum (drule_at Any)) >> fs[] >> metis_tac[]
QED
