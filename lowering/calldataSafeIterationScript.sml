(* Safe continuation composition, with independent fuels and early exits.
   No claim about any particular emitted loop is made here. *)
Theory calldataSafeIteration
Ancestors
  fragExecMem fragExec memSafeRun venomExecSemantics venomState
  compileEnv arithmetic

Theorem calldata_safe_transfer_trans:
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn t = r /\
      (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn t)) ==>
  (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn s))
Proof
  metis_tac[]
QED

Theorem calldata_safe_exit_pullback:
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  (?fuel r. run_from fuel ctx fn t = r /\ exit_result r /\ R r /\
     mem_safe_run fuel ctx fn t) ==>
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
     mem_safe_run fuel ctx fn s
Proof
  metis_tac[exit_result_not_error]
QED

Theorem calldata_safe_finite_iteration:
  !bound i Inv Q ctx fn R s.
  i <= bound /\ Inv i s /\
  (!j u. Inv j u /\ j < bound ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v. Inv (SUC j) v /\
      !fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
  (!u. Inv bound u ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v. Q v /\
      !fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) ==>
  (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s) \/
  ?t. Q t /\
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qabbrev_tac `X = \s. ?fuel r.
    run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  `!a b c. Rel a b /\ Rel b c ==> Rel a c` by
    (simp_tac pure_ss [Abbr `Rel`] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC calldata_safe_transfer_trans) >>
  `!a b. Rel a b /\ X b ==> X a` by
    (simp_tac pure_ss [Abbr `Rel`, Abbr `X`] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC calldata_safe_exit_pullback) >>
  qid_spec_tac `s` >> completeInduct_on `bound-i` >> rpt strip_tac >>
  Cases_on `i = bound` >- metis_tac[] >>
  `i < bound` by decide_tac >>
  `X s \/ ?v. Inv (SUC i) v /\ Rel s v` by metis_tac[]
  >- simp[] >>
  rename1 `Inv (SUC i) next` >>
  `X next \/ ?t. Q t /\ Rel next t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `bound-SUC i` mp_tac) >>
     impl_tac >- decide_tac >>
     disch_then (qspecl_then [`bound`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[]) >>
  metis_tac[]
QED

Theorem calldata_frag_mem_endpoint:
  frag_exec_mem ctx st last P Q R /\ fn_has_code st last fn /\ P s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
     mem_safe_run fuel ctx fn s) \/
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  simp[frag_exec_mem_def] >> metis_tac[]
QED
