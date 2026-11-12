(* Same-witness composition of successful-result and unconditional safety transfer. *)
Theory decoderEndpointComposition
Ancestors
  fragExecMem memSafeRun

Theorem decoder_endpoint_compose:
  let Safe = \s t. !fuel r.
        run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s)
  in
  (?u. H u /\ Safe initial u /\ Pull initial u) /\
  (!u. H u ==> ?t. Post t /\ Safe u t /\ Pull u t) ==>
  ?t. Post t /\ Safe initial t /\ Pull initial t
Proof
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >> strip_tac >>
  first_x_assum drule >> strip_tac >> qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (qpat_x_assum `Safe initial u` mp_tac >>
      qpat_x_assum `Safe u t` mp_tac >>
      simp_tac bool_ss [Abbr `Safe`] >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qpat_x_assum `Pull initial u` mp_tac >>
  qpat_x_assum `Pull u t` mp_tac >>
  simp_tac bool_ss [Abbr `Pull`] >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED
