(* Range induction is supplied by eval_for_rounds_ptr.  Inv and Done name
   the same explicit predicates as the checked one-round boundary. *)
Theory forPtrRangeLoop
Ancestors forPtrRangeAssemble forPtrRangeTerminal forPtrRounds
  bodyPtrDefs loweringPosts stmtSimForLoop vyperInterpreter
Libs monadsyntax

Theorem for_range_loop_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  (!j ei. j < LENGTH vs /\ P ei ==>
    stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <| scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &j); popped := []|>))
          :: ei.scopes; gas_obs := [] |>)) /\
  (!j ei G tn s. Inv j ei G tn s <=>
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j <= Num (n2-n1) /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx ei s /\ ghost_inv d cenv cx ei G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &j)) /\
    lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME a /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
    (!name lo z. local_region cenv ei.scopes s name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  (!ei G tn t. Done ei G tn t <=>
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ei t /\ ghost_inv d cenv cx ei G tn t /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  (!ei j obs r ef sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
        value := IntV (n1 + &j); popped := []|>)) :: ei.scopes;
      gas_obs := obs |>) = (r,ef) /\
    (r = INL () \/ r = INR ContinueException) /\ ef.scopes = sc :: rest ==>
    P (ef with scopes := rest)) /\
  (!ei. P ei ==> not_local_ptr bc (FEMPTY :: ei.scopes) p) /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ret_pc_ok cenv st s0 /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> dv /\ x <> cv /\ x <> nv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  n1 <= n2 /\ LENGTH vs = Num (n2-n1) /\
  (!j. j < LENGTH vs ==> EL j vs = IntV (n1 + &j) /\
    (i2w (n1 + &j) : bytes32) <> i2w n2) ==>
  !k es s G tn.
    k <= LENGTH vs /\ Inv k es G tn s /\
    gas_admissible (eval_for cx tyv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_for cx tyv id stmts (DROP k vs)) (es,s,G,tn)
      (\res ee gf tf t. res = INL () /\ Done ee gf tf t)
      (\res ee gt r. ?ex. res = INR ex /\
        !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >> ho_match_mp_tac eval_for_rounds_ptr >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `P es` by metis_tac[] >>
      `stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
        (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
        (es with <|scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>))
            :: es.scopes; gas_obs := []|>)` by metis_tac[] >>
      `not_local_ptr bc (FEMPTY :: es.scopes) p` by metis_tac[] >>
      drule_all for_range_round_ptr >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Inv _ _ _ _ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  `!x. not_fresh_at st x ==> x <> dv` by metis_tac[] >>
  drule_all for_range_terminal_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `gf`, `tf`] >> simp[] >>
  fs[exprSimWordArgsTheory.stmt_state_rel_gas_obs]
QED
