(* Concrete callback-to-round suffix.  Scope projection precedes the
   signed backedge; a break retains the callback ghost and target state. *)
Theory forPtrRangeFinish
Ancestors forPtrRangeBackedge forPtrRangeSource forPtrRoundCleanup
  forPtrRangeLanding
  forPtrRangeTerminal stmtSimForLoop bodyPtrDefs loweringPosts venomState
  fragGasPathPtr

Theorem for_range_callback_finish_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  (!ei j obs r ef sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
        value := IntV (n1 + &j); popped := []|>)) :: ei.scopes;
      gas_obs := obs |>) = (r,ef) /\
    (r = INL () \/ r = INR ContinueException) /\ ef.scopes = sc :: rest ==>
    P (ef with scopes := rest)) /\
  P es /\ lookup_scopes id es.scopes = NONE /\ k < Num (n2-n1) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  eval_stmts cx stmts (es with <| scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tyv;
      value := IntV (n1 + &k); popped := []|>)) :: es.scopes;
    gas_obs := obs |>) = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee s /\
  ghost_inv d c3 cx ee G tn s /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  ptr_covers G tn p s sz /\ lookup_var p s = SOME a /\
  lookup_var cv s = SOME (i2w (n1 + &k)) /\
  lookup_var ev s = SOME (i2w n2) /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ (res = INL () ==> ~block_is_terminated sb1) /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?sc rest t gf tf.
    ee.scopes = sc :: rest /\
    gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK t) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (ee with scopes := rest) t /\
    ghost_inv d cenv cx (ee with scopes := rest) gf tf t /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    (res = INR BreakException ==> t.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==>
      t.vs_current_bb = cond_lbl /\ P (ee with scopes := rest) /\
      lookup_scopes id rest = NONE /\ SUC k <= Num (n2-n1) /\
      lookup_var cv t = SOME (i2w (n1 + &(SUC k))) /\
      lookup_var ev t = SOME (i2w n2) /\ lookup_var p t = SOME a /\
      FLOOKUP gf cv = NONE /\ FLOOKUP gf ev = NONE /\
      op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {} /\
      ptr_covers gf tf p t sz /\
      FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
      (!name lo z. local_region cenv rest t name lo z ==>
        regions_disjoint (w2n a) sz lo z))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`esk` |-> `es with gas_obs := obs`] for_range_callback_landing_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK land)` >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`sc`, `rest`, `land`, `G`, `tn`] >>
      gvs[Abbr `land`]) >>
  suspend "next"
QED

Resume for_range_callback_finish_ptr[next]:
  `res = INL () \/ res = INR ContinueException` by fs[stmt_lands_def] >> (
  `P (ee with scopes := rest) /\ lookup_scopes id rest = NONE` by
    (simp[] >> qpat_x_assum `!ei j obs r ef sc rest. _` irule >> simp[] >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `land.vs_current_bb = incr_lbl /\ SUC k <= Num (n2-n1)` by simp[] >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x land = SOME v)` by metis_tac[] >>
  `lookup_var cv land = SOME (i2w (n1 + &k)) /\
   lookup_var ev land = SOME (i2w n2) /\ lookup_var p land = SOME a /\
   FLOOKUP land.vs_allocas ainst.inst_id = SOME (w2n a,sz)` by simp[] >>
  mp_tac (SRULE [] (Q.INST
    [`es` |-> `ee with scopes := rest`, `s` |-> `land`]
    (SPEC_ALL (SRULE [] for_range_backedge_restore_ptr)))) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn land 0 gf tf (OK fin)` >>
  `!y. lookup_var y fin =
       lookup_var y (update_var cv (i2w (n1 + &(k + 1)))
                       (update_var nv (i2w (n1 + &(k + 1))) land))`
    by simp[Abbr `fin`] >>
  qexistsl_tac [`sc`, `rest`, `fin`, `gf`, `tf`] >> simp[] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[])
QED
Finalise for_range_callback_finish_ptr
