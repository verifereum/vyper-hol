(* Same-run sequencing for a linked declaration with an allocated destination. *)
Theory bodyAnnCopySequenceMods
Ancestors
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods
  stmtSimDeclSource exprSimDefs vyperStorageTrace vyperStorageFootprint
  gasExemptCertMods loweringPosts

Theorem ann_copy_sequence_at_entry[local]:
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + exception) r /\
    halt_exit H cx ee (INR exc) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) /\
  (!marks res mid G tn s.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H res mid G tn s /\ ~s.vs_halted /\ mid.gas_obs = []) ==>
    ?v out t Gf tf. res = INL v /\
      (!tail. new_variable id dtv v (mid with gas_obs := tail) =
        (INL (),out with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H out.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,Gf,tf) /\
        Q H (INL ()) (out with gas_obs := []) Gf tf t)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,entry,Ga,tna) Q R
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn u. P H res ee G tn u /\
                    ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >- (BETA_TAC >> rpt strip_tac >> disj1_tac >>
      qpat_x_assum `!marks res mid G tn s. _`
        (drule_all_then (qx_choosel_then [`v`,`out`,`dst`,`Gf`,`tf`] strip_assume_tac)) >>
      `~t.vs_halted` by
        (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         fs[storage_trace_domain_def]) >>
      qexists_tac `v` >> simp[] >> irule gas_outcome_full_mods_pure >>
      conj_tac >- (qexistsl_tac [`Gf`,`out`,`INL ()`,`dst`,`tf`] >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[] >>
  first_x_assum irule >> fs[halt_exit_def]
QED

(* Only the return-buffer floor is added at the outcome level; the suffix
   supplies the path and its installed post at the very same endpoint. *)
Theorem ann_copy_sequence_installed_mods:
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + exception) r /\
    halt_exit H cx ee (INR exc) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) /\
  (!marks res mid G tn s.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H res mid G tn s /\ ~s.vs_halted /\ mid.gas_obs = []) ==>
    ?v out t Gf tf. res = INL v /\
      (!tail. new_variable id dtv v (mid with gas_obs := tail) =
        (INL (),out with gas_obs := tail)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      (!H. valid_horizon cx st0 H out.storage_trace ==>
        (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) ==>
        Q H (INL ()) (out with gas_obs := []) Gf tf t)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qabbrev_tac `Q0 = \H res ee G tn t.
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) ==>
    Q H res ee G tn t` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. Q0 H res ee G tn t /\
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)`, `R`] >>
  conj_tac >- simp[Abbr `Q0`] >>
  conj_tac >- simp[] >>
  ho_match_mp_tac gas_outcome_full_mods_return_buf_allocas >>
  reverse conj_tac >- simp[] >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- simp[] >>
  irule ann_copy_sequence_at_entry >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`P`,`dtv`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!marks res mid G tn s. _`
    (drule_all_then (qx_choosel_then [`v`,`out`,`dst`,`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`v`,`out`,`dst`,`Gf`,`tf`] >> simp[Abbr `Q0`]
QED
