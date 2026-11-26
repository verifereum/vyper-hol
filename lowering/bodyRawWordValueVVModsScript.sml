(* Transport the linked word-list CPS rule across a Value-only result. *)
Theory bodyRawWordValueVVMods
Ancestors
  bodyRawRequestWordsMods gasOutcomeFullMods gasStorage gasContext
  exprSimDefs vyperStorageTrace vyperState sum pair combin

Triviality value_sum_injective:
  (SUM_MAP Value I x = SUM_MAP Value I y) <=> x = y
Proof
  Cases_on `x` >> Cases_on `y` >> simp[]
QED

Triviality value_result_equation:
  (!st. wrapped st = (SUM_MAP Value I (FST (plain st)), SND (plain st))) ==>
  (wrapped st = (SUM_MAP Value I res, ee) <=> plain st = (res,ee))
Proof
  strip_tac >> Cases_on `plain st` >> simp[value_sum_injective]
QED

Triviality value_result_ignore:
  (!st. wrapped st = (SUM_MAP Value I (FST (plain st)), SND (plain st))) ==>
  ignore_bind wrapped (return ()) = ignore_bind plain (return ())
Proof
  strip_tac >> simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `plain x` >> Cases_on `q` >> simp[]
QED

(* Reuse the same marked path and both focus alternatives. In the normal
   branch, recover the unwrapped result from the empty gas tail. *)
Triviality value_result_outcome:
  (!st. wrapped st = (SUM_MAP Value I (FST (plain st)), SND (plain st))) ==>
  (gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
     wrapped (es,s,G,tn) Q R <=>
   gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
     plain (es,s,G,tn)
     (\H res ee g tt t. Q H (SUM_MAP Value I res) ee g tt t)
     (\H res ee gt r. R H (SUM_MAP Value I res) ee gt r))
Proof
  strip_tac >> drule_then (mk_asm "ign") value_result_ignore >>
  `!marks. gas_bad_storage_at cx st0 wrapped es s marks =
           gas_bad_storage_at cx st0 plain es s marks` by
    simp[gas_bad_storage_at_def] >>
  pop_assum (mk_asm "bad") >>
  `!raw r. create_size_exit_ok ctx (SUM_MAP Value I raw) r =
           create_size_exit_ok ctx raw r` by
    (Cases_on `raw` >> simp[createSizeExitTheory.create_size_exit_ok_def]) >>
  pop_assum (mk_asm "create_size") >>
  asm "ign" (fn ign => asm "bad" (fn bad =>
    simp[NoAsms, gas_outcome_full_mods_def, ign, bad])) >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  iff_tac >> strip_tac
  >- (qabbrev_tac `reads = gas_explicit marks s.vs_gas_readings` >>
      qabbrev_tac `raw = FST (plain (es with gas_obs := reads))` >>
      `res = SUM_MAP Value I raw` by
        (qpat_assum `!tail. wrapped (_ with gas_obs := _) = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `!st. wrapped st = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms, Abbr `raw`] >> metis_tac[]) >>
      qexistsl [`raw`,`ee`,`r`,`G'`,`tn'`] >>
      qpat_x_assum `res = SUM_MAP Value I raw` SUBST_ALL_TAC >>
      drule value_result_equation >> strip_tac >>
      simp[] >> conj_tac
      >- (qpat_assum `!st res ee. wrapped st = _ <=> _`
            (fn th => pure_once_rewrite_tac[GSYM th]) >>
          first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then mp_tac) >>
      asm "create_size" (fn th => simp[NoAsms,th])) >>
  rename1 `gas_origin_ptr_path _ _ _ (r,g,tt)` >>
  qexistsl [`SUM_MAP Value I res`,`ee`,`r`,`g`,`tt`] >>
  asm "create_size" (fn th => simp[th])
QED

Triviality value_result_read:
  (!st pv u. action st = (INL pv,u) ==> ?v. pv = Value v) ==>
  !st. action st = (SUM_MAP Value I (FST (bind action (read_result cx) st)),
                  SND (bind action (read_result cx) st))
Proof
  strip_tac >> gen_tac >> Cases_on `action st` >> Cases_on `q` >>
  gvs[bind_def,read_result_def,return_def] >>
  first_x_assum drule >> strip_tac >> simp[read_result_def,return_def]
QED

Triviality value_result_bind:
  (!vs st pv u. k vs st = (INL pv,u) ==> ?v. pv = Value v) ==>
  !st. bind args k st =
    (SUM_MAP Value I (FST (bind args (\vs. bind (k vs) (read_result cx)) st)),
     SND (bind args (\vs. bind (k vs) (read_result cx)) st))
Proof
  strip_tac >> once_rewrite_tac[GSYM bind_assoc] >> irule value_result_read >>
  rpt gen_tac >> simp[bind_def] >>
  Cases_on `args st` >> Cases_on `q` >> simp[] >> metis_tac[]
QED

Triviality value_result_ok:
  expr_vv_res_ok (SUM_MAP Value I res) <=> expr_res_ok res
Proof
  Cases_on `res` >> simp[expr_vv_res_ok_def,expr_res_ok_def]
QED

Triviality value_result_admissibility:
  (!st. wrapped st = (SUM_MAP Value I (FST (plain st)), SND (plain st))) ==>
  (gas_admissible wrapped expr_vv_res_ok ee <=> gas_admissible plain expr_res_ok ee)
Proof
  strip_tac >> simp[gas_admissible_def, FORALL_PROD, value_result_ok] >>
  eq_tac >> strip_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `gs` mp_tac) >> simp[]) >>
  gen_tac >> Cases_on `plain (ee with gas_obs := gs)` >> simp[] >> metis_tac[]
QED

Triviality value_result_exit:
  expr_exit (SUM_MAP Value I res) r = expr_exit res r /\
  halt_exit H cx ee (SUM_MAP Value I res) r = halt_exit H cx ee res r
Proof
  Cases_on `res` >> simp[halt_exit_def, stmtSimPropsTheory.expr_exit_INR_type]
QED

val request_vv_entry = ``\(H : (bool # 256 word # type_value) list # num list).
  stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0``;

val request_vv_endpoint = ``\(H : (bool # 256 word # type_value) list # num list).
  typed_args_post H ctx func cenv cx es sa s0 ee ws xs vs t /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem request_word_value_vv_prefix_mods:
  !ws es sa shadow_sa xs sb shadow_sb s0 G0 tn0
      (k : value list -> evaluation_state -> eval_result evaluation_result).
  body_exprs_full_ok_mods mods exps cx ws /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  (!e mid. MEM e ws /\ expr_sim_inv_mods mods cenv cx env mid /\
     body_const_cells_agree_mods mods cx env mid ==>
     expr_body_pre_mods mods cenv cx env e mid) /\
  EVERY (is_word_type o expr_type) ws /\
  (!e. MEM e ws ==> arg_ty (gas_shadow_expr e) = arg_ty e) /\
  lower_word_args cenv arg_ty ws sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) arg_ty
    (MAP gas_shadow_expr ws) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_exprs cx ws) k) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> (^request_vv_entry) H) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\
  (!vs st pv st'. k vs st = (INL pv,st') ==> ?v. pv = Value v) /\
  (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r) /\
  (!reads vs ee G tn t.
     (!tail. eval_exprs cx ws (es with gas_obs := reads ++ tail) =
         (INL vs,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> (^request_vv_endpoint) H) /\
     LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                           value_has_type tv v) ws vs /\
     EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) xs /\
     EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at sb z)) xs /\
     expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
     t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
     gas_admissible (k vs) expr_vv_res_ok ee ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (k vs) (ee,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx ws) k) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule value_result_bind >>
  disch_then (qspecl_then [`cx`,`eval_exprs cx ws`] assume_tac) >>
  pop_assum (fn rel =>
    assume_tac (Q.INST [`ee` |-> `es`] (MATCH_MP value_result_admissibility rel)) >>
    once_rewrite_tac[MATCH_MP value_result_outcome rel]) >>
  irule request_word_prefix_mods >> BETA_TAC >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result])
  >- (rpt strip_tac >> qpat_assum `!H res ee gt r. _ ==> R H res ee gt r` irule >>
      simp[value_result_exit])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- fs[]
  >- first_assum ACCEPT_TAC >>
  qexistsl [`arg_ty`,`d`,`env`,`exps`,`mods`,`sa`,`sb`,`shadow_func`,`shadow_sa`,
            `shadow_sb`,`src`,`tops`,`xs`] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `!st. k vs st = (SUM_MAP Value I (FST (bind (k vs) (read_result cx) st)),
                   SND (bind (k vs) (read_result cx) st))` by
    (irule value_result_read >> metis_tac[]) >>
  pop_assum (fn rel =>
    assume_tac (Q.INST [`ee` |-> `ee`] (MATCH_MP value_result_admissibility rel)) >>
    irule (iffLR (MATCH_MP value_result_outcome rel))) >>
  qpat_assum `!reads vs ee G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (k vs) _ _ _` irule >>
  rpt conj_tac
  >~ [`gas_admissible (k vs) expr_vv_res_ok ee`] >- fs[]
  >- (qexists `reads` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _` drule >> simp[]
QED
