(* The linked Range route sequences the two forced evaluations before
   transferring control to the checked counter setup. *)
Theory bodyForRangeRouteMods
Ancestors
  bodyFullPredsMods bodySimDeclCases bodyFullForRange
  gasOutcomeFullBindMods gasExemptCertMods gasOutcomeFull gasOutcomeFullMods gasExemptCert
  gasShadow gasShadowCompileBase gasShadowCompileStmtHelpers bodyFullShared stmtSimForRange stmtLoweringMono
  exprLoweringProps fragExec compileEnv exprBopSimProps loweringPosts bodyFullPostsMods
  bodyForEntryInputsMods
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  list integer

val _ = Parse.hide "body";

Theorem eval_stmt_range_bind_mods:
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  eval_stmt cx (For id typ (Range e1 e2) bound body) =
  do v1 <- bind (eval_expr cx e1) (read_result cx);
     v2 <- bind (eval_expr cx e2) (read_result cx);
     rl <- lift_sum (get_range_limits v1 v2);
     check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
     eval_for cx tyv id body
       (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))
  od
Proof
  strip_tac >> pure_once_rewrite_tac[Once evaluate_def] >>
  simp[LET_THM, lift_option_type_def] >>
  pure_once_rewrite_tac[Once evaluate_def] >>
  simp[LET_THM, bind_assoc, bind_return, LENGTH_GENLIST]
QED

(* Bind the result of a forced endpoint, without restricting exempt errors
   to the active module. The continuation receives the actual source replay. *)
Theorem range_endpoint_bind_mods[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> P H v mid G1 tn1 t) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (next v) (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >> qpat_assum `!marks v mid G1 tn1 t. _` irule >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem range_full_endpoints_mods:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e1) (read_result cx)) (es,s,G,tn)
    (\H res ee G1 tn1 t1. ?v. res = INL v /\ P1 H v ee G1 tn1 t1)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!marks1 v1 mid1 G1 tn1 t1.
    (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit marks1 s.vs_gas_readings ++ tail) =
      (INL v1, mid1 with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid1.storage_trace /\
    (!H. valid_horizon cx st0 H mid1.storage_trace ==> P1 H v1 mid1 G1 tn1 t1) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (bind (eval_expr cx e2) (read_result cx)) (mid1,t1,G1,tn1)
      (\H res ee G2 tn2 t2. ?v. res = INL v /\ P2 v1 mid1 G1 tn1 t1 H v ee G2 tn2 t2)
      (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
    (!marks2 v2 mid2 G2 tn2 t2.
      (!tail. bind (eval_expr cx e2) (read_result cx)
        (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ tail) =
        (INL v2, mid2 with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid2.storage_trace /\
      (!H. valid_horizon cx st0 H mid2.storage_trace ==>
           P2 v1 mid1 G1 tn1 t1 H v2 mid2 G2 tn2 t2) ==>
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (do rl <- lift_sum (get_range_limits v1 v2);
            check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
            eval_for cx tyv id body
              (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
        (mid2,t2,G2,tn2) Q R)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Range e1 e2) bound body)) (es,s,G,tn) Q R
Proof
  strip_tac >> drule eval_stmt_range_bind_mods >>
  disch_then (pure_once_rewrite_tac o single) >>
  qmatch_goalsub_abbrev_tac `bind (bind (eval_expr cx e1) _) next1` >>
  irule range_endpoint_bind_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac
  >- (simp[Abbr `next1`] >> gen_tac >> irule storage_trace_frame_bind_all
      >> reverse conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, evaluate_storage_trace_frame]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_assum `!marks1 v1 mid1 G1 tn1 t1. _` (drule_all_then strip_assume_tac) >>
  simp[Abbr `next1`] >>
  qmatch_goalsub_abbrev_tac `bind (bind (eval_expr cx e2) _) next2` >>
  irule range_endpoint_bind_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx e2) _) _ _ _`
    (irule_at Any) >>
  conj_tac
  >- (simp[Abbr `next2`] >> gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, evaluate_storage_trace_frame]) >>
  simp[Abbr `next2`] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!marks2 v2 mid2 G2 tn2 t2. _` (drule_all_then (ACCEPT_TAC o BETA_RULE))
QED

(* The second expression judgment is conditional on the actual forced
   success of the first endpoint, not on a successful complete iterator. *)
Theorem range_iterator_second_mods:
  body_iterator_full_ok_mods mods exps cx (Range e1 e2) /\
  bind (eval_expr cx e1) (read_result cx) es = (INL v,es1) ==>
  body_expr_full_ok_mods mods exps cx e2
Proof
  simp[body_iterator_full_ok_mods_def, bind_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* The range checks themselves never need the exemption branch. Reuse
   the scalar setup run irrespective of the module list used for that run. *)
Definition range_counter_source_def:
  range_counter_source n1 n2 bound =
    do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
       check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
       return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od
End

Theorem range_counter_source_cases:
  range_counter_source n1 n2 bound =
    if n2 < n1 then raise (Error (RuntimeError "no range"))
    else if bound < Num (n2 - n1) then
      raise (Error (RuntimeError "For too long"))
    else return (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))
Proof
  `n2 < n1 <=> ~(n1 <= n2)` by intLib.COOPER_TAC >>
  `bound < Num (n2 - n1) <=> ~(Num (n2 - n1) <= bound)` by decide_tac >>
  Cases_on `n1 <= n2` >> Cases_on `Num (n2 - n1) <= bound` >>
  simp[range_counter_source_def, get_range_limits_def, lift_sum_def,
       vyperValueTheory.compatible_bound_def, check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, FUN_EQ_THM]
QED

Theorem range_counter_outcome_mods:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (range_counter_source n1 n2 bound) (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (range_counter_source n1 n2 bound) (es,s,G,tn) Q R
Proof
  simp[gas_outcome_full_def, gas_outcome_full_mods_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  disj2_tac
  >- (disj1_tac >> metis_tac[]) >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  Cases_on `n2 < n1` >> Cases_on `bound < Num (n2 - n1)` >>
  simp[range_counter_source_cases, ignore_bind_def, bind_def, raise_def, return_def] >>
  strip_tac >> gvs[e2eDefsTheory.unspecified_behaviour_exempt_def]
QED

Theorem range_counter_rounds_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (range_counter_source n1 n2 bound) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?rs. res = INL rs /\ Ready H rs ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!rs mid G1 tn1 t.
    n1 <= n2 /\ Num (n2 - n1) <= bound /\
    rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> Ready H rs mid G1 tn1 t) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (eval_for cx tyv id body rs) (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id body
          (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  `bind (range_counter_source n1 n2 bound) (eval_for cx tyv id body) =
       do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
          check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
          eval_for cx tyv id body
            (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od` by
    simp[range_counter_source_def, bind_assoc, ignore_bind_def, bind_return] >>
  pop_assum (pure_once_rewrite_tac o single o GSYM) >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_results >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_results >> simp[])
  >~ [`storage_trace_frame (range_counter_source _ _ _)`]
  >- (rw[range_counter_source_cases] >>
      simp[storage_trace_frame_return, storage_trace_frame_raise])
  >~ [`!rs. storage_trace_frame (eval_for _ _ _ _ rs)`]
  >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G1 tn1 t. ?rs. res = INL rs /\ Ready H rs ee G1 tn1 t` >>
  reverse conj_tac >- simp[] >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!tail. range_counter_source _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
  Cases_on `n2 < n1` >> simp[range_counter_source_cases, raise_def] >>
  Cases_on `bound < Num (n2 - n1)` >> simp[raise_def, return_def] >>
  strip_tac >> gvs[] >> first_x_assum irule >> simp[] >> intLib.COOPER_TAC
QED

(* Both successful endpoint values inhabit the loop's declared integer
   type. Only a checked, nonempty iterator activates the body judgment. *)
Theorem range_iterator_success_mods:
  bind (eval_expr cx e1) (read_result cx) es = (INL (IntV n1),es1) /\
  bind (eval_expr cx e2) (read_result cx) es1 = (INL (IntV n2),es2) /\
  n1 <= n2 ==>
  eval_iterator cx (Range e1 e2) es =
    (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),es2)
Proof
  strip_tac >> gvs[bind_def,AllCaseEqs()] >>
  simp[Once evaluate_def,bind_def,get_range_limits_def,lift_sum_def,return_def]
QED

(* Code growth between the endpoint intervals follows from the exact
   checked suffix of the same compiled For, not from whole-loop growth. *)
Theorem range_checked_endpoint_intervals[local]:
  compile_stmt cenv lctx ret_ty (For id typ (Range e1 e2) bound body) a = ((),b) /\
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
  lower_value compile_expr cenv typ e1 a = (op1,m) /\
  lower_value compile_expr cenv typ e2 m = (op2,z) /\
  cenv.ce_alloca_locals /\ fn_has_code a b func ==>
  fn_has_code a m func /\ fn_has_code m z func /\ fn_has_code z b func
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m z` by metis_tac[compile_expr_grows] >>
  `cs_extends a z` by metis_tac[cs_extends_trans] >>
  `for_range_checked_code cenv lctx ret_ty id typ bound body op1 op2 z = ((),b)` by
    (drule_all compile_stmt_for_range_checked >> metis_tac[]) >>
  `!c lc s t. compile_stmts c lc ret_ty body s = ((),t) ==> cs_extends s t` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends z b` by
    (drule_all for_range_checked_parts >> disch_then strip_assume_tac >>
     first_assum ACCEPT_TAC) >>
  `fn_has_code a z func /\ fn_has_code z b func` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem range_checked_endpoint_intervals_mods:
  stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) a = (cenv',b) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) sa = (scenv',sb) /\
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
  cenv.ce_alloca_locals /\ gas_shadow_state a sa /\
  fn_has_code a b func /\ fn_has_code sa sb shadow_func ==>
  cenv' = cenv /\ scenv' = gas_shadow_env T cenv /\
  ?op1 op2 m z sm sz.
    lower_value compile_expr cenv typ e1 a = (op1,m) /\
    lower_value compile_expr cenv typ e2 m = (op2,z) /\
    lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) sa = (op1,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) sm = (op2,sz) /\
    gas_shadow_state m sm /\ gas_shadow_state z sz /\
    fn_has_code a m func /\ fn_has_code m z func /\ fn_has_code z b func /\
    fn_has_code sa sm shadow_func /\ fn_has_code sm sz shadow_func /\ fn_has_code sz sb shadow_func
Proof
  pure_rewrite_tac[range_full_outer_env] >> strip_tac >>
  namedCases_on `lower_value compile_expr cenv typ e1 a` ["op1 m"] >>
  namedCases_on `lower_value compile_expr cenv typ e2 m` ["op2 z"] >>
  namedCases_on `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) sa`
    ["sop1 sm"] >>
  `sop1 = op1 /\ gas_shadow_state m sm` by
    (irule gas_shadow_step >> rpt (goal_assum (drule_at Any)) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  namedCases_on `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) sm`
    ["sop2 sz"] >>
  `sop2 = op2 /\ gas_shadow_state z sz` by
    (irule gas_shadow_step >> rpt (goal_assum (drule_at Any)) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `!e a i. gas_shadow_expr e = Literal a (IntL i) ==> e = Literal a (IntL i)` by
    (Cases >> simp[gas_shadow_expr_def]) >>
  `~(?a1 n1 a2 n2. gas_shadow_expr e1 = Literal a1 (IntL n1) /\
                     gas_shadow_expr e2 = Literal a2 (IntL n2))` by metis_tac[] >>
  `(gas_shadow_env T cenv).ce_alloca_locals` by simp[gas_shadow_env_def] >>
  qpat_assum `compile_stmt cenv _ _ _ a = _`
    (mp_then (Pos hd) (drule_all_then strip_assume_tac) range_checked_endpoint_intervals) >>
  qpat_assum `compile_stmt (gas_shadow_env T cenv) _ _ _ sa = _`
    (mp_then (Pos hd) (drule_all_then strip_assume_tac) range_checked_endpoint_intervals) >>
  reverse (rpt (conj_tac >- first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`op1`,`op2`,`m`,`z`,`sm`,`sz`] >> simp[]
QED

Theorem range_first_operand_kept_mods:
  eval_operand op1 t1 = SOME w /\
  (!x. op1 = Var x ==> not_fresh_at m x) /\
  (!l. op1 <> Label l) /\
  expr_post_mods H ctx func cenv cx e2 es1 m z t1 es2 v2 op2 t2 ==>
  eval_operand op1 t2 = SOME w
Proof
  strip_tac >> irule eval_operand_frame >> simp[] >> qexistsl_tac [`m`,`t1`] >>
  fs[expr_post_mods_def, expr_post_def]
QED

Theorem range_body_for_callback_mods:
  (!tenv s tyv t s1 vs t1 s2 u t2.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s =
       (INL tyv,t) /\
     eval_iterator cx (Range e1 e2) s1 = (INL vs,t1) /\
     check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 =
       (INL u,t2) ==>
     body_for_full_ok_mods mods exps cx tyv id body vs) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e1) (read_result cx) es = (INL (IntV n1),es1) /\
  bind (eval_expr cx e2) (read_result cx) es1 = (INL (IntV n2),es2) /\
  n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) <> 0 ==>
  body_stmts_full_ok_mods mods exps cx body
Proof
  strip_tac >> drule_all_then assume_tac range_iterator_success_mods >>
  `?r rs. GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) = r::rs` by
    (Cases_on `Num (n2 - n1)` >> fs[GENLIST_CONS]) >>
  `compatible_bound (Dynamic bound) (LENGTH (r::rs))` by
    (pop_assum (SUBST1_TAC o SYM) >>
     simp[vyperValueTheory.compatible_bound_def]) >>
  `?v. r = Value v` by
    (qpat_assum `GENLIST _ _ = r::rs` mp_tac >>
     Cases_on `Num (n2 - n1)` >> gvs[GENLIST_CONS]) >>
  gvs[] >> irule for_body_callback_mods >>
  rpt (goal_assum (drule_at Any)) >> simp[read_result_def, return_def] >>
  qexistsl_tac [`id`,`bound`] >> simp[] >> first_assum ACCEPT_TAC
QED
