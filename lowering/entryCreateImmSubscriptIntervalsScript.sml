(* Physical intervals of an immutable subscript: base, index, array suffix. *)
Theory entryCreateImmSubscriptIntervals
Ancestors
  targetSubscriptContinuation entryCreateStmtUpdateCode createSizeOperandCode
  entryCreateIntervalLayout entryCreateNativeFirstExit entryCreateRegionLift
  entryCreateCompletedCut entryCreatePathScope entryCreateFocusSpec
  gasExemptCert vyperStorageTrace fragGasOriginPtrExec
  fragExec createSizeCutRegion createSizeCutCode list arithmetic pair
  compileEnv exprLoweringProps createSizePrefixReplay abiEncoderProps bodyFullIfExpReach
  entryCreateOperandReplay vyperStorageFootprint vyperState vyperInterpreter
  createExprSizeExitDefs fragGasOriginPtr gasSummary gasOutcomeFull

Theorem immutable_array_code[local]:
  create_cut_code {} a (SND (compile_array_subscript p i dyn cnt ws sz signed
    (compile_ptr_load ctor imm loc) a))
Proof
  irule update_array_subscript_cut >> simp[]
QED

Theorem immutable_subscript_code[local]:
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  rb = (baseop,SOME loc,SOME (ValPT (ArrayT ety bd))) /\
  fn_has_code sa sb f /\ create_layout sa sb ==>
  create_cut_code {} sa sm /\ create_cut_code {} sm sn /\
  create_cut_code {} sn sb /\ fn_has_code sa sm f /\
  fn_has_code sm sn f /\ fn_has_code sn sb f /\
  fn_has_code sm sb f /\ create_layout sm sb
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    (irule target_subscript_compile_intervals >> simp[] >> metis_tac[]) >>
  drule_all target_subscript_interval_code >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by fs[ci_mono_def] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sb f` by metis_tac[fn_has_code_split] >>
  `create_layout sm sb` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  conj_tac >- metis_tac[update_target_ptr_cut,SND] >>
  conj_tac >- metis_tac[create_operand_cut_code,SND] >>
  fs[target_subscript_suffix_array] >>
  metis_tac[immutable_array_code,SND]
QED

Theorem immutable_right_prefix[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix m b E C f u marks t ==>
  create_expr_prefix a b E C f u marks t
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >> simp[create_prefix_step_def,frag_ids_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem immutable_right_scope[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E C f s left u /\
  create_operand_full_scope m b E C f u right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac
  >- metis_tac[immutable_right_prefix,create_expr_prefix_append] >>
  rename1 `create_expr_prefix m b E C f u front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[immutable_right_prefix,create_expr_prefix_append] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem immutable_right_focus[local]:
  a.cs_next_id <= m.cs_next_id /\ body_inv tops C ce cx /\
  MEM f C.ctx_functions /\ create_cut_code {} m b /\ fn_has_code m b f /\
  create_operand_at m u /\ create_expr_prefix a b E C f s left u /\
  create_operand_focus_scope m b E C f u marks ==>
  create_operand_focus_scope a b E C f s (left ++ marks)
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix m b E C f u front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[immutable_right_prefix,create_expr_prefix_append] >>
  qexistsl_tac [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
  `create_cut_region m b u` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> rpt strip_tac >>
  qpat_assum `create_prefix_step a b E C f stop _ _`
    (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
  qpat_assum `!right v. create_prefix_step m b E C f stop right v ==> _` irule >>
  qexists_tac `v` >> irule (cj 1 operand_cut_region_edge) >>
  qpat_assum `gas_origin_edge F E C f stop right (OK v)` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem immutable_interval_embeddings[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_operand_at a s /\
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a m f /\ fn_has_code m b f /\ create_layout a b ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                     create_operand_full_scope m b E C f t right r ==>
                     create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
   m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  conj_tac >- metis_tac[create_left_focus_lift_at] >>
  conj_tac >- metis_tac[create_left_terminal_lift_at] >>
  conj_tac
  >- (rpt strip_tac >> irule immutable_right_focus >>
      simp[] >> conj_tac >- metis_tac[] >> qexistsl_tac [`m`,`t`] >>
      qpat_assum `create_operand_full_scope a m _ _ _ s left (OK t)`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
      simp[create_operand_at_def] >> metis_tac[create_left_prefix_lift_at]) >>
  rpt strip_tac >> irule immutable_right_scope >>
  qexistsl_tac [`m`,`t`] >> simp[] >>
  qpat_assum `create_operand_full_scope a m _ _ _ s left (OK t)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
  metis_tac[create_left_prefix_lift_at]
QED

(* Universally quantified interfaces of the two shared bind theorems. The
   argument types, rather than a common success type, select each instance. *)
Definition immutable_scoped_bind_law_def:
  immutable_scoped_bind_law (:'a) (:'b) <=>
  !DF lo E C f PG tops cx st0 a m b source next es s G tn P Q R.
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
      (source : evaluation_state -> 'a evaluation_result) (es,s,G,tn) P
      (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    (!left res mid G1 tn1 t.
       (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
          (res,mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
       create_operand_full_scope a m E C f s left (OK t) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
         P H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,E,C,f,PG)
           (s,G,tn) left (OK t,G1,tn1)) ==>
       ?v. res = INL v /\ scoped_operand_outcome (DF,lo,E,C,f,PG)
           tops cx st0 m b ((next : 'a -> evaluation_state -> 'b evaluation_result) v)
           (mid,t,G1,tn1) Q R) /\
    storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
    (!marks err ee leaf finish.
       gas_exempt_cert T tops (C,f) (ignore_bind source (return ()))
         (es,s) marks (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
         (es,s) marks (err,ee) (leaf,finish)) /\
    (!left v mid t right err ee leaf finish.
       gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
       gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
         (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
         (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
    (!marks. create_operand_focus_scope a m E C f s marks ==>
             create_operand_focus_scope a b E C f s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
               create_operand_full_scope a b E C f s marks r) /\
    (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                    create_operand_focus_scope m b E C f t right ==>
                    create_operand_focus_scope a b E C f s (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                      create_operand_full_scope m b E C f t right r ==>
                      create_operand_full_scope a b E C f s (left ++ right) r) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
      (bind source next) (es,s,G,tn) Q R
End

Definition immutable_replay_bind_law_def:
  immutable_replay_bind_law (:'a) (:'b) <=>
  !a m b E C f s tops cx st0 source DF lo PG es G tn Q next.
    (!p d k before hit after.
      create_interior_visit a b E C f (p,d,k) s (before,hit,after) ==>
      create_interior_visit a m E C f (p,d,k) s (before,hit,after) \/
      ?t d1 k1 front back.
        before = front ++ back /\ create_operand_at m t /\
        create_expr_prefix a m E C f s (create_cut_marks E front) t /\
        create_interior_visit m b E C f (p,d1,k1) t (back,hit,after)) /\
    ~s.vs_halted /\
    create_operand_cut a m E C f tops cx st0
      (source : evaluation_state -> 'a evaluation_result) (es,s) /\
    gas_completed_operand (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn) Q /\
    (!H r mid G' tn' t. Q H r mid G' tn' t ==> ?v. r = INL v) /\
    (!v. storage_trace_frame ((next : 'a -> evaluation_state -> 'b evaluation_result) v)) /\
    (!H0 front v mid G' tn' t.
      valid_horizon cx st0 H0 mid.storage_trace /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn)
          (create_cut_marks E front) (OK t,G',tn') /\
        Q H (INL v) (mid with gas_obs := []) G' tn' t) ==>
      create_operand_cut m b E C f tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
    create_operand_cut a b E C f tops cx st0 (bind source next) (es,s)
End

(* This normal handoff holds at the selected exit with one pair of ghosts
   for all valid horizons. The source equation belongs to that witness. *)
Definition immutable_subscript_return_def:
  immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
    P left v (mid,t,G1,tn1) <=>
    (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    create_operand_at m t /\ ~t.vs_halted /\
    create_expr_prefix a m E C f s left t /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H v mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,E,C,f,PG)
        (s,G,tn) left (OK t,G1,tn1))
End

Theorem immutable_return_completed[local]:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t) R ==>
  gas_completed_operand (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
    (\H res mid G1 tn1 t. ?v left. res = INL v /\
      immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
        P left v (mid,t,G1,tn1))
Proof
  strip_tac >> irule scoped_outcome_completed_operand >> simp[] >>
  qexists_tac `R` >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[scoped_operand_outcome_def]) >>
  simp[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >> qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> gen_tac >> strip_tac >>
      first_assum (drule_then strip_assume_tac) >> gvs[exit_result_def] >>
      qexists_tac `marks` >>
      simp[immutable_subscript_return_def,create_operand_at_def] >>
      fs[create_operand_full_scope_def] >>
      first_x_assum drule >> strip_tac >>
      drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  simp[]
QED

Theorem immutable_outcome_normalize[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
    P R ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
    (\H res ee G1 tn1 t. P H res ee G1 tn1 t /\ ee.gas_obs = []) R
Proof
  simp[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >> qexists_tac `marks` >>
  fs[]
QED

Definition immutable_subscript_bind_certs_def:
  immutable_subscript_bind_certs tops C f source next es s <=>
    (!marks err ee leaf finish.
       gas_exempt_cert T tops (C,f) (ignore_bind source (return ()))
         (es,s) marks (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
         (es,s) marks (err,ee) (leaf,finish)) /\
    (!left v mid t right err ee leaf finish.
       gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
       gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
         (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
         (es,s) (left ++ right) (err,ee) (leaf,finish))
End

Theorem immutable_subscript_bind_certs_places[local,simp]:
  immutable_subscript_bind_certs tops C f
    (source : evaluation_state -> place evaluation_result) next es s
Proof
  rw[immutable_subscript_bind_certs_def] >>
  rewrite_tac[ignore_bind_def,bind_assoc]
  >- (irule gas_exempt_cert_error_place >> simp[]) >>
  irule gas_exempt_cert_bind_place >> qexistsl_tac [`mid`,`t`,`v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem immutable_subscript_bind_certs_values[local,simp]:
  immutable_subscript_bind_certs tops C f
    (source : evaluation_state -> value evaluation_result) next es s
Proof
  rw[immutable_subscript_bind_certs_def] >>
  rewrite_tac[ignore_bind_def,bind_assoc]
  >- (irule gas_exempt_cert_error_value >> simp[]) >>
  irule gas_exempt_cert_bind_value >> qexistsl_tac [`mid`,`t`,`v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem immutable_bind_at_interval[local]:
  immutable_scoped_bind_law (:'a) (:'b) /\ immutable_replay_bind_law (:'a) (:'b) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_operand_at a s /\ ~s.vs_halted /\
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a m f /\ fn_has_code m b f /\ create_layout a b /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  immutable_subscript_bind_certs tops C f source next es s /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (source : evaluation_state -> 'a evaluation_result) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  create_operand_cut a m E C f tops cx st0 source (es,s) /\
  (!left v mid t G1 tn1.
    immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
      P left v (mid,t,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      ((next : 'a -> evaluation_state -> 'b evaluation_result) v) (mid,t,G1,tn1) Q R /\
    create_operand_cut m b E C f tops cx st0 (next v) (mid,t)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R /\
  create_operand_cut a b E C f tops cx st0 (bind source next) (es,s)
Proof
  strip_tac >> conj_tac
  >- (drule_all immutable_interval_embeddings >> strip_tac >>
      drule immutable_outcome_normalize >> strip_tac >>
      qpat_x_assum `immutable_scoped_bind_law _ _`
        (irule o REWRITE_RULE[immutable_scoped_bind_law_def]) >>
      qpat_x_assum `immutable_subscript_bind_certs _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[immutable_subscript_bind_certs_def]) >>
      simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`\H res ee G1 tn1 t. (?v. res = INL v /\ P H v ee G1 tn1 t) /\ ee.gas_obs = []`,`m`] >>
      qpat_x_assum `!explicit. (!marks. create_operand_focus_scope _ _ explicit _ _ _ marks ==> _) /\ _`
        (qspec_then `E` strip_assume_tac) >>
      RULE_ASSUM_TAC BETA_RULE >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >> gvs[] >>
      `immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
         P left v (mid,t,G1,tn1)` by
        (simp[immutable_subscript_return_def] >> rpt conj_tac
         >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
               (drule_then strip_assume_tac) >>
             drule gas_origin_ptr_path_exec >> simp[exit_result_def])
         >- fs[create_operand_full_scope_def] >> metis_tac[]) >>
      metis_tac[]) >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  drule_all immutable_return_completed >> strip_tac >>
  qpat_x_assum `immutable_replay_bind_law _ _`
    (irule o REWRITE_RULE[immutable_replay_bind_law_def]) >>
  simp[] >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> metis_tac[]
QED

Theorem immutable_subscript_selected_binds:
  immutable_scoped_bind_law (:place) (:place) /\
  immutable_scoped_bind_law (:value) (:place) /\
  immutable_replay_bind_law (:place) (:place) /\
  immutable_replay_bind_law (:value) (:place) /\
  body_inv tops C cenv cx /\ MEM f C.ctx_functions /\
  create_operand_at sa s /\ ~s.vs_halted /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  rb = (baseop,SOME loc,SOME (ValPT (ArrayT ety bd))) /\
  fn_has_code sa sb f /\ create_layout sa sb /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sm
    (eval_target_place cx bt) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?p. res = INL p /\ P H p ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  create_operand_cut sa sm E C f tops cx st0 (eval_target_place cx bt) (es,s) /\
  (!left p mid t G1 tn1.
    immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 sa sm
      (eval_target_place cx bt) (es,s,G,tn) P left p (mid,t,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sm sn
      (bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)
      (\H res ee G2 tn2 u. ?v. res = INL v /\ Idx p mid t G1 tn1 H v ee G2 tn2 u)
      (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    create_operand_cut sm sn E C f tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (mid,t) /\
    (!right v mid2 u G2 tn2.
      immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 sm sn
        (bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)
        (Idx p mid t G1 tn1) right v (mid2,u,G2,tn2) ==>
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sn sb
        (bind (extend_place cx (PlaceR p) (ValueSubscript v)) get_place)
        (mid2,u,G2,tn2) Q R /\
      create_operand_cut sn sb E C f tops cx st0
        (bind (extend_place cx (PlaceR p) (ValueSubscript v)) get_place) (mid2,u))) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sb
    (bind (eval_target_place cx bt)
      (\p. bind (bind (eval_expr cx e) (read_result cx))
         (\v. bind (extend_place cx (PlaceR p) (ValueSubscript v)) get_place)))
    (es,s,G,tn) Q R /\
  create_operand_cut sa sb E C f tops cx st0
    (bind (eval_target_place cx bt)
      (\p. bind (bind (eval_expr cx e) (read_result cx))
         (\v. bind (extend_place cx (PlaceR p) (ValueSubscript v)) get_place))) (es,s)
Proof
  strip_tac >> drule_all immutable_subscript_code >> strip_tac >>
  `create_cut_code {} sm sb` by metis_tac[create_cut_code_join] >>
  irule immutable_bind_at_interval >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_get_place,
       storage_trace_frame_extend_place] >>
  conj_tac >- metis_tac[] >> qexistsl_tac [`P`,`sm`] >> simp[] >>
  qx_genl_tac [`left`,`p`,`mid`,`t`,`G1`,`tn1`] >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qpat_assum `immutable_subscript_return _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[immutable_subscript_return_def]) >>
  irule immutable_bind_at_interval >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_get_place,
       storage_trace_frame_extend_place] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`Idx p mid t G1 tn1`,`sn`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem create_selected_bind_at_interval:
  immutable_scoped_bind_law (:'a) (:'b) /\ immutable_replay_bind_law (:'a) (:'b) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_operand_at a s /\ ~s.vs_halted /\
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a m f /\ fn_has_code m b f /\ create_layout a b /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  immutable_subscript_bind_certs tops C f source next es s /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (source : evaluation_state -> 'a evaluation_result) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  create_operand_cut a m E C f tops cx st0 source (es,s) /\
  (!left v mid t G1 tn1.
    immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
      P left v (mid,t,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      ((next : 'a -> evaluation_state -> 'b evaluation_result) v) (mid,t,G1,tn1) Q R /\
    create_operand_cut m b E C f tops cx st0 (next v) (mid,t)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R /\
  create_operand_cut a b E C f tops cx st0 (bind source next) (es,s)
Proof
  ACCEPT_TAC immutable_bind_at_interval
QED
