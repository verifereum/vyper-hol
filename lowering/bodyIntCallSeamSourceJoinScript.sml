(* Typed source binding at a staged internal-call boundary. *)
Theory bodyIntCallSeamSourceJoin
Ancestors
  bodyIntCallHeldArgs bodyIntCallStageDescriptors bodyIntCallSeamPrefixSupport
  vyperTypeBindArguments gasOutcome gasSummary stmtSimDeclGas
  fragGasMode fragGasPath gasExemptCert vyperState vyperInterpreter
  bodyIntCallSourceFrame list pair
Libs
  monadsyntax

Theorem intcall_staged_values_typed:
  intcall_held_args ce cx a sm es s H /\
  LENGTH flags = LENGTH H /\
  LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
    ty' = ty /\ flag' = flag /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D ==>
  EVERY (\(ty,tv,v,flag,op). value_has_type tv v) D
Proof
  strip_tac >> simp[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
  `LENGTH D = LENGTH H` by gvs[LIST_REL_EL_EQN] >>
  `i < LENGTH H` by simp[] >>
  `MEM (EL i H) H` by simp[EL_MEM] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[EL_ZIP] >>
  qmatch_goalsub_abbrev_tac `f hd fd dd` >>
  PairCases_on `hd` >> PairCases_on `dd` >>
  simp[Abbr `f`] >> strip_tac >> gvs[] >>
  drule_all intcall_held_args_member >> strip_tac >>
  metis_tac[]
QED

Theorem intcall_staged_bind_arguments:
  MAP (\(ty,tv,v,flag,op). ty) D = MAP SND args /\
  EVERY (\(ty,tv,v,flag,op).
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v) D ==>
  ?penv. bind_arguments tenv args (MAP (\(ty,tv,v,flag,op). v) D) = SOME penv
Proof
  strip_tac >> irule bind_arguments_succeeds_stmt >>
  `LENGTH args = LENGTH D` by metis_tac[LENGTH_MAP] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `EVERY _ D` mp_tac >> simp[EVERY_EL] >>
  disch_then (qspec_then `i` mp_tac) >>
  qpat_x_assum `MAP _ D = _` (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP] >> qabbrev_tac `dd = EL i D` >>
  PairCases_on `dd` >> simp[] >>
  metis_tac[]
QED

Theorem intcall_admin_unit_prefix:
  ~s.vs_halted /\
  (!gs. (a : evaluation_state -> unit evaluation_result)
     (es with gas_obs := gs) = (INL (),mid with gas_obs := gs)) /\
  gas_outcome F tops (ctx,func) next (mid,s) Q R ==>
  gas_outcome F tops (ctx,func) (bind a (\u. next)) (es,s) Q R
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, bind_def]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ _ (leaf,target)` >>
  disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`target`] >>
  `gas_marked_exec F (ctx,func) a (es,s) [] (INL ()) mid (OK s)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_rules) >> simp[]) >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  simp[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >>
  disch_then irule >> fs[ignore_bind_def]
QED

Theorem intcall_push_outcome:
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (k (cx with stk updated_by CONS id))
    (es with scopes := [penv],s) Q R ==>
  gas_outcome F tops (ctx,func) (bind (push_function id penv cx) k) (es,s) Q R
Proof
  strip_tac >>
  `bind (push_function id penv cx) k =
   bind (set_scopes [penv]) (\u. k (cx with stk updated_by CONS id))` by
    simp[FUN_EQ_THM, bind_def, push_function_def, set_scopes_def, return_def] >>
  simp[] >> irule intcall_admin_unit_prefix >> simp[] >>
  qexists_tac `es with scopes := [penv]` >>
  simp[set_scopes_def, return_def]
QED

Theorem intcall_read_bind_push_outcome:
  ~s.vs_halted /\
  read_results cx raws es = (INL vals,es) /\
  bind_arguments (get_tenv cx) args vals = SOME penv /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  gas_outcome F tops (ctx,func)
    (k es.scopes rtv (cx with stk updated_by CONS id))
    (es with scopes := [penv],s) Q R ==>
  gas_outcome F tops (ctx,func)
    (do prev <- get_scopes;
        vs <- read_results cx raws;
        env <- lift_option_type (bind_arguments (get_tenv cx) args vs)
          "IntCall bind_arguments";
        rt <- lift_option_type (evaluate_type (get_tenv cx) ret)
          "IntCall eval ret";
        lock_if_nr cx F (is_view_mut mut);
        cxf <- push_function id env cx;
        k prev rt cxf od) (es,s) Q R
Proof
  strip_tac >>
  `!gs. read_results cx raws (es with gas_obs := gs) =
    (INL vals,es with gas_obs := gs)` by
    (gen_tac >>
     qspecl_then [`raws`,`es`,`es.outcomes`,`gs`] mp_tac read_results_outcomes >>
     Cases_on `es` >> simp[evaluation_state_fn_updates]) >>
  `gas_outcome F tops (ctx,func)
     (bind (push_function id penv cx) (k es.scopes rtv)) (es,s) Q R` by
    (irule intcall_push_outcome >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ (bind _ _) _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, get_scopes_def,
        bind_def, return_def, lift_option_type_def, lock_if_nr_def, ignore_bind_def]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ _ (leaf,target)` >>
  disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`target`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  `gas_marked_exec F (ctx,func) (read_results cx raws) (es,s)
    [] (INL vals) es (OK s)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_rules) >> simp[]) >>
  drule gas_exempt_cert_bind_values >> simp[] >> disch_then irule >>
  simp[lift_option_type_def, bind_return, lock_if_nr_def, ignore_bind_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[ignore_bind_def, bind_assoc]
QED
