(* The bad-storage and exempt arms of deploy_unit_execution_correct_at
 * (deployUnitExecution) at the joint body induction's marks: the body's
 * gas_outcome_full arm at the body start (s0, G0, tn0), prefixed with
 * deploy_ctor_entry_joint's zero-mark entry path, and the constructor body's
 * run carried through load_contract_trace.
 * TOP-LEVEL: deploy_ctor_bad_storage_arm, deploy_ctor_exempt_arm,
 * deploy_ctor_source_trace.
 *)
Theory ctorDeployLoweringArms
Ancestors
  ctorDeployLoweringEntrySelection ctorDeployLoweringSource
  ctorDeployLoweringDefs
  ctorDeployDefs e2eDeployDefs gasStorage gasExemptCert fragGasOriginPtr
  vyperStorageTrace vyperStorageFootprint vyperTypeConstantFold vyperInterpreter
  vyperTypeContract vyperTypeConstantCells vyperTypeContractStaticMaps
  vyperTypeExprSoundness vyperContext
  vyperState evalNoHalt list alist

val _ = Parse.hide "body";
val _ = Parse.hide "finish";

Theorem storage_trace_domain_nil[local]:
  storage_trace_domain cx st []
Proof
  EVAL_TAC >> simp[]
QED

Theorem deploy_ctor_arm_selection[local]:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_code tops rp runtime_bc unit
    (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
  nr' = F /\ body' = body
Proof
  strip_tac >>
  `supported_program tops` by fs[ctorDeployDefsTheory.deploy_source_ok_def] >>
  drule_all deploy_ctor_entry_selection_agrees >> strip_tac >>
  `nr' = F` by
    (gvs[deploy_state_rel_def, constructor_args_encode_def,
         deploy_ctor_start_def]) >>
  simp[]
QED

(* The deployment guard is the finite storage guard of the load trace. *)
Theorem deploy_storage_ok_domain:
  deploy_storage_ok tops am tx os gs ==>
  storage_trace_domain (deploy_evaluation_context tops am tx)
    (initial_state am []) (deploy_storage_trace (SOME os) gs am tx tops)
Proof
  simp[deploy_storage_ok_def, storage_trace_domain_def, valid_horizon_def,
       storage_trace_horizon_def, storage_observations_ok_def, EVERY_MEM]
QED

(* With no reentrancy lock, the constructor's start observes no storage. *)
Theorem deploy_ctor_start_storage_trace:
  deploy_ctor_start tops am tx (mut, F, body, am_c, es0) ==>
  es0.storage_trace = []
Proof
  simp[deploy_ctor_start_def] >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[ignore_bind_def, bind_def, return_def, send_call_value_def,
       transfer_value_def, check_def, assert_def, raise_def,
       get_accounts_def, update_accounts_def, lift_option_def, COND_RATOR,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[initial_state_def, return_def, raise_def]
QED

(* The trace twins of vyperTypeConstantFold's constants_fold_module_constants_env,
   constants_fold_evaluate_module_constants and
   check_contract_evaluate_all_constants: a checked contract's constant
   expressions return their initial state, so constant evaluation observes
   no storage.  Candidates for vyperTypeConstantFold. *)
Theorem constants_fold_module_constants_env_trace:
  !mods imms src ts acc.
  !cenv cx am full artifact mode layouts addr.
    constants_fold_module mods imms src ts acc = SOME cenv /\
    check_contract mode (layouts : ('checker_addr, ((num option # string), num) alist # ((num option # string), num) alist) alist)
      addr mods = SOME artifact /\
    ALOOKUP mods src = SOME full /\ EVERY (\tl. MEM tl full) ts /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP am.immutables cx.txn.target = SOME imms /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
    constant_fmap_declared_typed (type_env_all_modules mods) full acc ==>
    constants_env_trace cx am cx.txn.target src ts acc = (SOME cenv, [])
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def, constants_env_trace_def] >>
  gvs[AllCaseEqs()]
  >>~- ([`constant_value mods (merge_constant_imms src acc imms) e = SOME v`],
    drule_all check_contract_toplevel_decl_MEM_checked >>
    simp[check_toplevel_decl_def] >> strip_tac >>
    `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
    `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods
       (merge_constants cx.txn.target src acc am)` by
      (irule merge_constants_preserves_constant_cells_typed >> metis_tac[]) >>
    `ALOOKUP (merge_constants cx.txn.target src acc am).immutables cx.txn.target =
       SOME (merge_constant_imms src acc imms)` by simp[merge_constants_immutables] >>
    `constant_machine_immutables
       (merge_constants cx.txn.target src acc am) cx.txn.target =
       merge_constant_imms src acc imms` by
      simp[constant_machine_immutables_def] >>
    drule_all (cj 1 constant_value_eval_expr_checked) >>
    disch_then (qspec_then `[FEMPTY]` strip_assume_tac) >>
    `value_has_type tv v` by gvs[value_runtime_typed_def, artifact_env_def] >>
    `constant_fmap_declared_typed (type_env_all_modules mods) full
       (acc |+ (id,(tv,v)))` by
      (irule constant_fmap_declared_typed_update >> metis_tac[]) >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac >>
    simp[get_tenv_def, bind_def] >> simp[initial_state_def]) >>
  metis_tac[]
QED

Theorem constants_fold_evaluate_module_constants_trace:
  !rest imms am imms' cx artifact mode layouts addr.
    constants_fold mods imms rest = SOME imms' /\
    check_contract mode (layouts : ('checker_addr, ((num option # string), num) alist # ((num option # string), num) alist) alist)
      addr mods = SOME artifact /\
    EVERY (\m. MEM m mods) rest /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP am.immutables cx.txn.target = SOME imms /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
    ?am_c.
      evaluate_module_constants_trace cx am cx.txn.target rest = (SOME am_c, [])
Proof
  Induct >- simp[constants_fold_def, evaluate_module_constants_trace_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  rw[constants_fold_def] >> gvs[AllCaseEqs()] >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `ALOOKUP mods h0 = SOME h1` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
  `constants_env_trace (set_current_module cx h0) am cx.txn.target h0 h1 FEMPTY =
     (SOME cenv, []) /\
   constant_fmap_declared_typed (type_env_all_modules mods) h1 cenv` by
    (conj_tac
     >- (drule constants_fold_module_constants_env_trace >>
         disch_then (qspec_then `set_current_module cx h0` mp_tac) >>
         simp[set_current_module_def, EVERY_MEM] >> disch_then drule_all >> simp[]) >>
     drule constants_fold_module_constants_env >>
     disch_then (qspec_then `set_current_module cx h0` mp_tac) >>
     simp[set_current_module_def, EVERY_MEM] >> disch_then drule_all >> simp[]) >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods
     (merge_constants cx.txn.target h0 cenv am)` by
    (irule merge_constants_preserves_constant_cells_typed >> metis_tac[]) >>
  `ALOOKUP (merge_constants cx.txn.target h0 cenv am).immutables cx.txn.target =
     SOME (merge_constant_imms h0 cenv imms)` by simp[merge_constants_immutables] >>
  first_x_assum drule_all >> strip_tac >>
  simp[evaluate_module_constants_trace_def]
QED

Theorem check_contract_evaluate_all_constants_trace:
  check_contract in_deploy layouts addr mods = SOME art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP am.immutables cx.txn.target = SOME imms ==>
  ?am_c. evaluate_module_constants_trace cx am cx.txn.target
           (constants_order mods) = (SOME am_c, [])
Proof
  strip_tac >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> rw[]) >>
  gvs[contract_constants_ok_def, optionTheory.IS_SOME_EXISTS] >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am` by
    (rw[deployment_constant_cells_typed_def] >>
     drule_all checked_initial_immutables_constant_absent >> gvs[]) >>
  drule_at (Pat `check_contract _ _ _ _ = _`)
    constants_fold_evaluate_module_constants_trace >>
  disch_then (qspec_then `constants_order mods` mp_tac) >>
  simp[EVERY_MEM, MEM_constants_order] >> disch_then drule_all >> metis_tac[]
QED

(* Under deploy_source_ok the constant evaluation that load_contract_trace
   runs before the constructor observes no storage. Its FST is
   evaluate_all_constants by evaluate_module_constants_def. *)
Theorem deploy_constants_trace_nil:
  deploy_source_ok tops am tx /\
  initial_immutables (type_env_all_modules [(NONE, tops)]) [(NONE, tops)] =
    SOME imms ==>
  SND (evaluate_module_constants_trace (deploy_evaluation_context tops am tx)
         (am with <| immutables updated_by CONS (tx.target, imms);
                     exports updated_by CONS (tx.target, []) |>)
         tx.target (constants_order [(NONE, tops)])) = []
Proof
  rpt strip_tac >>
  `(deploy_evaluation_context tops am tx).txn.target = tx.target` by
    simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
  `?am_c. evaluate_module_constants_trace (deploy_evaluation_context tops am tx)
            (am with <| immutables updated_by CONS (tx.target, imms);
                        exports updated_by CONS (tx.target, []) |>)
            (deploy_evaluation_context tops am tx).txn.target
            (constants_order [(NONE, tops)]) = (SOME am_c, [])` by
    (irule (check_contract_evaluate_all_constants_trace |>
       Q.GENL [`in_deploy`, `layouts`, `addr`] |>
       Q.ISPECL [`T`, `am.layouts`, `tx.target`]) >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
     gvs[ctorDeployDefsTheory.deploy_source_ok_def,
         deploy_typing_ok_constants_ready] >>
     metis_tac[]) >>
  gvs[]
QED

(* deploy_ctor_finish reads no gas observations. *)
Theorem deploy_ctor_finish_gas_obs:
  deploy_ctor_finish tops tx cx nr mut am_c res (st with gas_obs := g) =
  deploy_ctor_finish tops tx cx nr mut am_c res st
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[deploy_ctor_finish_def, unlock_if_nr_def,
    release_nonreentrant_lock_def, update_transient_def,
    ignore_bind_def, bind_def, record_storage_event_def,
    return_def, raise_def, abstract_machine_from_state_def] >>
  Cases_on `mut` >>
  simp[bind_def, get_transient_storage_def, update_transient_def,
    record_storage_event_def, return_def, abstract_machine_from_state_def]
QED

(* The trace twin of deploy_ctor_source_run, at any call-outcome oracle:
   load_contract_trace is deploy_ctor_finish of the constructor body's run
   from deploy_ctor_start, and its trace is the body's: the constant
   evaluation before it observes no storage. *)
Theorem deploy_ctor_source_trace:
  !tops am tx mut body am_c es0.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, F, body, am_c, es0) ==>
    !orc gobs res st.
      eval_stmts (deploy_evaluation_context tops am tx) body
        (es0 with <| gas_obs := gobs; outcomes := orc |>) = (res, st) ==>
      load_contract_trace orc gobs am tx [(NONE, tops)] [] =
        (deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
           F mut am_c res st,
         st.storage_trace)
Proof
  rpt gen_tac >> strip_tac >>
  `get_module_code (deploy_evaluation_context tops am tx) NONE = SOME tops` by
    simp[deploy_evaluation_context_def, initial_evaluation_context_def,
         vyperContextTheory.get_module_code_def] >>
  qpat_assum `deploy_ctor_start _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_ctor_start_def]) >>
  `?ctr. evaluate_module_constants_trace (deploy_evaluation_context tops am tx)
           (am with <|immutables updated_by CONS (tx.target,imms);
                      exports updated_by CONS (tx.target,[])|>)
           tx.target (constants_order [(NONE,tops)]) = (SOME am_c, ctr)` by
    (qpat_x_assum `evaluate_all_constants _ _ _ _ = _` mp_tac >>
     simp_tac std_ss [evaluate_all_constants_def, evaluate_module_constants_def] >>
     qmatch_goalsub_abbrev_tac `FST constants_pair = SOME am_c` >>
     Cases_on `constants_pair` >> simp[]) >>
  `ctr = []` by
    (drule deploy_constants_trace_nil >>
     disch_then (qspec_then `imms` mp_tac) >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >> rpt strip_tac >>
  `!v. res = INR (ReturnException v) ==> v = NoneV` by
    (rpt strip_tac >> irule deploy_ctor_return_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl [`gobs`, `orc`, `st`] >> gvs[]) >>
  `res <> INR HaltException` by
    (strip_tac >>
     `!s s'. eval_stmts (deploy_evaluation_context tops am tx) body s <>
             (INR HaltException, s')` by
       (rpt gen_tac >> irule deploy_body_no_halt >>
        gvs[ctorDeployDefsTheory.deploy_source_ok_def] >> metis_tac[]) >>
     metis_tac[]) >>
  qabbrev_tac `cx = deploy_evaluation_context tops am tx` >>
  qabbrev_tac `G = ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx F (is_view_mut mut)) (eval_stmts cx body)))` >>
  `G (initial_state am_c [FEMPTY] with
       <|outcomes := orc; requests := []; gas_obs := gobs|>) = (res,st)` by
    (drule deploy_ctor_prefix_transport >>
     disch_then (qspecl_then [`orc`, `gobs`] assume_tac) >>
     gvs[Abbr `G`, ignore_bind_def, bind_def, AllCaseEqs(),
         Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `G (initial_state am_c [FEMPTY] with
       <|outcomes := orc; requests := []; gas_obs := gobs;
         storage_trace := []|>) = (res, st)` by
    (`initial_state am_c [FEMPTY] with
        <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|> =
      initial_state am_c [FEMPTY] with
        <|outcomes := orc; requests := []; gas_obs := gobs|>` by
       simp[initial_state_def] >>
     simp[]) >>
  `deploy_evaluation_context tops
      (am with <|exports updated_by CONS (tx.target,[]);
        immutables updated_by CONS (tx.target,imms)|>) tx = cx /\
   deploy_evaluation_context tops
      (am with <|immutables updated_by CONS (tx.target,imms);
        exports updated_by CONS (tx.target,[])|>) tx = cx /\
   deploy_evaluation_context tops am tx = cx` by
    simp[Abbr `cx`, deploy_evaluation_context_def] >>
  `cx.in_deploy /\ cx.txn = tx with created_in_tx := T` by
    simp[Abbr `cx`, deploy_evaluation_context_def, initial_evaluation_context_def] >>
  `bind (eval_external_defaults cx [])
      (\dflt_vs. case bind_arguments (type_env_all_modules [(NONE,tops)]) args
          (tx.args ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => ignore_bind (set_scopes [env])
          (ignore_bind (lock_if_nr cx F (is_view_mut mut)) (eval_stmts cx body))) =
    ignore_bind (set_scopes [env])
      (ignore_bind (lock_if_nr cx F (is_view_mut mut)) (eval_stmts cx body))` by
    simp[FUN_EQ_THM, bind_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  simp[load_contract_trace_def, call_external_function_trace_def,
       GSYM deploy_evaluation_context_def,
       Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  gvs[] >>
  Cases_on `res`
  >- (Cases_on `x` >>
      simp[deploy_ctor_finish_def, unlock_if_nr_def, return_def]) >>
  rename1 `INR ex` >> Cases_on `ex` >>
  gvs[deploy_ctor_finish_def, unlock_if_nr_def, return_def,
      vyperValueOperationTheory.safe_cast_def]
QED

(* The bad-storage arm: the body's storage failure is the deployment's, and
   the focus from the body start extends back to the unit's entry. *)
Theorem deploy_ctor_bad_storage_arm:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut nr' body' am_c es0 s0 G0 tn0 explicit marks H
   leaf leaf_pg leaf_g leaf_tn finish.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    (!H. valid_horizon (deploy_evaluation_context tops am tx)
           (initial_state am [])
           H (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
         gas_origin_ptr_path
           (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
            dunit.cu_context, func, [])
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                       vs_inst_idx := 0 |>, FEMPTY, entry_taint)
           [] (OK s0, G0, tn0)) /\
    gas_bad_storage_at (deploy_evaluation_context tops am tx)
      (initial_state am [])
      (eval_stmts (deploy_evaluation_context tops am tx) body)
      (es0 with outcomes := SOME vs.vs_outcomes) s0 marks /\
    (storage_trace_domain (deploy_evaluation_context tops am tx)
       (initial_state am [])
       (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
     valid_horizon (deploy_evaluation_context tops am tx)
       (initial_state am [])
       H (es0 with outcomes := SOME vs.vs_outcomes).storage_trace) /\
    gas_origin_ptr_focus
      (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
       dunit.cu_context, func, [])
      (s0, G0, tn0) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish) ==>
    (!tail. ~deploy_storage_ok tops am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail)) /\
      gas_origin_ptr_focus
        (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
         dunit.cu_context, func, [])
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>, FEMPTY, entry_taint)
        marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_arm_selection >> strip_tac >> gvs[] >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `es0.storage_trace = []` by metis_tac[deploy_ctor_start_storage_trace] >>
  `gas_origin_ptr_focus
     (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
      dunit.cu_context, func, [])
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>, FEMPTY, entry_taint)
     ([] ++ marks) (leaf, leaf_pg, leaf_g, leaf_tn, finish)` by
    (irule (cj 2 gas_origin_ptr_focus_rules) >>
     gvs[storage_trace_domain_nil] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`tops`, `am`, `tx`, `mut`, `body`, `am_c`, `es0`]
    deploy_ctor_source_trace) >>
  impl_tac >- simp[] >> strip_tac >>
  fs[] >> rpt strip_tac >>
  qabbrev_tac `gx = gas_explicit marks vs.vs_gas_readings ++ tail` >>
  Cases_on `eval_stmts (deploy_evaluation_context tops am tx) body
              (es0 with <| gas_obs := gx; outcomes := SOME vs.vs_outcomes |>)` >>
  rename1 `_ = (res, st)` >>
  qpat_x_assum `!orc gobs res st. _`
    (qspecl_then [`SOME vs.vs_outcomes`, `gx`, `res`, `st`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  drule deploy_storage_ok_domain >>
  simp[deploy_storage_trace_def] >> strip_tac >>
  qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _`
    (qspec_then `tail` mp_tac o REWRITE_RULE [gas_bad_storage_at_def]) >>
  gvs[Abbr `gx`]
QED

(* The exempt arm: the body's exempt error is the deployment's source
   result, with one trace for every continuation of the readings. *)
Theorem deploy_ctor_exempt_arm:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func mut nr' body' am_c es0 s0 G0 tn0 explicit marks H err ee
   leaf leaf_pg leaf_g leaf_tn finish.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    (!H. valid_horizon (deploy_evaluation_context tops am tx)
           (initial_state am [])
           H (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
         gas_origin_ptr_path
           (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
            dunit.cu_context, func, [])
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                       vs_inst_idx := 0 |>, FEMPTY, entry_taint)
           [] (OK s0, G0, tn0)) /\
    gas_exempt_cert T tops (dunit.cu_context, func)
      (ignore_bind (eval_stmts (deploy_evaluation_context tops am tx) body)
         (return ()))
      (es0 with outcomes := SOME vs.vs_outcomes, s0) marks (err, ee)
      (leaf, finish) /\
    (storage_trace_domain (deploy_evaluation_context tops am tx)
       (initial_state am [])
       (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
     valid_horizon (deploy_evaluation_context tops am tx)
       (initial_state am [])
       H (es0 with outcomes := SOME vs.vs_outcomes).storage_trace) /\
    gas_origin_ptr_focus
      (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
       dunit.cu_context, func, [])
      (s0, G0, tn0) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish) ==>
    ?src obs.
      (!tail. load_contract_trace (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
         [(NONE, tops)] [] = (src, obs)) /\
      deploy_source_exempt tops src /\
      gas_origin_ptr_focus
        (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
         dunit.cu_context, func, [])
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>, FEMPTY, entry_taint)
        marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_arm_selection >> strip_tac >> gvs[] >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `es0.storage_trace = []` by metis_tac[deploy_ctor_start_storage_trace] >>
  `gas_origin_ptr_focus
     (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
      dunit.cu_context, func, [])
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>, FEMPTY, entry_taint)
     ([] ++ marks) (leaf, leaf_pg, leaf_g, leaf_tn, finish)` by
    (irule (cj 2 gas_origin_ptr_focus_rules) >>
     gvs[storage_trace_domain_nil] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`tops`, `am`, `tx`, `mut`, `body`, `am_c`, `es0`]
    deploy_ctor_source_trace) >>
  impl_tac >- simp[] >> strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  `!tail. eval_stmts (deploy_evaluation_context tops am tx) body
            (es0 with <| gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail;
                         outcomes := SOME vs.vs_outcomes |>) =
          (INR (Error err), ee with gas_obs := tail)` by
    (gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def] >>
     Cases_on `eval_stmts (deploy_evaluation_context tops am tx) body
                 (es0 with <| outcomes := SOME vs.vs_outcomes;
                   gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail |>)` >>
     Cases_on `q` >> simp[]) >>
  qexistsl_tac [`INR (Error err)`, `ee.storage_trace`] >>
  fs[deploy_source_exempt_def] >> gen_tac >>
  first_x_assum (qspec_then `tail` assume_tac) >>
  first_x_assum drule >> simp[deploy_ctor_finish_def]
QED
