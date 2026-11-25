(* Find a concrete source expression error in the checked default suffix. *)
Theory groupedRejectSourceError
Ancestors
  runtimeDefaultErrorDescent e2eDefs ptrDiscipline vyperTypeContract list pred_set venomInst venomState
  callRejectMemory[ignore_grammar] compileEnv vyperContext finite_map rich_list words
  gasExemptCert[qualified,ignore_grammar] vyperInterpreter[qualified,ignore_grammar]
  vyperState[qualified,ignore_grammar] vyperValue[qualified,ignore_grammar]
  vyperMisc[qualified,ignore_grammar] vyperValueOperation[qualified,ignore_grammar]
  whitelistCheckerConsts[qualified,ignore_grammar] constSubst[qualified,ignore_grammar]
  exprCallBounds[qualified,ignore_grammar] pair arithmetic relation vyperAST gasContext

val _ = Parse.hide "tops";

Theorem row22_source_no_exempt_if_descent:
  (!tops err mods ds cx st ee.
    unspecified_behaviour_exempt tops err /\
    EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds /\
    (!p c a b. MEM p ds /\ expr_size c < expr_size p /\
      runtime_constant_expr mods c /\ no_sha256_expr c ==>
      eval_expr cx c a <> (INR (Error err),b)) ==>
    eval_exprs cx ds st <> (INR (Error err),ee)) ==>
  !cx mods ds. EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds ==>
    !st ee err. eval_exprs cx ds st = (INR (Error err),ee) ==>
    ~unspecified_behaviour_exempt (cx_tops cx) err
Proof
  disch_then (mk_asm "descent") >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_tac >> strip_tac >>
  `!st ee. eval_exprs cx ds st <> (INR (Error err),ee)` by
    (irule default_eval_error_if_descent >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `mods` >> simp[] >>
     qx_genl_tac [`ds'`,`st'`,`ee'`] >> strip_tac >>
     asm "descent" (qspecl_then [`cx_tops cx`,`err`,`mods`,`ds'`,`cx`,`st'`,`ee'`]
       match_mp_tac) >>
     asm_rewrite_tac[]) >>
  qpat_assum `!st ee. eval_exprs cx ds st <> _`
    (qspecl_then [`st`,`ee`] (fn excluded =>
       qpat_assum `eval_exprs cx ds st = (INR (Error err),ee)`
         (ACCEPT_TAC o MP (NOT_ELIM excluded))))
QED

Theorem grouped_default_bind_error[local]:
  f st <> (INR err,ee) /\ (!x mid. g x mid <> (INR err,ee)) ==>
  vyperState$bind f g st <> (INR err,ee)
Proof
  Cases_on `f st` >> Cases_on `q` >> simp[vyperStateTheory.bind_def]
QED

Theorem grouped_default_list_fold_error[local]:
  (!v a b. read_result cx v a <> (INR (Error err),b)) /\
  (!e a b. MEM e ds ==> eval_expr cx e a <> (INR (Error err),b)) ==>
  !st ee. eval_exprs cx ds st <> (INR (Error err),ee)
Proof
  Induct_on `ds` >- simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def] >>
  gen_tac >> simp[vyperInterpreterTheory.evaluate_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  disch_then strip_assume_tac >> rpt gen_tac >>
  irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> simp[vyperStateTheory.return_def]
QED

Theorem grouped_default_error_descent_if[local]:
  (!acc ty bt tys vs. runtime_constant_builtin bt \/ constant_builtin bt ==>
     evaluate_builtin cx acc ty bt tys vs <> INR err) /\
  (!tb typ tys vs. constant_type_builtin tb ==>
     evaluate_type_builtin cx tb typ tys vs <> INR err) /\
  (!src id a b. lookup_global cx src id a <> (INR (Error err),b)) /\
  (!v a b. read_result cx v a <> (INR (Error err),b)) /\
  (!v a b. conditional_result cx v a <> (INR (Error err),b)) /\
  (!ty v sub a b. select_result cx ty v sub a <> (INR (Error err),b)) /\
  (!v a b. result_array_length cx v a <> (INR (Error err),b)) /\
  unspecified_behaviour_exempt tops err /\
  EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds /\
  (!p c a b. MEM p ds /\ expr_size c < expr_size p /\
     runtime_constant_expr mods c /\ no_sha256_expr c ==>
     eval_expr cx c a <> (INR (Error err),b)) ==>
  eval_exprs cx ds st <> (INR (Error err),ee)
Proof
  strip_tac >> irule grouped_default_list_fold_error >> simp[] >>
  rpt gen_tac >> disch_tac >>
  `runtime_constant_expr mods e /\ no_sha256_expr e` by
    metis_tac[EVERY_MEM, constSubstTheory.no_sha256_collections] >>
  `!c a b. expr_size c < expr_size e /\ runtime_constant_expr mods c /\
           no_sha256_expr c ==> eval_expr cx c a <> (INR (Error err),b)` by metis_tac[] >>
  qpat_x_assum `!p c a b. _ ==> _` kall_tac >>
  Cases_on `e` >> fs[runtime_constant_expr_def, constSubstTheory.no_sha256_expr_def] >>
  TRY (simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def] >> NO_TAC)
  >~ [`eval_expr _ (TopLevelName _ _) _`]
  >- (rename1 `TopLevelName _ nsid` >> Cases_on `nsid` >>
      simp[Once vyperInterpreterTheory.evaluate_def])
  >> TRY (qmatch_goalsub_rename_tac `eval_expr _ (IfExp _ _ _ _) _` >>
          suspend "ifexp")
  >~ [`eval_expr _ (StructLit _ _ _) _`]
  >- suspend "struct"
  >~ [`eval_expr _ (Subscript _ _ _) _`]
  >- suspend "subscript"
  >~ [`eval_expr _ (Attribute _ _ _) _`]
  >- suspend "attribute"
  >> TRY (qmatch_goalsub_rename_tac `eval_expr _ (Builtin _ _ _) _` >>
          suspend "builtin")
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _`]
  >- suspend "typebuiltin"
QED

Resume grouped_default_error_descent_if[ifexp]:
  markerLib.RESUME_TAC >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperInterpreterTheory.switch_BoolV_def] >>
  irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> simp[COND_RATOR, vyperStateTheory.raise_def, AllCaseEqs()] >>
  fs[unspecified_behaviour_exempt_def]
QED

Resume grouped_default_error_descent_if[struct]:
  rename1 `StructLit ann nsid fs` >> Cases_on `nsid` >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  irule grouped_default_bind_error >> simp[vyperStateTheory.return_def] >>
  irule grouped_default_list_fold_error >> simp[] >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  gvs[constSubstTheory.no_sha256_collections, EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
  `expr_size e < expr_size (StructLit ann (q,r) fs)` by
    (irule exprCallBoundsTheory.expr_struct_field_bound >> metis_tac[]) >>
  fs[expr_size_def] >> metis_tac[pairTheory.SND]
QED

Resume grouped_default_error_descent_if[subscript]:
  simp[Once vyperInterpreterTheory.evaluate_def] >> irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[vyperStateTheory.return_def] >>
      irule grouped_default_bind_error >> simp[vyperStateTheory.return_def]) >>
  rpt gen_tac >> BETA_TAC >> irule grouped_default_bind_error >> simp[] >>
  rpt gen_tac >> irule grouped_default_bind_error >> simp[]
QED

Resume grouped_default_error_descent_if[attribute]:
  simp[Once vyperInterpreterTheory.evaluate_def] >> irule grouped_default_bind_error >> simp[]
QED

Resume grouped_default_error_descent_if[builtin]:
  markerLib.RESUME_TAC >> rename1 `Builtin ann bt args` >>
  (Cases_on `bt = Len` >- suspend "length" >>
   (Cases_on `bt = Env MsgGas` >- suspend "gas") >>
   suspend "ordinary")
QED

Resume grouped_default_error_descent_if[length]:
  markerLib.RESUME_TAC >> gvs[runtime_constant_builtin_def] >> Cases_on `args` >>
  simp[Once vyperInterpreterTheory.evaluate_def, builtin_args_length_ok_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  gvs[constSubstTheory.no_sha256_expr_def, runtime_constant_builtin_def, constant_builtin_def,
      whitelistCheckerConstsTheory.constant_expr_runtime_constant,
      AllCaseEqs(), unspecified_behaviour_exempt_def]
QED

Resume grouped_default_error_descent_if[gas]:
  markerLib.RESUME_TAC >> rename1 `eval_expr _ _ st <> _` >>
  Cases_on `st.gas_obs` >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperInterpreterTheory.next_gas_reading_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  gvs[unspecified_behaviour_exempt_def]
QED

Resume grouped_default_error_descent_if[ordinary]:
  markerLib.RESUME_TAC >>
  `!ct addr. code_slice_source bt args <> SOME (ct,addr)` by
    (simp[vyperInterpreterTheory.code_slice_source_SOME] >> rpt strip_tac >>
     gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
  `~precompile_builtin bt` by
    (Cases_on `bt` >> gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
  `code_slice_source bt args = NONE` by
    (Cases_on `code_slice_source bt args` >> simp[] >> PairCases_on `x` >> gvs[]) >>
  `EVERY (runtime_constant_expr mods) args` by
    (fs[EVERY_MEM] >> metis_tac[whitelistCheckerConstsTheory.constant_expr_runtime_constant]) >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.ignore_bind_def] >>
  irule grouped_default_bind_error >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def, AllCaseEqs()] >>
  (reverse conj_tac >- fs[unspecified_behaviour_exempt_def]) >>
  rpt gen_tac >> BETA_TAC >> irule grouped_default_bind_error >> simp[vyperStateTheory.return_def] >>
  irule grouped_default_bind_error >>
  (reverse conj_tac
   >- (irule grouped_default_list_fold_error >> simp[] >>
       rpt gen_tac >> disch_tac >> first_x_assum irule >>
       fs[EVERY_MEM, constSubstTheory.no_sha256_collections] >>
       drule exprCallBoundsTheory.expr_list_member_bound >> simp[])) >>
  simp[vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  rpt gen_tac >>
  (Cases_on `is_self_codesize bt args`
   >- (qpat_x_assum `unspecified_behaviour_exempt tops err` mp_tac >>
       Cases_on `x`
       >- (simp[evaluate_self_codesize_def, vyperStateTheory.lift_sum_def,
                vyperStateTheory.raise_def, unspecified_behaviour_exempt_def] >>
           rpt strip_tac >> gvs[]) >>
       Cases_on `t` >> Cases_on `h` >>
       simp[evaluate_self_codesize_def, vyperStateTheory.lift_sum_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def,
            unspecified_behaviour_exempt_def] >> rpt strip_tac >> gvs[]) >>
   Cases_on `evaluate_builtin cx mid.accounts ann bt (MAP expr_type args) x` >>
   simp[vyperStateTheory.lift_sum_def, vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
   metis_tac[])
QED

Resume grouped_default_error_descent_if[typebuiltin]:
  rename1 `TypeBuiltin ann tb typ args` >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.ignore_bind_def] >>
  irule grouped_default_bind_error >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def, AllCaseEqs()] >>
  (reverse conj_tac >- fs[unspecified_behaviour_exempt_def]) >>
  rpt gen_tac >> BETA_TAC >> irule grouped_default_bind_error >> simp[vyperStateTheory.return_def] >>
  (reverse conj_tac
   >- (irule grouped_default_list_fold_error >> simp[] >>
       rpt gen_tac >> disch_tac >> first_x_assum irule >>
       fs[EVERY_MEM, constSubstTheory.no_sha256_collections] >>
       drule exprCallBoundsTheory.expr_list_member_bound >> simp[])) >>
  rpt gen_tac >>
  Cases_on `evaluate_type_builtin cx tb typ (MAP expr_type args) x` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >> metis_tac[]
QED

Finalise grouped_default_error_descent_if[local]

Theorem grouped_read_bind[local]:
  f st <> (INR (Error err),ee) /\
  (!v mid. f st = (INL v,mid) ==> g v mid <> (INR (Error err),ee)) ==>
  bind f g st <> (INR (Error err),ee)
Proof
  simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem grouped_read_subscripts[local]:
  unspecified_behaviour_exempt tops err ==>
  (!tv v sb. evaluate_subscripts tv v sb <> INR err)
Proof
  rpt strip_tac >> drule vyperStateTheory.evaluate_subscripts_error_shape >>
  gvs[unspecified_behaviour_exempt_def]
QED

Theorem grouped_read_state[local]:
  unspecified_behaviour_exempt tops err ==>
  (!cx src st ee. get_immutables cx src st <> (INR (Error err),ee)) /\
  (!cx p st ee. place_type_value cx p st <> (INR (Error err),ee)) /\
  (!cx src id st ee. lookup_global cx src id st <> (INR (Error err),ee))
Proof
  strip_tac >> conj_asm1_tac
  >- (simp[vyperStateTheory.get_immutables_def, vyperStateTheory.get_address_immutables_def,
           vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
           vyperMiscTheory.option_CASE_rator, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, AllCaseEqs()] >> gvs[unspecified_behaviour_exempt_def]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `p` >>
      simp[vyperStateTheory.place_type_value_def, vyperStateTheory.get_scopes_def,
           vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_def,
           vyperMiscTheory.option_CASE_rator, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[unspecified_behaviour_exempt_def] >> metis_tac[]) >>
  simp[vyperStateTheory.lookup_global_def, vyperStateTheory.get_immutables_def,
       vyperStateTheory.get_address_immutables_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.record_storage_event_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       UNCURRY, LET_THM, vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, vyperStateTheory.var_decl_info_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[unspecified_behaviour_exempt_def]
QED

Theorem grouped_read_storage_element[local]:
  unspecified_behaviour_exempt tops err ==>
  !cx tr slot tv bd i st ee.
    resolve_array_element cx tr slot (ArrayTV tv bd) [ValueSubscript (IntV i)] st <>
    (INR (Error err),ee)
Proof
  strip_tac >> rpt gen_tac >>
  `!slot mid. resolve_array_element cx tr slot tv [] mid = (INL (slot,tv,[]),mid)` by
    (Cases_on `tv` >> simp[vyperStateTheory.resolve_array_element_def, vyperStateTheory.return_def]) >>
  Cases_on `bd` >> Cases_on `tr` >>
  gvs[vyperStateTheory.resolve_array_element_def, vyperStateTheory.get_storage_backend_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.get_transient_storage_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def, COND_RATOR, AllCaseEqs(),
      unspecified_behaviour_exempt_def] >>
  metis_tac[]
QED

Theorem grouped_read_extend_storage[local]:
  unspecified_behaviour_exempt tops err ==>
  !cx tr slot tv sb st ee.
    extend_storage_place cx tr slot tv sb st <> (INR (Error err),ee)
Proof
  strip_tac >> drule grouped_read_storage_element >> strip_tac >>
  rpt gen_tac >> Cases_on `tv` >> Cases_on `sb` >>
  TRY (rename1 `extend_storage_place _ _ _ _ (ValueSubscript v) _ <> _` >>
       Cases_on `v`) >>
  simp[oneline vyperStateTheory.extend_storage_place_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.prod_CASE_rator,
       COND_RATOR, UNCURRY, AllCaseEqs()] >>
  rpt strip_tac >> gvs[unspecified_behaviour_exempt_def] >> metis_tac[]
QED

Theorem grouped_read_selection[local]:
  unspecified_behaviour_exempt tops err ==>
  !cx ty v sb st ee. select_result cx ty v sb st <> (INR (Error err),ee)
Proof
  strip_tac >> drule grouped_read_state >> strip_tac >>
  drule grouped_read_subscripts >> strip_tac >>
  `!cx p st ee. read_place cx p st <> (INR (Error err),ee)` by
    (rpt strip_tac >>
     `read_result cx (PlaceR p) st = (INR (Error err),ee)` by simp[vyperStateTheory.read_result_def] >>
     metis_tac[gasExemptCertTheory.read_result_no_exempt_error]) >>
  drule grouped_read_extend_storage >> strip_tac >>
  rpt gen_tac >> Cases_on `v` >>
  TRY (rename1 `select_result _ _ (PlaceR p) _ _ <> _` >> Cases_on `p`) >>
  TRY (rename1 `select_result _ _ (HashMapRef _ _ _ vt) _ _ <> _` >>
       Cases_on `sb` >> Cases_on `vt`) >>
  simp[oneline vyperStateTheory.select_result_def, oneline vyperStateTheory.extend_place_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def, vyperStateTheory.raise_def, LET_THM] >>
  rpt (ho_match_mp_tac grouped_read_bind >> conj_tac
       >- (simp[vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_def,
                vyperStateTheory.record_storage_event_def, vyperStateTheory.return_def,
                vyperStateTheory.raise_def, vyperMiscTheory.option_CASE_rator,
                vyperMiscTheory.sum_CASE_rator, AllCaseEqs()] >>
           rpt strip_tac >> gvs[unspecified_behaviour_exempt_def]) >>
       rpt gen_tac >> disch_tac) >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def, unspecified_behaviour_exempt_def]
QED

Theorem grouped_read_array_length[local]:
  unspecified_behaviour_exempt tops err ==>
  !cx v st ee. result_array_length cx v st <> (INR (Error err),ee)
Proof
  strip_tac >> ho_match_mp_tac vyperStateTheory.result_array_length_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[Once vyperStateTheory.result_array_length_def, vyperStateTheory.return_def] >>
  ho_match_mp_tac grouped_read_bind >> conj_tac
  >- (rename1 `get_storage_backend cx tr st <> _` >> Cases_on `tr` >>
      simp[vyperStateTheory.get_storage_backend_def, vyperStateTheory.get_accounts_def,
           vyperStateTheory.get_transient_storage_def, vyperStateTheory.bind_def,
           vyperStateTheory.return_def]) >>
  TRY (rpt gen_tac >> disch_tac >> simp[vyperStateTheory.return_def] >> NO_TAC) >>
  TRY (rename1 `read_result _ _ _ <> _` >> disch_tac >>
       drule_then (qspec_then `tops` mp_tac) gasExemptCertTheory.read_result_no_exempt_error >> simp[]) >>
  qx_gen_tac `w` >> rpt gen_tac >> disch_tac >> Cases_on `w` >>
  simp[vyperValueTheory.array_value_CASE_rator, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[unspecified_behaviour_exempt_def]
QED

Theorem grouped_default_read_error_rules[local]:
  unspecified_behaviour_exempt tops err ==>
  (!cx src id st ee. lookup_global cx src id st <> (INR (Error err),ee)) /\
  (!cx v st ee. read_result cx v st <> (INR (Error err),ee)) /\
  (!cx v st ee. conditional_result cx v st <> (INR (Error err),ee)) /\
  (!cx ty v sb st ee. select_result cx ty v sb st <> (INR (Error err),ee)) /\
  (!cx v st ee. result_array_length cx v st <> (INR (Error err),ee))
Proof
  strip_tac >> drule grouped_read_state >> strip_tac >>
  drule grouped_read_selection >> strip_tac >>
  drule grouped_read_array_length >> strip_tac >>
  simp[] >> conj_tac >- metis_tac[gasExemptCertTheory.read_result_no_exempt_error] >>
  rpt gen_tac >> Cases_on `v` >>
  simp[vyperStateTheory.conditional_result_def, vyperStateTheory.return_def, vyperStateTheory.raise_def]
  >- (ho_match_mp_tac grouped_read_bind >> conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> IF_CASES_TAC >> simp[vyperStateTheory.return_def] >>
      ho_match_mp_tac grouped_read_bind >> conj_tac
      >- metis_tac[vyperStateTheory.read_result_def, gasExemptCertTheory.read_result_no_exempt_error] >>
      simp[vyperStateTheory.return_def]) >>
  rpt strip_tac >> gvs[unspecified_behaviour_exempt_def]
QED

Theorem grouped_default_binop_error_rules[local]:
  !err u tv bop v1 v2.
    constant_binop bop /\
    (err = RuntimeError "abi_decode invalid" \/
     err = RuntimeError "transfer_value recipient overflow") ==>
    evaluate_binop u tv bop v1 v2 <> INR err
Proof
  rpt gen_tac >> Cases_on `bop` >>
  simp[constant_binop_def, vyperValueOperationTheory.evaluate_binop_def] >>
  strip_tac >> gvs[] >>
  simp[vyperValueOperationTheory.bounded_int_op_def,
       vyperValueOperationTheory.bounded_decimal_op_def, AllCaseEqs()] >>
  simp[oneline vyperValueOperationTheory.binop_negate_def, AllCaseEqs()]
QED

Theorem grouped_default_builtin_error_rules[local]:
  !tops err cx acc ty bt tys vs.
    unspecified_behaviour_exempt tops err /\
    (runtime_constant_builtin bt \/ constant_builtin bt) ==>
    evaluate_builtin cx acc ty bt tys vs <> INR err
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[constant_builtin_def, runtime_constant_builtin_def] >>
  simp[unspecified_behaviour_exempt_def] >> strip_tac >> gvs[] >>
  simp[evaluate_builtin_def] >>
  gvs[vyperValueOperationTheory.evaluate_as_wei_value_def, evaluate_block_hash_def,
      vyperValueOperationTheory.bounded_int_op_def,
      vyperValueOperationTheory.bounded_decimal_op_def, AllCaseEqs()] >>
  simp[grouped_default_binop_error_rules]
QED

val type_builtin_eq = oneline evaluate_type_builtin_def;
val max_value_eq = oneline vyperValueOperationTheory.evaluate_max_value_def;
val min_value_eq = oneline vyperValueOperationTheory.evaluate_min_value_def;

Theorem grouped_default_type_builtin_error_rules[local]:
  !tops err cx tb typ tys vs.
    unspecified_behaviour_exempt tops err /\ constant_type_builtin tb ==>
    evaluate_type_builtin cx tb typ tys vs <> INR err
Proof
  rpt gen_tac >> Cases_on `tb` >> simp[constant_type_builtin_def] >>
  simp[unspecified_behaviour_exempt_def] >> strip_tac >> gvs[] >>
  simp[type_builtin_eq, max_value_eq, min_value_eq, AllCaseEqs()]
QED

Theorem grouped_default_pure_error_rules[local]:
  !tops err. unspecified_behaviour_exempt tops err ==>
    (!cx acc ty bt tys vs.
      (runtime_constant_builtin bt \/ constant_builtin bt) ==>
      evaluate_builtin cx acc ty bt tys vs <> INR err) /\
    (!cx tb typ tys vs. constant_type_builtin tb ==>
      evaluate_type_builtin cx tb typ tys vs <> INR err)
Proof
  metis_tac[grouped_default_builtin_error_rules,
            grouped_default_type_builtin_error_rules]
QED

Theorem grouped_default_error_descent:
  unspecified_behaviour_exempt tops err /\
  EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds /\
  (!p c a b. MEM p ds /\ expr_size c < expr_size p /\
     runtime_constant_expr mods c /\ no_sha256_expr c ==>
     eval_expr cx c a <> (INR (Error err),b)) ==>
  eval_exprs cx ds st <> (INR (Error err),ee)
Proof
  strip_tac >>
  drule grouped_default_pure_error_rules >> strip_tac >>
  drule grouped_default_read_error_rules >> strip_tac >>
  irule grouped_default_error_descent_if >> simp[] >> metis_tac[]
QED
