(* Source-only conversion at the qualified callee's reached lock and body. *)
Theory bodySelectedQualifiedBodySourceMods
Ancestors
  bodySelectedReturnSourceSuccessMods vyperInterpreter vyperState vyperAST
  vyperTyping vyperTypeValues vyperValueOperation vyperFiniteStoragePreservation
  vyperStorageTrace vyperStorageFootprint gasContext exprSimDefs
  compileUnit compileVyper compileEnv constSubstMods nonreentrantEquiv[qualified]
Libs
  monadsyntax

val pushed = ``cx with stk updated_by CONS (src,name)``;
val run_body = ``try (do eval_stmts (^pushed) ss; return NoneV od) handle_function``;
val callee_src = ``do lock_if_nr cx nr (is_view_mut mut); ^run_body od``;
val rest = ``do lock_if_nr cx nr (is_view_mut mut);
  rv <- finally_unless_halt (finally (^run_body) (pop_function prev))
          (unlock_if_nr cx nr (is_view_mut mut));
  crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
  return (Value crv)
  od``;

Theorem selected_qualified_body_source_mods:
  (!tail. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := tail) =
          (INL (),locked with gas_obs := tail)) /\
  (!tail. eval_stmts (^pushed) ss (locked with gas_obs := pre ++ tail) =
          (res,ee with gas_obs := tail)) ==>
  (!tail. (^callee_src) (es1 with gas_obs := pre ++ tail) =
    ((case res of
        INL _ => INL NoneV
      | INR (ReturnException v) => INL v
      | INR (Error e) => INR (Error e)
      | INR (AssertException msg) => INR (AssertException msg)
      | INR HaltException => INR HaltException
      | _ => INR (Error (TypeError "handle_function"))),ee with gas_obs := tail)) /\
  (storage_trace_domain (^pushed) st0 ee.storage_trace <=>
   storage_trace_domain cx st0 ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon (^pushed) st0 H ee.storage_trace /\
       valid_horizon (^pushed) st0 H locked.storage_trace /\
       valid_horizon cx st0 H es1.storage_trace)
Proof
  strip_tac >> conj_tac
  >- (gen_tac >>
      qpat_assum `!tail. lock_if_nr _ _ _ _ = _`
        (qspec_then `pre ++ tail` assume_tac) >>
      qpat_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `tail` assume_tac) >>
      Cases_on `res` >>
      simp[try_def, ignore_bind_def, bind_def, return_def,
           Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      rename1 `eval_stmts _ _ _ = (INR ex,_)` >> Cases_on `ex` >>
      simp[handle_function_def, raise_def, return_def]) >>
  conj_tac
  >- simp[storage_trace_domain_def, valid_horizon_def,
          storage_well_formed_on_stk, storage_observations_ok_stk] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H locked.storage_trace` by
    (`storage_trace_frame (eval_stmts (^pushed) ss)` by simp[evaluate_storage_trace_frame] >>
     qpat_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (`storage_trace_frame (lock_if_nr cx nr (is_view_mut mut))` by
       simp[storage_trace_frame_optional_locks] >>
     qpat_assum `!tail. lock_if_nr _ _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  fs[valid_horizon_def, storage_well_formed_on_stk, storage_observations_ok_stk]
QED

Theorem selected_void_package[local]:
  set_internal_package_target target
    (package_internal_fn_unit mods trans nkeys deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,NoneT,ss))) =
    (label,ce,params,has_rb,nr',key,trans',view,ctor,ilen',ss_comp,rt) ==>
  rt = NONE /\ ~has_rb /\ ce.ce_returns_count = 0
Proof
  simp[subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def, update_cenv_nonreentrant_def] >>
  strip_tac >> qpat_x_assum `_ = ce` (SUBST1_TAC o SYM) >>
  simp[build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, returns_stack_count_def]
QED

Theorem selected_qualified_fallthrough_void_mods:
  (!tail. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := tail) =
          (INL (),locked with gas_obs := tail)) /\
  (!tail. eval_stmts (^pushed) ss (locked with gas_obs := pre ++ tail) =
          (INL (),ee with gas_obs := tail)) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  gas_admissible (^rest) expr_vv_res_ok es1 ==>
  (!tail. (^callee_src) (es1 with gas_obs := pre ++ tail) =
          (INL NoneV,ee with gas_obs := tail)) /\
  ret = NoneT /\ rtv = NoneTV /\
  (set_internal_package_target target
    (package_internal_fn_unit mods trans nkeys deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans',view,ctor,ilen',ss_comp,rt) ==>
    rt = NONE /\ ~has_rb /\ ce.ce_returns_count = 0) /\
  ?out. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) /\
    (!tail. (^rest) (es1 with gas_obs := pre ++ tail) =
            (INL (Value NoneV),(out with scopes := prev) with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H out.storage_trace ==>
         valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es1.storage_trace)
Proof
  strip_tac >>
  `!tail. (^callee_src) (es1 with gas_obs := pre ++ tail) =
          (INL NoneV,ee with gas_obs := tail)` by
    (drule_all selected_qualified_body_source_mods >>
     disch_then (qspec_then `st0` (mp_tac o CONJUNCT1)) >>
     simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `?out. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
         (INL (),out)` by
    (Cases_on `nr /\ ~is_view_mut mut`
     >- (Cases_on `cx.nonreentrant_slot` >>
         fs[unlock_if_nr_def, return_def, Excl "is_view_mut_def",
            nonreentrantEquivTheory.release_nonreentrant_lock_execution]) >>
     fs[unlock_if_nr_def, return_def, Excl "is_view_mut_def"]) >>
  drule_all selected_return_source_success_mods >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  `rtv = NoneTV` by
    (qpat_x_assum `safe_cast _ NoneV = SOME _` mp_tac >>
     Cases_on `rtv` >> simp[NoAsms, Once safe_cast_def, pairTheory.UNCURRY] >>
     Cases_on `b` >> simp[NoAsms, AllCaseEqs()] >>
     metis_tac[bound_nchotomy]) >>
  `ret = NoneT` by metis_tac[evaluate_type_NoneTV_imp_NoneT] >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  MATCH_ACCEPT_TAC selected_void_package
QED
