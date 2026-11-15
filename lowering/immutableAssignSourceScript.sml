(* The source continuation writes a bare immutable without consuming gas observations. *)
Theory immutableAssignSource
Ancestors
  exprSimMemorySource vyperTypeInvariants vyperInterpreter vyperState
  finite_map alist
Libs monadsyntax

Theorem immutable_assignment_source_tail:
  env_consistent env cx ee /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\
  read_result cx pv ee = (INL v,ee) /\
  imms = (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m) ==>
  !tail.
    (do value <- read_result cx pv;
        place <- eval_target_place cx (TopLevelNameTarget (src,id));
        write_place cx place value od) (ee with gas_obs := tail) =
    (INL (), (ee with immutables :=
      (cx.txn.target,set_source_immutables src
        (get_source_immutables src imms |+ (id,(tv,v))) imms) ::
      ADELKEY cx.txn.target ee.immutables) with gas_obs := tail)
Proof
  strip_tac >>
  `env_context_consistent env cx /\ env_immutables_consistent env cx ee` by
    fs[env_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
  `?old. FLOOKUP (get_source_immutables src imms) id = SOME (tv,old)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`env_immutables_consistent env cx ee`,
        `FLOOKUP env.bare_globals (src,id) = SOME ity`,
        `evaluate_type (get_tenv cx) ity = SOME tv`, `imms = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qhdtm_assum `env_immutables_consistent` (fn th =>
       MAP_EVERY assume_tac
         (List.take (CONJUNCTS (PURE_REWRITE_RULE [env_immutables_consistent_def] th), 2))) >>
     qpat_x_assum `imms = _`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
     `IS_SOME (FLOOKUP (get_source_immutables src imms) id)` by metis_tac[] >>
     Cases_on `FLOOKUP (get_source_immutables src imms) id`
     >- (qpat_x_assum `IS_SOME _` mp_tac >> simp[]) >>
     rename1 `FLOOKUP (get_source_immutables src imms) id = SOME entry` >>
     PairCases_on `entry` >>
     qpat_x_assum `!src id ty tv v. _`
       (qspecl_then [`src`,`id`,`ity`,`entry0`,`entry1`] mp_tac) >>
     asm_rewrite_tac[] >>
     qpat_assum `evaluate_type (get_tenv cx) ity = SOME tv`
       (fn th => rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
  drule read_result_gas_obs >> strip_tac >> gen_tac >>
  simp[bind_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  simp[bind_def, Ntimes evaluate_def 3, get_place_def,
       lookup_global_def, get_immutables_def, get_address_immutables_def,
       lift_option_type_def, return_def, write_place_def, assign_subscripts_def,
       lift_sum_def, set_immutable_def, set_address_immutables_def,
       get_source_immutables_def, evaluation_state_component_equality]
QED
