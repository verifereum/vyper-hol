Theory bodyLoopImmutableFrame
Ancestors
  alist list relation vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeContract vyperTypeSystem vyperStorageAccessFrame
  vyperTypeCallGraphSoundness vyperAST vyperState vyperInterpreter
  vyperBareGlobalName vyperImmutablesPreservation vyperStoragePlaceProvenance

(* A loop's initial calls generate a set closed under callable bodies and
   defaults. The checker guards each member of this set against writes. *)
Theorem loop_calls_reachable_writes:
  EVERY (callee_writes_ok mods p) calls ==>
  ?reached.
    EVERY reached calls /\
    !sid fn ts deploy mut nr args dflts ret body.
      reached (sid,fn) /\
      ALOOKUP mods sid = SOME ts /\
      lookup_callable_function deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
      stmts_writes_ok (callee_write_ok p) body /\
      EVERY reached (function_int_calls dflts body)
Proof
  strip_tac >>
  qexists_tac
    `\callee. ?origin. MEM origin calls /\
      (origin = callee \/
       TC (call_edge_rel (contract_call_edges mods)) origin callee)` >>
  conj_tac >- (simp[EVERY_MEM] >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `origin` (CONJUNCTS_THEN assume_tac)) STRIP_ASSUME_TAC) >>
  rename1 `lookup_callable_function deploy fn ts =
             SOME (mut,nr,args,dflts,ret,bod)` >>
  Cases_on `dflts = [] /\ bod = []`
  >- gvs[stmt_writes_ok_def, function_int_calls_def, int_calls_expr_def,
         int_calls_stmt_def] >>
  `?vis mut' nr' raw args' ret'.
     MEM (FunctionDecl vis mut' nr' raw fn args' dflts ret' bod) ts` by
    metis_tac[lookup_callable_function_SOME_decompose] >>
  strip_tac >>
  drule ALOOKUP_MEM >> strip_tac >>
  `EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
   stmts_writes_ok (callee_write_ok p) bod` by
    (qpat_x_assum `EVERY _ calls` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >>
     simp[callee_writes_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
     disch_then (drule_at Any) >> disch_then (drule_at Any) >>
     simp[contract_reachable_TC] >> metis_tac[]) >>
  simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM ((sid,fn),callee) (contract_call_edges mods)` by
    (irule contract_call_edges_function >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  metis_tac[TC_SUBSET, TC_TRANSITIVE, transitive_def, call_edge_rel_def]
QED

Theorem extend_immutable_array_field_error[local]:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) ==>
  ?err. extend_place cx (PlaceR (ImmutablePlace src name []))
          (AttrSubscript fld) st = (INR err,st)
Proof
  simp[lookup_immutable_def, extend_place_def, read_place_def,
       place_type_value_def, get_immutables_def, get_address_immutables_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, subscripts_type_def, evaluate_subscripts_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[] >>
  strip_tac >> simp[return_def, raise_def, subscripts_type_def,
                    evaluate_subscripts_def]
QED

Theorem eval_base_place_immutable_array_access[local]:
  !target cx st st' src name path elem bound av.
    lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
    eval_base_place cx target st =
      (INL (PlaceR (ImmutablePlace src name path)),st') ==>
    !pending. place_access target pending = (TopLevelNameTarget (src,name),[]) \/
      (target = TopLevelNameTarget (src,name) /\ path = [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) st = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_immutable_root]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner st = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >> strip_tac >>
  simp[place_access_def] >>
  first_x_assum (qspecl_then [`cx`,`st`] mp_tac) >>
  disch_then drule_all >> strip_tac
  >~ [`place_access inner [] = _`]
  >- (first_x_assum (qspec_then `[]` strip_assume_tac) >>
      gvs[place_access_def]) >>
  gvs[place_access_def] >>
  qmatch_asmsub_rename_tac
    `extend_place cx (PlaceR (ImmutablePlace src name child)) (AttrSubscript fld) mid` >>
  first_x_assum (qspec_then `fld::pending` strip_assume_tac) >> gvs[] >>
  gvs[Once evaluate_def] >>
  drule lookup_global_immutables >> strip_tac >>
  `?err. extend_place cx (PlaceR (ImmutablePlace src name []))
           (AttrSubscript fld) mid = (INR err,mid)` by
    (irule extend_immutable_array_field_error >>
     qexistsl [`av`,`bound`,`elem`] >> gvs[lookup_immutable_def]) >>
  gvs[]
QED

Theorem immutable_array_guarded_target:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
  callee_write_ok (TopLevelNameTarget (src,name)) target /\
  eval_target_place cx target st = (INL pl,st') ==>
  !path. pl <> ImmutablePlace src name path
Proof
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, get_place_def,
                      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all eval_base_place_immutable_array_access >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[callee_write_ok_def, place_contains_def, place_access_def]
QED
