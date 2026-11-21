Theory immutableIteratorPrefixWrite
Ancestors
  vyperAST vyperInterpreter vyperState vyperTypeContract vyperTypeSystem
  vyperStoragePlaceProvenance vyperBareGlobalName vyperCallOutcomeFrame
  whitelistForIterImmFrame targetPlaceSimCasesBase list rich_list alist finite_map

(* Attributes after the first subscript do not count towards the access
   checked by the loop guard. The checked attributes begin the runtime path. *)
Theorem eval_immutable_base_attribute_prefix[local]:
  !target cx es src id path es' pending.
    eval_base_place cx target es = (INL (PlaceR (ImmutablePlace src id path)),es') ==>
    ?attrs tail. place_access target pending = (TopLevelNameTarget (src,id),attrs) /\
                path ++ MAP AttrSubscript pending = MAP AttrSubscript attrs ++ tail
Proof
  ho_match_mp_tac base_assignment_target_induct >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- (gen_tac >> rename1 `TopLevelNameTarget nid` >> PairCases_on `nid` >>
      rpt strip_tac >> gvs[Once evaluate_def] >>
      drule lookup_global_immutable_root >> simp[place_access_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      drule extend_place_immutable_root >> strip_tac >> gvs[place_access_def] >>
      first_x_assum drule >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> simp[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[place_access_def] >>
  first_x_assum drule >> disch_then (qspec_then `s::pending` mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem eval_immutable_target_attribute_prefix[local]:
  eval_target_place cx target es = (INL (ImmutablePlace src id path),es') ==>
  ?attrs tail. place_access target [] = (TopLevelNameTarget (src,id),attrs) /\
              path = MAP AttrSubscript attrs ++ tail
Proof
  strip_tac >> gvs[Once evaluate_def, bind_def, get_place_def, return_def,
                  raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_immutable_base_attribute_prefix >> disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

(* Unlike the type-based memory rule, only one non-prefix premise is needed:
   a successful assignment cannot descend into attributes of an array. *)
Theorem assign_subscripts_other_attribute_prefix[local]:
  !attrs ws tv old tail op new av.
    ~isPREFIX ws attrs /\
    evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av) /\
    assign_subscripts tv old (MAP AttrSubscript ws ++ tail) op = INL new ==>
    evaluate_subscripts tv new (MAP AttrSubscript attrs) = INL (ArrayV av)
Proof
  Induct >> Cases_on `ws` >> simp[evaluate_subscripts_def, assign_subscripts_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `old` >>
  gvs[assign_subscripts_def, AllCaseEqs()] >>
  Cases_on `h = h'`
  >- (gvs[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP, AllCaseEqs()] >>
      first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
      disch_then drule_all >> simp[]) >>
  `h' <> h` by metis_tac[] >>
  Cases_on `ALOOKUP l h'` >> gvs[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP]
QED

Theorem lookup_immutable_set_existing[local]:
  lookup_immutable cx es src id = SOME (tv,old) ==>
  lookup_immutable cx (SND (set_immutable cx src id tv new es)) src id = SOME (tv,new)
Proof
  simp[set_immutable_def, lookup_immutable_def, bind_def,
       get_address_immutables_def, set_address_immutables_def, lift_option_type_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def, get_source_immutables_def, set_source_immutables_def,
       ALOOKUP_ADELKEY, FLOOKUP_UPDATE]
QED

Theorem immutable_prefix_assignment[local]:
  ~isPREFIX ws attrs /\
  lookup_immutable cx es src id = SOME (tv,old) /\
  evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av) /\
  assign_subscripts tv old (MAP AttrSubscript ws ++ tail) op = INL new ==>
  ?root. lookup_immutable cx (SND (set_immutable cx src id tv new es)) src id = SOME (tv,root) /\
         evaluate_subscripts tv root (MAP AttrSubscript attrs) = INL (ArrayV av)
Proof
  rpt strip_tac >> qexists_tac `new` >> conj_tac
  >- (irule lookup_immutable_set_existing >> goal_assum (drule_at Any)) >>
  drule_all assign_subscripts_other_attribute_prefix >> simp[]
QED

Theorem immutable_lookup_get_existing[local]:
  lookup_immutable cx es src id = SOME (tv,old) ==>
  ?imms. get_immutables cx src es = (INL imms,es) /\ FLOOKUP imms id = SOME (tv,old)
Proof
  simp[lookup_immutable_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> simp[return_def, raise_def]
QED

Theorem immutable_prefix_write[local]:
  ~isPREFIX ws attrs /\
  lookup_immutable cx es src id = SOME (tv,old) /\
  evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av) ==>
  ?root. lookup_immutable cx
           (SND (write_place cx (ImmutablePlace src id (MAP AttrSubscript ws ++ tail)) v es))
           src id = SOME (tv,root) /\
         evaluate_subscripts tv root (MAP AttrSubscript attrs) = INL (ArrayV av)
Proof
  strip_tac >> drule immutable_lookup_get_existing >> strip_tac >>
  simp[write_place_def, bind_def, lift_option_type_def, return_def, lift_sum_def] >>
  Cases_on `assign_subscripts tv old (MAP AttrSubscript ws ++ tail) (Replace v)` >>
  simp[return_def, raise_def] >> metis_tac[immutable_prefix_assignment]
QED

Theorem immutable_prefix_append[local]:
  ~isPREFIX ws attrs /\
  lookup_immutable cx es src id = SOME (tv,old) /\
  evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av) ==>
  ?root. lookup_immutable cx
           (SND (append_place cx (ImmutablePlace src id (MAP AttrSubscript ws ++ tail)) v es))
           src id = SOME (tv,root) /\
         evaluate_subscripts tv root (MAP AttrSubscript attrs) = INL (ArrayV av)
Proof
  strip_tac >> drule immutable_lookup_get_existing >> strip_tac >>
  simp[append_place_def, place_type_value_def, read_place_def, bind_def,
       lift_option_type_def, return_def, lift_sum_def] >>
  Cases_on `subscripts_type tv (MAP AttrSubscript ws ++ tail)` >> simp[return_def, raise_def] >>
  Cases_on `evaluate_subscripts tv old (MAP AttrSubscript ws ++ tail)` >>
  simp[return_def, raise_def] >>
  rename1 `evaluate_subscripts tv old _ = INL child` >>
  rename1 `subscripts_type tv _ = SOME ty` >>
  Cases_on `append_element ty child v` >> simp[return_def, raise_def] >>
  metis_tac[immutable_prefix_write]
QED

Theorem immutable_prefix_pop[local]:
  ~isPREFIX ws attrs /\
  lookup_immutable cx es src id = SOME (tv,old) /\
  evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av) ==>
  ?root. lookup_immutable cx
           (SND (pop_place cx (ImmutablePlace src id (MAP AttrSubscript ws ++ tail)) es))
           src id = SOME (tv,root) /\
         evaluate_subscripts tv root (MAP AttrSubscript attrs) = INL (ArrayV av)
Proof
  strip_tac >> drule immutable_lookup_get_existing >> strip_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def, return_def, lift_sum_def] >>
  Cases_on `evaluate_subscripts tv old (MAP AttrSubscript ws ++ tail)` >>
  simp[return_def, raise_def] >>
  rename1 `evaluate_subscripts tv old _ = INL child` >>
  Cases_on `popped_value child` >> simp[return_def, raise_def] >>
  Cases_on `assign_subscripts tv old (MAP AttrSubscript ws ++ tail) PopOp` >>
  simp[return_def, raise_def] >>
  rename1 `assign_subscripts tv old _ PopOp = INL new` >>
  Cases_on `set_immutable cx src id tv new es` >>
  rename1 `set_immutable cx src id tv new es = (ans,mid)` >>
  Cases_on `ans` >> simp[return_def, raise_def] >>
  drule_all immutable_prefix_assignment >> simp[]
QED

Theorem immutable_guarded_prefix_mutation:
  place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
  callee_write_ok p target /\
  eval_target_place cx target s = (INL pl,mid) ==>
  (let R = \es es'.
      (?old. lookup_immutable cx es src name = SOME (tv,old) /\
             evaluate_subscripts tv old (MAP AttrSubscript attrs) = INL (ArrayV av)) ==>
      (?root. lookup_immutable cx es' src name = SOME (tv,root) /\
              evaluate_subscripts tv root (MAP AttrSubscript attrs) = INL (ArrayV av))
   in state_rel_frame R (write_place cx pl v) /\
      state_rel_frame R (append_place cx pl v) /\
      state_rel_frame R (pop_place cx pl))
Proof
  strip_tac >> Cases_on `?path. pl = ImmutablePlace src name path`
  >- (gvs[] >> drule eval_immutable_target_attribute_prefix >> strip_tac >>
      gvs[callee_write_ok_def, place_contains_def, state_rel_frame_result] >>
      rpt conj_tac >> rpt strip_tac >>
      metis_tac[immutable_prefix_write, immutable_prefix_append, immutable_prefix_pop, pairTheory.SND]) >>
  `!s' n' path. pl = ImmutablePlace s' n' path ==> (s',n') <> (src,name)` by
    metis_tac[pairTheory.PAIR_EQ] >>
  simp[state_rel_frame_result] >> rpt conj_tac >> rpt strip_tac >>
  metis_tac[lookup_immutable_write_other, append_guarded_immutable_frame,
            pop_place_immutable_other]
QED
