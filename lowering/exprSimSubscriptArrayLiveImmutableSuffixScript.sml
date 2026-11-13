(* Immutable array selection on current contents, independent of the base evaluation. *)
Theory exprSimSubscriptArrayLiveImmutableSuffix
Ancestors
  exprSimSubscriptArraySuffix exprSimSubscriptArraySource exprSimSubscriptArrayFramed
  exprSimProps exprSimCopy exprSimHypsDefs loweringPosts context vyperState
  vyperPlaceStatePreservation vyperPlaceResultTyping vyperPlaceTyping vyperValueOperation vyperValue
  valueEncodingDefs finite_map words

Theorem live_immutable_select:
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
    SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  evaluate_subscripts itv iv path = INL a /\
  evaluate_subscripts ptv a [sb] = INL v ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb ee =
    (INL (PlaceR (ImmutablePlace src id (path ++ [sb]))),ee) /\
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [sb]))) ee = (INL v,ee)
Proof
  rpt gen_tac >> strip_tac >>
  `subscripts_type itv path = SOME ptv` by metis_tac[mem_path_offset_sound] >>
  `evaluate_subscripts itv iv (path ++ [sb]) = INL v` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `get_immutables cx src ee =
    (INL (get_source_immutables src (THE (ALOOKUP ee.immutables cx.txn.target))),ee)` by
    (Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
     gvs[get_immutables_def, get_address_immutables_def, bind_def,
         lift_option_type_def, return_def]) >>
  conj_tac
  >- (Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
      drule_all select_immutable_result >>
      simp[bind_def, lift_sum_def, return_def]) >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def]
QED
