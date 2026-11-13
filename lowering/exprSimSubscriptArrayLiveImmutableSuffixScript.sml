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

Theorem live_immutable_element_place_ptr:
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  src = cenv.ce_module /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  p.ptr_location = LocCode /\ w = n2w (off+k) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w+n2w j) ==>
  vv_place_ptr cenv cx ee q
    (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst p.ptr_location))
Proof
  strip_tac >> drule_all array_element_step_offset >> strip_tac >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  gvs[vv_place_ptr_def, mk_ptr_def] >>
  pure_rewrite_tac[GSYM wordsTheory.word_add_n2w, arithmeticTheory.ADD_ASSOC,
                   wordsTheory.WORD_ADD_ASSOC] >> REFL_TAC
QED

Theorem live_immutable_element_summary:
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  src = cenv.ce_module /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  expr_type obj = ArrayT et bd /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
    (PlaceR (ImmutablePlace src id path)) (LocatedValue ann p) q /\
  p.ptr_location = LocCode /\ w = n2w (off+k) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w+n2w j) /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all live_immutable_select >> strip_tac >>
  drule_all live_immutable_element_place_ptr >> strip_tac >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
     (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
     (LocatedValue et (mk_ptr dst p.ptr_location)) q` by
    (irule vv_post_array_element >> simp[] >>
     qexistsl_tac [`ann`,`av`,`i`,`PlaceR (ImmutablePlace src id path)`] >> simp[]) >>
  irule select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED
