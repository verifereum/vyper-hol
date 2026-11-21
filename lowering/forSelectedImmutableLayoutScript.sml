(* Reconstitute a captured immutable array's code-layout postcondition
   from the current projection, without freezing the surrounding value. *)
Theory forSelectedImmutableLayout
Ancestors
  exprSimSubscriptArrayLiveImmutableMetadata vyperBareGlobalName
  reasonEndpointResourcesPtr loweringPosts context

Theorem selected_immutable_array_value_holds:
  expr_sim_inv c cx env em /\ expr_sim_inv c cx env ep /\
  stmt_state_rel H ctx func c cx ep t /\ ~cx_const_name cx (src,name) /\
  vv_place_ptr c cx em u (PlaceR (ImmutablePlace src name path)) vv /\
  vv_location vv = SOME LocCode /\
  eval_operand (vv_operand vv) u = SOME bw /\
  eval_operand (vv_operand vv) t = SOME bw /\
  runtime_place_typed cx em (ImmutablePlace src name path) (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  (?rt rv. lookup_immutable cx ep src name = SOME (rt,rv) /\
    evaluate_subscripts rt rv path = INL (ArrayV av)) ==>
  immutable_holds c cx (ArrayT et bd) (Value (ArrayV av)) bw ep t
Proof
  strip_tac >> Cases_on `vv` >> gvs[vv_location_def, vv_operand_def] >>
  rename1 `eval_operand p.ptr_operand u = SOME bw` >>
  `vv_place_ptr c cx em u (PlaceR (ImmutablePlace src name path))
    (LocatedValue (ArrayT et bd) p)` by fs[vv_place_ptr_def] >>
  `!rt rv. FLOOKUP (case ALOOKUP ep.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables src imms) name =
        SOME (rt,rv) ==> evaluate_subscripts rt rv path = INL (ArrayV av)` by
    (rpt strip_tac >> Cases_on `ALOOKUP ep.immutables cx.txn.target` >>
     gvs[lookup_immutable_def]) >>
  drule_at (Pat `vv_place_ptr _ _ _ _ _ _`) live_immutable_captured_array_view >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`etv`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  gvs[] >>
  drule_all immutable_holds_read_value >> simp[]
QED
