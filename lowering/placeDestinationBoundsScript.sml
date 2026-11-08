Theory placeDestinationBounds
Ancestors
  bodySimAugPlaceLoad placeMemoryLiveRegion exprSimProps exprLoweringProps
  exprSimHypsDefs loweringPosts words allocLimits allocLimitsProps

Theorem memory_place_destination_bound:
  stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  write_place cx p v ee = (INL (),ff) ==>
  w2n w + type_memory_size dtv < dimword (:256)
Proof
  strip_tac >>
  `!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> metis_tac[aug_place_entry_type_agrees]) >>
  drule_all memory_place_live_region >> strip_tac >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  first_x_assum drule >> strip_tac >> decide_tac
QED

(* The compiler's own target dispatch gives the static layout used by the
   allocation check; no independent re-inference of target types is needed. *)
Theorem storage_target_normalization_bound:
  compile_get_target_ptr cfn cenv bt sa = ((op,SOME loc,SOME (ValPT dty)),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  assign_alloc_ok cenv bt e /\
  ~is_word_type dty /\ dty <> lowered_value_type cenv e /\
  ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  type_memory_bytes cenv dty < 2 ** 64
Proof
  strip_tac >>
  `target_store_place cenv bt = SOME (SOME (ValPT dty))` by
    (drule compile_get_target_ptr_store_place >> simp[]) >>
  gvs[assign_alloc_ok_def]
QED
