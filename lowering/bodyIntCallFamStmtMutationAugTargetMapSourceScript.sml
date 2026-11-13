(* Observation-free mapping extension with an arbitrary machine post. *)
Theory bodyIntCallFamStmtMutationAugTargetMapSource
Ancestors
  targetSubscriptSplit vyperState vyperTypeSystem gasSummary option

Theorem intcall_target_mapping_extend_summary:
  well_formed_vtype (get_tenv cx) vt /\
  (!pv. extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es =
          (INL pv,es) ==>
     ?u. gas_marked_path F ctx func s 0 (OK u) /\
         Q (INL pv) (es with gas_obs := []) u) ==>
  gas_summary_at F (ctx,func) []
    (extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key))
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `?pv. extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es =
          (INL pv,es)` by
    (Cases_on `vt` >>
     fs[well_formed_vtype_def, well_formed_type_def, IS_SOME_EXISTS] >>
     simp[extend_place_def, lift_option_type_def, bind_def, return_def]) >>
  first_x_assum drule >> strip_tac >>
  irule target_subscript_extend_summary_normal >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
