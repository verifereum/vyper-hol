(* Reconstruct a live array place from the current source/target relation. *)
Theory exprSimSubscriptArrayLiveMemoryEndpoint
Ancestors
  exprSimSubscriptArrayEndpoint exprSimSubscriptArraySource
  targetSubscriptMemory exprSimProps vyperTypeEnvPreservation vyperPlaceTyping
  exprSimWordArgs exprBopSimProps exprSimHypsDefs loweringPosts
  exprLoweringProps loweringStateRelDefs vyperState vyperValue
  vyperTyping finite_map list option

Theorem live_memory_array_current_view:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),t) /\
  eval_expr cx idx t = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  vv_post ctx func cenv cx obj es sa sb s0 t (PlaceR (MemoryPlace id path))
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\ ee.gas_obs = [] /\
  (!entry. lookup_scopes id ee.scopes = SOME entry ==>
     ?v. evaluate_subscripts entry.type entry.value path = INL v) ==>
  ?entry av etv b.
    lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    eval_operand p.ptr_operand s = SOME b /\ p.ptr_location = LocMemory /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
      (SOME LocMemory) (Type (ArrayT et bd)) /\
    val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n b) s.vs_memory /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV etv bd)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  drule_all expr_body_pre_place_metadata >> strip_tac >>
  gvs[runtime_place_typed_memory] >>
  `wb_frame cenv t ee sb u s` by metis_tac[expr_post_frame] >>
  `?entry'. lookup_scopes id ee.scopes = SOME entry'` by
    (fs[wb_frame_def, locals_kept_def] >>
     metis_tac[lookup_scopes_same_fdoms_some, IS_SOME_EXISTS]) >>
  `?v. evaluate_subscripts entry'.type entry'.value path = INL v` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  `entry'.type = entry.type` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes id t.scopes = SOME entry ==> _` drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [IS_SOME_EXISTS]) >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes id t.scopes = SOME entry ==> _` drule_all >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes id ee.scopes = SOME entry ==> _` drule_all >>
     simp[]) >>
  `vv_place_ptr cenv cx t u (PlaceR (MemoryPlace id path))
     (LocatedValue (ArrayT et bd) p)` by fs[vv_post_def] >>
  qpat_x_assum `vv_place_ptr _ _ _ _ _ _` mp_tac >>
  simp[vv_place_ptr_def] >> strip_tac >>
  `lookup_var q s = SOME b` by
    (fs[wb_frame_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand p.ptr_operand s = SOME (b + n2w k)` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`,`u`] >> fs[wb_frame_def]) >>
  `tv0 = entry.type` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes id t.scopes = SOME entry ==> _` drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [IS_SOME_EXISTS]) >>
     qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> cenv.ce_var_type id = SOME ty` drule >>
     strip_tac >> gvs[] >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes id t.scopes = SOME entry ==> _` drule_all >>
     simp[]) >>
  `tvk = tv` by metis_tac[mem_path_offset_sound, optionTheory.SOME_11] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) (b + n2w k)
     (SOME LocMemory) (Type (ArrayT et bd))` by
    (simp[place_ptr_rel_def] >> metis_tac[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED
