(* Counted selection from the current contents of a live local array. *)
Theory exprSimSubscriptArrayLiveMemory
Ancestors
  bodySimAugPlaceMemory
  exprSimSubscriptArrayLiveMemoryEndpoint exprSimSubscriptArrayLiveImmutableEndpoint
  exprSimSubscriptArraySuffix exprSimSubscriptArraySource targetSubscriptMemory exprSimHyps
  exprSimProps exprSimHash exprSimHypsDefs exprSimWordArgs exprSimVVFrame loweringPosts exprLoweringProps loweringStateRelDefs
  vyperState vyperPlaceTyping vyperValueOperation valueTypingMemoryProps words finite_map arithmetic

Theorem live_memory_place_at[local]:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee q /\
  place_ptr_rel cenv cx q (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op q = SOME w ==>
  vv_at cenv cx ty sa sd ee (PlaceR (MemoryPlace id path))
    (LocatedValue ty (mk_ptr op LocMemory)) q
Proof
  strip_tac >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `local_ptrs_rel func cenv ee.scopes q /\ alloca_room ctx func q` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  qpat_x_assum `!name entry p sz. _ ==> _` drule_all >> strip_tac >> gvs[] >>
  `tv0 = entry.type` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes id ee.scopes = SOME entry ==> _` drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
     qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> cenv.ce_var_type id = SOME ty` drule >>
     strip_tac >> gvs[] >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes id ee.scopes = SOME entry ==> _` drule_all >> simp[]) >>
  gvs[] >> drule mem_path_offset_sound >> strip_tac >>
  drule alloca_room_next_lt >> strip_tac >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k) = w2n b + k` by simp[w2n_add_2, w2n_n2w, LESS_MOD] >>
  `read_result cx (PlaceR (MemoryPlace id path)) ee = (INL v,ee)` by
    simp[read_result_def, read_place_def, get_scopes_def, bind_def,
         lift_option_type_def, lift_sum_def, return_def, read_memory_path_def] >>
  simp[vv_at_def, contextTheory.mk_ptr_def] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`id`,`w2n b`,`sz`] >>
  simp[local_region_def, local_val_at_def, local_path_at_def, local_place_at_def] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  conj_tac >- decide_tac >>
  metis_tac[]
QED

Theorem live_memory_place_holds[local]:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee q /\
  place_ptr_rel cenv cx q (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op q = SOME w ==>
  vv_holds cenv cx ty (PlaceR (MemoryPlace id path))
    (LocatedValue ty (mk_ptr op LocMemory)) ee q /\
  vv_place_ptr cenv cx ee q (PlaceR (MemoryPlace id path))
    (LocatedValue ty (mk_ptr op LocMemory))
Proof
  strip_tac >> drule_all place_ptr_rel_memory_current >> strip_tac >>
  `read_result cx (PlaceR (MemoryPlace id path)) ee = (INL v,ee)` by
    simp[read_result_def, read_place_def, get_scopes_def, bind_def,
         lift_option_type_def, lift_sum_def, return_def, read_memory_path_def] >>
  conj_tac
  >- (simp[vv_holds_def, contextTheory.mk_ptr_def] >>
      rpt strip_tac >> irule val_in_memory_word_type >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`ty`,`get_tenv cx`] >> simp[]) >>
  gvs[vv_place_ptr_def, place_ptr_rel_def, contextTheory.mk_ptr_def] >> metis_tac[]
QED

Theorem live_memory_selection_post[local]:
  vv_post ctx func cenv cx obj es sa sb s0 t r bvv u ==>
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s ==>
  is_word_type (expr_type idx) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q /\
  expr_sim_inv cenv cx env ee /\
  place_ptr_rel cenv cx q (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type et) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_type (get_tenv cx) et = SOME tv /\ eval_operand dst q = SOME w ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
    (PlaceR (MemoryPlace id path)) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  disch_tac >> disch_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func cenv cx idx t sb sd u ee iv iop q` by
    (irule exprSimSubscriptArrayEndpointTheory.word_expr_post_readonly_tail >> simp[] >>
     qexistsl_tac [`s`,`sc`] >> simp[]) >>
  `wb_frame cenv es t sa s0 u` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
     simp[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv t ee sb u q` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es ee sa s0 q` by
    (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 u` by fs[vv_post_def] >>
     `pure_frame cenv func t sb u q` by (drule_all expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> simp[] >> qexistsl_tac [`t`,`sb`,`u`] >> fs[wb_frame_def]) >>
  drule_all live_memory_place_at >> strip_tac >>
  drule_all live_memory_place_holds >> strip_tac >>
  irule vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, expr_has_effect_thm, vv_storage_live_def] >>
  simp[contextTheory.mk_ptr_def]
QED

Theorem live_memory_array_suffix_summary:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),t) /\
  eval_expr cx idx t = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.gas_obs = [] /\
  (!entry. lookup_scopes id ee.scopes = SOME entry ==>
     ?v. evaluate_subscripts entry.type entry.value path = INL v) /\
  vv_post ctx func cenv cx obj es sa sb s0 t (PlaceR (MemoryPlace id path))
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (MemoryPlace id path)) (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >>
  drule_all_then assume_tac exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_runtime_typed >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  drule_all live_memory_array_current_view >> strip_tac >>
  `subscripts_type entry.type path = SOME (ArrayTV etv bd)` by
    (drule_all place_ptr_rel_memory_current >> simp[]) >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >> gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  `array_length (ArrayTV etv bd) av < dimword (:256)` by
    metis_tac[target_memory_array_length_bound] >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (Cases_on `av` >> Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
     simp[not_fresh_at_def]) >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (mp_tac o Q.AP_TERM `SND`) >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM ci_mono_def] >> irule ci_mono_compile_array_subscript >>
     simp[ci_mono_compile_ptr_load]) >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_assum `iv = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`ee`] >> simp[]) >>
  `read_result cx (PlaceR (MemoryPlace id path)) ee = (INL (ArrayV av),ee)` by
    simp[read_result_def, read_place_def, get_scopes_def, bind_def,
         lift_option_type_def, lift_sum_def, return_def, read_memory_path_def] >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `iv = IntV i` SUBST_ALL_TAC >>
  suspend "selection"
QED

Resume live_memory_array_suffix_summary[selection]:
  `val_wf (ArrayTV etv bd) (ArrayV av)` by metis_tac[value_has_type_memory_wf] >>
  `((case bd of Fixed _ => F | Dynamic _ => T) ==> 
     mload (w2n b) s = n2w (array_length (ArrayTV etv bd) av)) /\
   ((case bd of Fixed _ => F | Dynamic _ => T) = F ==>
     (case bd of Fixed n => n | Dynamic _ => 0) = array_length (ArrayTV etv bd) av)` by
    (Cases_on `bd` >> simp[]
     >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
                            vyperValueOperationTheory.array_length_def]) >>
     drule_all target_memory_array_header >> simp[]) >>
  drule_all_then assume_tac array_index_word_bounds >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
      (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
       else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >> fs[] >> metis_tac[]) >>
  `?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)` by
    (qpat_x_assum `p.ptr_location = LocMemory` SUBST_ALL_TAC >>
     drule_all target_memory_array_abort_path >> simp[]) >>
  `extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) ee =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    (drule_all extend_place_memory_live_result >>
     disch_then (qspecl_then [`ValueSubscript (IntV i)`,`cx`] mp_tac) >>
     drule_all evaluate_array_subscript_oob >> simp[]) >>
  `select_result cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) ee =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    gvs[select_result_def, bind_def, ignore_bind_def] >>
  irule select_result_counted_summary >> simp[] >> goal_assum (drule_at Any) >>
  gvs[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume live_memory_array_suffix_summary[valid]:
  `idx_in_range (is_signed_type (expr_type idx)) iw
      (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
       else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >> fs[] >> metis_tac[]) >>
  qpat_x_assum `p.ptr_location = LocMemory` SUBST_ALL_TAC >>
  drule_all target_memory_array_path >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  suspend "child"
QED

Resume live_memory_array_suffix_summary[child]:
  `0 <= i /\ Num i < array_length (ArrayTV etv bd) av` by
    (fs[vyperArrayTheory.valid_index_def] >>
     metis_tac[integerTheory.NUM_LT, integerTheory.NUM_OF_INT, integerTheory.INT_POS]) >>
  `?k. mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (k,etv) /\
       ((if (case bd of Fixed _ => F | Dynamic _ => T) then b + n2w 32 else b) +
        iw * n2w (type_memory_bytes cenv et) = b + n2w k)` by
    ( `i2w i = iw` by
        (gvs[] >> Cases_on `is_signed_type (expr_type idx)` >> simp[]) >>
      Cases_on `bd`
      >- (drule_all (target_memory_array_offset |> Q.INST [`dyn` |-> `F`] |> SIMP_RULE (srw_ss()) []) >> simp[]) >>
      drule_all (target_memory_array_offset |> Q.INST [`dyn` |-> `T`] |> SIMP_RULE (srw_ss()) []) >> simp[]) >>
  `?v. evaluate_subscripts (ArrayTV etv bd) (ArrayV av)
         [ValueSubscript (IntV i)] = INL v` by
    metis_tac[evaluate_array_subscript_in_bounds] >>
  `evaluate_subscripts entry.type entry.value (path ++ [ValueSubscript (IntV i)]) = INL v` by
    metis_tac[aug_place_subscripts_append_live] >>
  `place_ptr_rel cenv cx q (PlaceR (MemoryPlace id path)) b (SOME LocMemory) (Type (ArrayT et bd))` by
    (fs[place_ptr_rel_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `place_ptr_rel cenv cx q (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
     (b + n2w k) (SOME LocMemory) (Type et)` by
    (drule_all place_ptr_rel_memory_step >> simp[]) >>
  `eval_operand dst q = SOME (b + n2w k)` by
    fs[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.is_slot_addressed_def] >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
     (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
     (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (`sb.cs_next_id <= sd.cs_next_id` by decide_tac >>
     drule live_memory_selection_post >> disch_then drule >>
     disch_then irule >> simp[] >>
     rpt conj_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  `extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) ee =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),ee)` by
    (drule_all extend_place_memory_live_result >>
     disch_then (qspecl_then [`ValueSubscript (IntV i)`,`cx`] mp_tac) >> simp[]) >>
  `select_result cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) ee =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),ee)` by
    gvs[select_result_def, bind_def, ignore_bind_def] >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[]
QED

Finalise live_memory_array_suffix_summary
