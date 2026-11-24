(* A memory select frame uses the length of the current source array. *)
Theory bodyWriteArrayMemoryChildMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteArraySelectMods targetSubscriptMemory
  targetPlaceSimCasesBase exprSimSubscriptArraySuffix typedMemoryCopy
  valueTypingMemoryProps bodyFullTargetDefs bodyWriteTargetStageMods
  exprSimHypsDefs vyperTypeEvalCaseProofs vyperTypeSystem vyperArray
  loweringPosts exprLoweringProps compileEnv vyperInterpreter vyperState
  vyperValue integer_word venomState words finite_map
  overflowElimHelpers vyperTypeEnv loweringStateRelDefs

Theorem memory_select_source[local]:
  lookup_scopes id mid2.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  i = (if sgn then w2i iw else &(w2n iw)) ==>
  let child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])) in
  let in_range = idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av)) in
    extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) mid2 =
      ((if in_range then INL child else
        INR (Error (RuntimeError "evaluate_subscripts array_index"))),mid2) /\
    (in_range ==> valid_index (ArrayTV etv bd) av i /\ place_readable cx mid2 child)
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  drule_all target_memory_array_length_bound >> strip_tac >>
  `valid_index (ArrayTV etv bd) av i <=> 0 <= i /\ Num i < array_length (ArrayTV etv bd) av` by
    (Cases_on `0 <= i` >> simp[valid_index_def, IgnAsm `i = _`] >>
     `(&Num i : int) = i` by simp[IgnAsm `i = _`] >> metis_tac[integerTheory.INT_LT]) >>
  drule_all array_index_word_bounds >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`,`cx`] assume_tac) >>
  qpat_x_assum `i = _` kall_tac >>
  `(0 <= i /\ Num i < array_length (ArrayTV etv bd) av) <=>
     idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av))` by metis_tac[] >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  Cases_on `idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av))` >>
  simp[Excl "valid_index_def"] >> strip_tac >>
  drule_all extend_place_memory_live >> strip_tac >>
  irule targetSubscriptMemoryTheory.place_readable_memory_live >> simp[] >>
  goal_assum drule >> simp[]
QED

Theorem memory_select_pointer[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) b
    (SOME LocMemory) (Type (ArrayT et bd)) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  valid_index (ArrayTV etv bd) av i /\
  i = (if sgn then w2i iw else &(w2n iw)) ==>
  place_ptr_rel cenv cx t (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
    ((if (case bd of Dynamic _ => T | _ => F) then b + n2w (word_scale LocMemory) else b) +
     iw * n2w (elem_size_in_location cenv LocMemory et)) (SOME LocMemory) (Type et)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) et = SOME etv` by fs[evaluate_type_def, AllCaseEqs()] >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _` drule >> simp[]) >>
  drule (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >> strip_tac >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by simp[value_has_type_memory_wf] >>
  drule_all array_element_step_offset >> strip_tac >>
  qpat_assum `valid_index _ _ _`
    (strip_assume_tac o REWRITE_RULE [valid_index_def]) >>
  `iw = n2w (Num i)` by
    (Cases_on `sgn` >> gvs[n2w_w2n] >>
     drule nonneg_w2i_eq_w2n >> disch_then (SUBST1_TAC o SYM) >> simp[n2w_w2n]) >>
  qpat_x_assum `i = _` kall_tac >>
  `((if (case bd of Dynamic _ => T | _ => F) then b + n2w (word_scale LocMemory) else b) +
    iw * n2w (elem_size_in_location cenv LocMemory et)) =
   b + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv)` by
    (Cases_on `bd` >>
     simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
          word_mul_n2w] >>
     pure_rewrite_tac[GSYM word_add_n2w] >> simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  pop_assum SUBST1_TAC >> irule place_ptr_rel_memory_step >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists `ArrayT et bd` >> simp[]
QED

Theorem write_array_memory_child_from_current_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2)) /\
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2))
    (LocMemory,b,iw,n2w (array_length (ArrayTV etv bd) av)) (t3,G3,tn3) /\
  lookup_scopes id mid2.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) /\
  place_ptr_rel cenv cx t2 (PlaceR (MemoryPlace id path)) b
    (SOME LocMemory) (Type (ArrayT et bd)) /\
  SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  local_ptrs_reserved cenv sn /\
  (!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    op_prov G2 (FST rb) = FLOOKUP G2 p) ==>
  let child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])) in
  let in_range = idx_in_range (is_signed_type (expr_type e)) iw
    (n2w (array_length (ArrayTV etv bd) av)) in
    extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) mid2 =
      ((if in_range then INL child else
        INR (Error (RuntimeError "evaluate_subscripts array_index"))),mid2) /\
    (in_range ==> target_ptr_ok cenv child r G3 tn3 t3 /\
      write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3)
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  drule_all memory_select_source >>
  disch_then (strip_assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV) o REWRITE_RULE[LET_THM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_assum `_ ==> valid_index _ _ _ /\ _` drule >> strip_tac >>
  qpat_x_assum `write_array_reached_mods _`
    (strip_assume_tac o REWRITE_RULE[write_array_reached_mods_def]) >>
  qpat_x_assum `write_array_select_frame _ _ _`
    (strip_assume_tac o REWRITE_RULE[write_array_select_frame_def]) >>
  `vt = Type et` by
    (qpat_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
     simp[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()]) >>
  drule_all write_array_select_cut_mods >> strip_tac >>
  `place_ptr_rel cenv cx t3 (PlaceR (MemoryPlace id path)) b
      (SOME LocMemory) (Type (ArrayT et bd))` by
    (irule place_ptr_rel_vars_frame >> goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     qexists `t2` >> simp[lookup_var_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _` drule >> simp[]) >>
  qpat_x_assum `idx_in_range _ _ _ ==> ~t3.vs_halted /\ _` drule >> strip_tac >>
  conj_tac
  >- (simp[target_ptr_ok_def] >> rpt strip_tac >>
      `not_fresh_at sn p` by
        (qpat_assum `local_ptrs_reserved _ _`
           (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
         qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = SOME (PtrVar (Var p) sz1) ==> _` drule >> simp[]) >>
      qpat_assum `!x. not_fresh_at sn x ==> _` drule >> simp[]) >>
  `FST (SND r) = SOME LocMemory` by
    (qpat_x_assum `r = _` mp_tac >> Cases_on `r` >> simp[]) >>
  simp[write_target_location_mods_def, IgnAsm `i = _`] >>
  irule memory_select_pointer >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  conj_tac >- (qexists `is_signed_type (expr_type e)` >> simp[]) >>
  conj_tac >- (qexistsl [`av`,`etv`] >> simp[Excl "valid_index_def", IgnAsm `i = _`]) >>
  goal_assum (drule_at Any) >> simp[]
QED
