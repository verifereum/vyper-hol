Theory bodyPtrPopTargetSimMapContinuation
Ancestors
  bodyPtrPopTargetSimMapTail bodyPtrPopTargetSimPost bodyPtrPopTargetFactor
  bodyPtrHashBuiltinsGhostCompose exprSimWordArgs targetPlaceSimCasesBase
  bodyPtrPopTargetDefs loweringPosts exprLowering exprLoweringProps
  compileEnv loweringStateRelDefs vyperState vyperTypeSystem venomState exprSimMapKey freshWrites
  bodyPtrEnvBuiltinsGhostCompose bodyPtrPopTargetSimArrayGas
  gasSummaryComposePtr

(* Mapping extension is state independent, for both map and value children. *)
Theorem target_map_source_ptr:
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv) es = (res,ee) /\
  (!m. res <> INR (Error (TypeError m))) ==>
  ee = es /\ ?child. res = INL child /\ place_readable cx es child /\
    (!s. place_ptr_rel cenv cx s child
      (hashmap_slot base_slot (encode_hashmap_key kt kv)) (SOME (slot_loc tr)) vt) /\
    (!G tn r s. op_taint tn (FST r) = {} /\ op_prov G (FST r) = NONE ==>
      target_ptr_ok cenv child r G tn s) /\
    (!gs. extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv)
      (es with gas_obs := gs) = (INL child,es with gas_obs := gs))
Proof
  Cases_on `vt`
  >- (rename1 `Type ty` >> Cases_on `evaluate_type (get_tenv cx) ty` >>
      simp[extend_place_def, bind_def, return_def, lift_option_type_def, raise_def] >>
      rpt strip_tac >> gvs[] >>
      simp[place_readable_def, place_ptr_rel_def, target_ptr_ok_def]) >>
  simp[extend_place_def, return_def] >> rpt strip_tac >> gvs[] >>
  simp[place_readable_def, place_ptr_rel_def, target_ptr_ok_def]
QED

Theorem target_map_compile_parts_ptr:
  compile_get_target_ptr cfn ce bt sa = ((bop,loc,SOME (MapPT kt vt)),sm) /\
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) sa = (r,sb) ==>
  ?key sn hashed sp slot.
    lower_value cfn ce (expr_type e) e sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn
     else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript bop hashed sp = (slot,sb) /\
    r = (slot,loc,SOME (value_type_place vt))
Proof
  strip_tac >> Cases_on `lower_value cfn ce (expr_type e) e sm` >>
  drule_all pop_compile_target_map_cut >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `is_bytestring_type kt` >> gvs[comp_return_def] >> metis_tac[]
QED

Theorem target_map_normal_continue_ptr:
  target_post ctx func cenv cx es sa sm s0 em
    (HashMapRef tr base_slot kt vt) (HashMapT kt vt)
    (bop,loc,SOME (MapPT kt vt)) s1 /\
  expr_post ctx func cenv cx idx em sm sn s1 en kv key t /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\ (!l. bop <> Label l) /\
  fn_inst_ids_distinct func /\ fn_has_code sp sb func /\ fn_has_code sn sb func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  MAP FDOM em.scopes = MAP FDOM en.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ptr_val_ok cx kt kv key G tn t /\ op_taint tn bop = {} /\
  ghost_inv d cenv cx en G tn t /\ ~ctx_has_dalloca ctx /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sn x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sn x) /\
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv) en = (res,ef) /\
  (!m. res <> INR (Error (TypeError m))) ==>
  ef = en /\ ?child u H tm. res = INL child /\
    gas_path_ptr D 0 ctx func PG G tn t 0 H tm (OK u) /\
    target_post ctx func cenv cx es sa sb s0 en child vt
      (slot,loc,SOME (value_type_place vt)) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx en H tm u /\
    target_ptr_ok cenv child (slot,loc,SOME (value_type_place vt)) H tm u /\
    ghost_kept cenv es sa G0 tn0 s0 H tm
Proof
  strip_tac >> drule_all target_map_source_ptr >>
  disch_then (qspec_then `cenv` strip_assume_tac) >> simp[] >>
  `eval_operand bop s1 = SOME base_slot /\ loc = SOME (slot_loc tr) /\
   (!x. bop = Var x ==> not_fresh_at sm x) /\
   stmt_state_rel ctx func cenv cx em s1 /\ wb_frame cenv es em sa s0 s1` by
    (fs[target_post_wb_frame, place_ptr_rel_def] >> metis_tac[]) >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    compile_mapping_index_success_tail_ptr >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "post"
QED

Resume target_map_normal_continue_ptr[post]:
  `wb_frame cenv es en sa s0 u` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `em`, `en`, `sm`, `s1`, `u`,
                  `ctx`] mp_tac wb_frame_trans >> simp[]) >>
  `wb_frame cenv es en sa s0 t` by
    (drule_all target_post_index_frame >> simp[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 H tm` by suspend "ghost" >>
  `!x. slot = Var x ==> not_fresh_at sb x` by
    (drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
     strip_tac >> gvs[]) >>
  qexistsl_tac [`u`, `H`, `tm`] >> simp[target_post_wb_frame]
QED

Resume target_map_normal_continue_ptr[ghost]:
  `local_ptrs_rel func cenv es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
  irule ghost_kept_locals_trans >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G`, `en`, `t`, `sn`, `tn`] >>
  simp[] >> fs[wb_frame_def] >>
  metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise target_map_normal_continue_ptr

Theorem target_map_extend_gas_tail_ptr:
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv) es = (res,ee) ==>
  ee = es /\ !gs.
    extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv)
      (es with gas_obs := gs) = (res,es with gas_obs := gs)
Proof
  Cases_on `vt`
  >- (rename1 `Type ty` >> Cases_on `evaluate_type (get_tenv cx) ty` >>
      simp[extend_place_def, bind_def, return_def, lift_option_type_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[extend_place_def, return_def] >> rpt strip_tac >> gvs[]
QED

(* The source extension consumes no gas.  Exceptions in the base or index
   remain the responsibility of the enclosing bind, before this normal cut. *)
Theorem target_map_suffix_outcome_ptr:
  ef.gas_obs = [] /\
  (?child t H tm.
    extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv) ef = (INL child,ef) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    target_post ctx fn cenv cx es sa sb s0 ef child vt rb t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ef H tm t /\ target_ptr_ok cenv child rb H tm t /\
    ghost_kept cenv es sa G0 tn0 s0 H tm) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript kv)) (ef,s,G,tn)
    (\res ee H tm t. ?child. res = INL child /\
      target_post ctx fn cenv cx es sa sb s0 ee child vt rb t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee H tm t /\ target_ptr_ok cenv child rb H tm t /\
      ghost_kept cenv es sa G0 tn0 s0 H tm)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> irule target_extension_outcome_ptr >> conj_tac
  >- (rpt strip_tac >> drule target_map_extend_gas_tail_ptr >> simp[]) >>
  disj1_tac >> qexistsl_tac [`child`, `t`, `H`, `tm`] >>
  `ef with gas_obs := [] = ef` by simp[evaluation_state_component_equality] >>
  simp[] >> metis_tac[]
QED
