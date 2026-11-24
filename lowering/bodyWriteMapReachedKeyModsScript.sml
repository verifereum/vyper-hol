(* Source and operand facts at the two successful cuts of a mapping write. *)
Theory bodyWriteMapReachedKeyMods
Ancestors
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods bodyWriteTargetStageMods
  bodyFullTargetMappingRep bodyFullPredsMods bodyFullPostsMods bodyFullTargetDefs
  exprBodyPreProps loweringPosts bodyPtrDefs ptrDiscipline supportedExprs
  exprLowering compileEnv vyperTypeEvalCaseProofs stmtSimAugAssignPlace
  vyperTypeExprSoundness vyperTypeEnv vyperTypeSystem vyperValue
  vyperTyping vyperState vyperInterpreter
  vyperStorage byte words finite_map venomState

Theorem write_map_reached_key_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  type_place_target env bt = SOME (HashMapT kt vt) /\
  (!i s. MEM i (target_indices (SubscriptTarget bt e)) /\
         expr_sim_inv_mods mods cenv cx env s ==>
         expr_body_pre_mods mods cenv cx env i s) /\
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget bt e) /\
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1) ==>
  expr_sim_inv_mods mods cenv cx env mid1 /\
  body_const_cells_agree_mods mods cx env mid1 /\
  expr_body_pre_mods mods cenv cx env e mid1 /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e mid1
Proof
  strip_tac >>
  `expr_sim_inv_mods mods cenv cx env mid1 /\
   body_const_cells_agree_mods mods cx env mid1` by
    (irule write_base_reached_source_mods >>
     qexistsl_tac [`bt`,`pv`,`es with gas_obs := base_gas`] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> simp[target_indices_def]) >>
  `expr_body_pre_mods mods cenv cx env e mid1` by
    (qpat_assum `!i s. MEM i _ /\ _ ==> _` irule >> simp[target_indices_def]) >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_x_assum `body_base_target_full_ok_mods _ _ _ _` mp_tac >>
     simp[body_base_target_full_ok_mods_def] >> strip_tac >> first_x_assum irule >>
     qexistsl_tac [`es with gas_obs := base_gas`,`pv`,`mid1`] >> simp[]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  simp[] >> qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                         _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,`func`,
                 `shadow_func`,`cenv`,`env`,`expr_type e`,`mid1`] mp_tac) >> simp[]
QED

Theorem write_map_base_view[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sm s0 mid1 pv
    (HashMapT kt vt) rb G0 tn0 G1 tn1 t1 ==>
  ?tr base_slot bop.
    pv = HashMapRef tr base_slot kt vt /\
    rb = (bop,SOME (slot_loc tr),SOME (MapPT kt vt)) /\
    eval_operand bop t1 = SOME base_slot /\
    op_taint tn1 bop = {} /\ op_prov G1 bop = NONE /\
    (!x. bop = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> drule_then strip_assume_tac write_target_post_view_mods >>
  `?tr base_slot. pv = HashMapRef tr base_slot kt vt` by
    (Cases_on `pv` >> fs[write_target_location_mods_def, place_ptr_rel_def] >>
     rename1 `PlaceR p` >> Cases_on `p` >>
     gvs[write_target_location_mods_def, place_ptr_rel_def]) >>
  gvs[] >> drule_then strip_assume_tac write_target_mapping_view_mods >>
  PairCases_on `rb` >> gvs[value_type_place_def]
QED

Theorem write_map_base_not_label[local]:
  type_place_target env bt = SOME (HashMapT kt vt) /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) ==>
  !l. FST rb <> Label l
Proof
  Cases_on `bt`
  >~ [`NameTarget id`]
  >- simp[type_place_target_NameTarget]
  >~ [`TopLevelNameTarget nsid`]
  >- (simp[compile_get_target_ptr_def] >> rpt strip_tac >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >>
      gvs[comp_return_def] >> rename1 `SOME entry` >> Cases_on `entry` >>
      gvs[comp_return_def]) >>
  strip_tac >> drule aug_place_target_ptr_not_label >> simp[]
QED

Theorem write_map_base_operand_frame[local]:
  (!x. bop = Var x ==> not_fresh_at sm x) /\
  (!l. bop <> Label l) /\ eval_operand bop t1 = SOME base_slot /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2 /\
  expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 ==>
  eval_operand bop t2 = SOME base_slot /\
  op_taint tn2 bop = op_taint tn1 bop /\ op_prov G2 bop = op_prov G1 bop
Proof
  Cases_on `bop` >>
  simp[expr_post_def, ghost_kept_at_def, op_taint_def, op_prov_def,
       eval_operand_def] >> metis_tac[]
QED

Theorem write_map_post_key_type[local]:
  hashmap_key_type (expr_type e) /\ evaluate_type tenv (expr_type e) = SOME tv ==>
  post_value_type cenv e = expr_type e
Proof
  `!kt tv. hashmap_key_type kt /\ evaluate_type tenv kt = SOME tv ==>
           is_word_type kt \/ is_bytestring_type kt` by
    (Cases >> simp[hashmap_key_type_def,is_word_type_def,is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[hashmap_key_type_def,is_word_type_def,is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[hashmap_key_type_def,is_word_type_def,is_bytestring_type_def,
          evaluate_type_def, AllCaseEqs()]) >>
  strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem write_map_key_input_mods:
  expr_type e = kt /\ hashmap_key_type kt /\
  expr_body_pre_mods mods cenv cx env e mid1 /\
  body_const_cells_agree_mods mods cx env mid1 /\
  bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := key_gas) =
    (INL v,mid2) /\
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sm s0 mid1 pv
    (HashMapT kt vt) rb G0 tn0 G1 tn1 t1 /\
  type_place_target env bt = SOME (HashMapT kt vt) /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
  expr_store_bound cx (post_value_type cenv e) v iop t2 /\
  ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2 ==>
  (?tr base_slot bop.
     pv = HashMapRef tr base_slot kt vt /\
     rb = (bop,SOME (slot_loc tr),SOME (MapPT kt vt)) /\
     eval_operand bop t2 = SOME base_slot /\
     op_taint tn2 bop = {} /\ op_prov G2 bop = NONE /\
     (!x. bop = Var x ==> not_fresh_at sm x)) /\
  (?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v) /\
  (if is_bytestring_type kt then
     ?x b base cap bs.
       iop = Var x /\ eval_operand iop t2 = SOME (n2w b) /\
       FLOOKUP G2 x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= t2.vs_alloca_next /\
       op_taint tn2 iop = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn2.t_mem) /\
       mem_word_at b t2.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) t2.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand iop t2 = SOME (encode_hashmap_key kt v) /\
        op_taint tn2 iop = {} /\ op_prov G2 iop = NONE)
Proof
  strip_tac >>
  `expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2` by
    fs[expr_post_mods_def] >>
  conj_tac
  >- (drule_all_then assume_tac write_map_base_not_label >>
      drule_then strip_assume_tac write_map_base_view >> gvs[] >>
      drule_all_then strip_assume_tac write_map_base_operand_frame >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env e (mid1 with gas_obs := key_gas)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (mid1 with gas_obs := key_gas)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ mid2`
    (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[value_runtime_typed_def] >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule write_map_post_key_type >> simp[] >> goal_assum (drule_at Any)) >>
  `expr_store_bound cx kt v iop t2` by gvs[] >>
  drule_all_then mp_tac mapping_index_key_input >> simp[]
QED
