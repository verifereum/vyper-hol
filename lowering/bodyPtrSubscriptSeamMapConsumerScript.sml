Theory bodyPtrSubscriptSeamMapConsumer
Ancestors
  bodyPtrSubscriptSeamMapTail bodyPtrSubscriptSeamMapPost
  bodyPtrSubscriptSeamMapCompose bodyPtrSubscriptMarkedCompose
  bodyPtrSubscriptMapDefs bodyPtrPreds gasSummaryComposePtr
  vyperHashMapStorage vyperStoragePlaceProvenance list

Theorem mapping_leaf_summary_ptr:
  (!tail. select_result cx (expr_type obj) captured (ValueSubscript kv)
     (ee with gas_obs := tail) =
     (INL (PlaceR (StoragePlace tr slot tv)),ee with gas_obs := tail)) /\
  gas_path_ptr (cx_dead cx) 0 ctx fn PG Gi tni it 0 G tn (OK u) /\
  storage_mapping_region cx tr slot (Type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  contract_storage_well_formed cx (ee with gas_obs := []) /\ storage_layout_safe cx /\
  stmt_state_rel ctx fn cenv cx (ee with gas_obs := []) u /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn u /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand u = SOME slot /\
  op_taint tn p.ptr_operand = {} /\ wb_frame cenv es sa s0 u /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (select_result cx (expr_type obj) captured (ValueSubscript kv))
    (ee with gas_obs := [],it,Gi,tni)
    (\res ef Gf tnf t. ?v. res = INL v /\
      vv_post ctx fn cenv cx (Subscript ann obj idx) es sa sb s0 ef v
        (LocatedValue ann p) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef Gf tnf t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx)) v
        (LocatedValue ann p) ef Gf tnf t /\
      (!ty op. LocatedValue ann p = StackValue ty op /\
        ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
        ptr_buf_ok cenv (Subscript ann obj idx) op Gf t) /\
      (!ty q. LocatedValue ann p = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Subscript ann obj idx) q.ptr_operand Gf t) /\
      ghost_kept cenv es sa G0 tn0 s0 Gf tnf)
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >> drule_all mapping_leaf_ptr_post >> strip_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl [`INL (PlaceR (StoragePlace tr slot tv))`, `ee`, `G`, `tn`, `OK u`] >>
  conj_tac
  >- simp[gas_marked_exec_ptr_def] >>
  disj1_tac >> qexists `u` >> simp[] >> gvs[]
QED

Theorem mapping_subscript_leaf_type:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt ==>
  vt = Type ann
Proof
  strip_tac >> drule_all exprSimSubscriptMapTheory.expr_body_pre_map_subscript_base >> strip_tac >>
  drule_all exprSimSubscriptMapTheory.expr_map_pre_checked_type >> strip_tac >>
  `~well_typed_expr env obj` by
    metis_tac[vyperTypeExprResultTheory.well_typed_expr_not_hashmap_place] >>
  qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
  simp[exprSimHypsDefsTheory.expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
  Cases_on `vt` >> simp[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]
QED

Theorem mapping_marked_source_leaf:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx obj)
    (es,s0,G0,tn0) left (INL (HashMapRef tr base_slot kt vt)) mid G1 tn1 (OK t) /\
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],t,G1,tn1) right (INL kv) fin Gi tni (OK it) ==>
  vt = Type ann /\ expr_type idx = kt /\ hashmap_key_type kt /\
  (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\ value_has_type key_ty kv) /\
  contract_storage_well_formed cx (fin with gas_obs := []) /\ storage_layout_safe cx /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  ?tv. evaluate_type (get_tenv cx) ann = SOME tv /\
    !tail. select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
      (ValueSubscript kv) (fin with gas_obs := tail) =
      (INL (PlaceR (StoragePlace tr
        (hashmap_slot base_slot (encode_hashmap_key kt kv)) tv)),fin with gas_obs := tail)
Proof
  strip_tac >> drule_all mapping_subscript_leaf_type >> strip_tac >>
  `gas_marked_exec F (ctx,fn) (eval_expr cx obj) (es,s0) left
     (INL (HashMapRef tr base_slot kt vt)) mid (OK t)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  `gas_marked_exec F (ctx,fn) (bind (eval_expr cx idx) (read_result cx))
     (mid with gas_obs := [],t) right (INL kv) fin (OK it)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env (fin with gas_obs := []) /\
   expr_type idx = kt /\ hashmap_key_type kt /\
   (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\ value_has_type key_ty kv) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (irule exprSimSubscriptMapTheory.mapping_subscript_marked_success >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) ann = SOME tv` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `contract_storage_well_formed cx (fin with gas_obs := []) /\ storage_layout_safe cx` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     pure_rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  gvs[] >> irule select_result_hashmap_leaf >> simp[]
QED

Theorem mapping_selection_summary_ptr:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (eval_expr cx obj)
    (es,s0,G0,tn0) left (INL (HashMapRef tr base_slot kt vt)) mid G1 tn1 (OK t) /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],t,G1,tn1) right (INL kv) fin Gi tni (OK it) /\
  storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
  wb_frame cenv es sa s0 t /\ ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  stmt_state_rel ctx fn cenv cx (mid with gas_obs := []) t /\
  expr_post ctx fn cenv cx idx (mid with gas_obs := []) sm sn t
    (fin with gas_obs := []) kv key it /\
  ptr_val_ok cx (post_value_type cenv idx) kv key Gi tni it /\
  ghost_inv d cenv cx (fin with gas_obs := []) Gi tni it /\
  ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gi tni /\
  it.vs_current_bb = sn.cs_current_bb /\ it.vs_inst_idx = LENGTH sn.cs_current_insts /\
  lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
  (if is_bytestring_type (expr_type idx) then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript slot hashed sp = (out,sb) /\
  fn_has_code sn sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  (!z. slot = Var z ==> not_fresh_at sm z) /\ (!l. slot <> Label l) /\
  eval_operand slot t = SOME base_slot /\ op_taint tn1 slot = {} /\
  p.ptr_location = slot_loc tr /\ p.ptr_operand = out ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt) (ValueSubscript kv))
    (fin with gas_obs := [],it,Gi,tni)
    (\res ef Gf tnf u. ?v. res = INL v /\
      vv_post ctx fn cenv cx (Subscript ann obj idx) es sa sb s0 ef v
        (LocatedValue ann p) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef Gf tnf u /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx)) v
        (LocatedValue ann p) ef Gf tnf u /\
      (!ty op. LocatedValue ann p = StackValue ty op /\
        ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
        ptr_buf_ok cenv (Subscript ann obj idx) op Gf u) /\
      (!ty q. LocatedValue ann p = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Subscript ann obj idx) q.ptr_operand Gf u) /\
      ghost_kept cenv es sa G0 tn0 s0 Gf tnf)
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >> drule_all mapping_marked_source_leaf >> strip_tac >>
  `~it.vs_halted` by metis_tac[bodyPtrHashBuiltinsSuffixTheory.hash_marked_ptr_normal] >>
  `local_ptrs_rel fn cenv es.scopes s0 /\
   local_ptrs_rel fn cenv (mid with gas_obs := []).scopes t` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        compileEnvTheory.state_rel_def, loweringPostsTheory.expr_post_def] >>
  `eval_operand slot it = SOME base_slot /\ op_taint tni slot = {}` by
    (qpat_assum `ghost_kept _ _ sm _ _ _ _ _`
       (mp_then Any mp_tac bodyPtrSubscriptSeamMapInterfaceTheory.mapping_slot_index_frame) >>
     disch_then irule >> simp[] >> gvs[loweringPostsTheory.expr_post_def]) >>
  `!z. slot = Var z ==> not_fresh_at sn z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  gvs[] >> drule_all mapping_index_tail_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `wb_frame cenv (mid with gas_obs := []) sm t it` by
    (gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >>
     metis_tac[]) >>
  `wb_frame cenv (mid with gas_obs := []) sm t u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     first_assum (irule_at (Pat `wb_frame _ _ _ _ u`)) >>
     first_assum (irule_at (Pat `wb_frame _ _ _ t _`)) >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     first_assum (irule_at (Pat `wb_frame _ _ _ _ u`)) >>
     first_assum (irule_at (Pat `wb_frame _ _ _ t _`)) >> simp[] >> metis_tac[]) >>
  `ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gu tnu` by
    (irule bodyPtrHashBuiltinsGhostComposeTheory.hash_expr_post_ghost_kept_compose >>
     first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gu tnu` by
    (irule bodyPtrEnvBuiltinsGhostComposeTheory.ghost_kept_locals_trans >>
     first_assum (irule_at (Pat `ghost_kept _ _ sa _ _ _ _ _`)) >>
     qexists `fn` >> simp[] >>
     gvs[loweringPostsTheory.wb_frame_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `storage_mapping_region cx tr
     (hashmap_slot base_slot (encode_hashmap_key (expr_type idx) kv)) (Type ann)` by
    metis_tac[storage_mapping_region_step] >>
  irule (SRULE [] mapping_leaf_summary_ptr) >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`Gu`, `tnu`, `u`] >> gvs[]
QED
