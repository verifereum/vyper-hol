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
