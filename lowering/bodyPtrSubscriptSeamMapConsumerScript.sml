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
