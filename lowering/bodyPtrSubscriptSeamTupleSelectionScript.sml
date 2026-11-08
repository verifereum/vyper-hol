(* Selection endpoints, independent of the fresh ADD execution. *)
Theory bodyPtrSubscriptSeamTupleSelection
Ancestors
  bodyPtrSubscriptSeamTupleSource bodyPtrSubscriptSeamTupleNonmemory
  bodyPtrSubscriptSeamTupleMemory bodyPtrSubscriptSeamTuplePost
  bodyPtrSubscriptTupleDispatch bodyPtrAttributeFields bodyPtrSubscriptSeamTupleLayoutBridge
  exprSimDefs exprSimHyps exprSimHypsDefs exprSimProps exprSimTuple exprSimAttributeProps
  exprSimAggregateChildren exprSimFieldLayout exprSimAttributeFields
  loweringPosts exprLowering compileEnv context vyperAST vyperTyping
  valueEncoding valueEncodingProofs tupleMemoryLayout vyperTypeABI list rich_list

Theorem tuple_selected_vv_post:
  expr_body_pre cenv cx env (Subscript ann obj idx) (es with gas_obs := gs) /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  eval_expr cx obj (es with gas_obs := gs) = (INL btv,ee) /\
  vv_post ctx func cenv cx obj es sa sn s0 ee btv bvv q /\
  eval_operand (vv_operand bvv) q = SOME w /\
  idx = Literal ity (IntL (&k)) /\
  eval_operand dst q = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) ==>
  ?tv'. select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee = (INL tv',ee) /\
    vv_post ctx func cenv cx (Subscript ann obj idx) es sa sn s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >> drule tuple_selected_source >>
  simp[vv_post_initial_gas] >> disch_then drule >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  irule tuple_child_post >> simp[post_value_type_def, expr_type_def] >> metis_tac[]
QED

Theorem tuple_selected_ptr:
  expr_body_pre cenv cx env (Subscript ann obj idx) (es with gas_obs := gs) /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  eval_expr cx obj (es with gas_obs := gs) = (INL btv,ee) /\
  vv_post ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  ptr_vv_ok cx (TupleT tys) btv bvv ee G tn s /\
  (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv obj (vv_operand bvv) G s) /\
  idx = Literal ity (IntL (&k)) /\ eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\ (vv_loc bvv = LocCode ==> op_prov H dst = NONE) /\
  (!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
    ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
  ?tv'. select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee = (INL tv',ee) /\
    ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee H tn' t /\
    (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Subscript ann obj idx) dst H t)
Proof
  strip_tac >> drule tuple_selected_source >>
  simp[vv_post_initial_gas] >> disch_then drule >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx ee s /\
    vv_at cenv cx (TupleT tys) sa sm ee btv bvv s` by
    (fs[vv_post_def, expr_body_pre_def] >> gvs[]) >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `k < LENGTH tvs` by simp[] >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (drule_all tuple_memory_child_address >> strip_tac >>
      `tuple_val_wf vs tvs` by metis_tac[typed_value_wf] >>
      `type_memory_bytes cenv (lowered_value_type cenv obj) = type_memory_size_list tvs /\
       type_memory_bytes cenv (lowered_value_type cenv (Subscript (EL k tys) obj (Literal ity (IntL (&k))))) =
         type_memory_size (EL k tvs)` by
        (`expr_body_pre cenv cx env obj es` by
           (drule tuple_subscript_pre >> simp[]) >>
         `lowered_value_type cenv obj = post_value_type cenv obj` by
           (irule aggregate_lowered_post_type >>
            simp[is_word_type_def, is_bytestring_type_def] >> metis_tac[]) >>
         simp[lowered_value_type_def, post_value_type_def, expr_type_def] >>
         conj_tac
         >- (`type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
               metis_tac[expr_sim_inv_memory_size] >>
             gvs[type_memory_size_def]) >>
         metis_tac[expr_sim_inv_memory_size]) >>
      simp[] >> irule tuple_memory_selected_ptr >>
      goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
      gvs[MAP_TAKE] >> metis_tac[]) >>
  simp[] >> irule tuple_nonmemory_selected_ptr >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
