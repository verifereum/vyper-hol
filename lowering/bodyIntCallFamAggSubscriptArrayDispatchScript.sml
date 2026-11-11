(* Framed array production, with the inherited residual place-base boundary. *)
Theory bodyIntCallFamAggSubscriptArrayDispatch
Ancestors
  bodyIntCallFamAggSubscriptArrayProducer bodyIntCallFamAggSubscriptHeld
  bodyIntCallJointContract supportedExprs bodyIntCallFamAggSubscriptTypedSupport

Theorem intcall_subscript_array_outcome:
  (!e'. expr_size e' < expr_size (Subscript ann obj idx) ==>
     intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
     intcall_map_producer fp e') /\
  expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
  post_value_type ce obj = expr_type obj /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es /\
  supported_expr fp.jc_tops (Subscript ann obj idx) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr (Subscript ann obj idx)) /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Subscript ann obj idx)) (es,s)
    (\res ee u. ?tv. res = INL tv /\
      vv_holds ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) tv vv ee u /\
      vv_at ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u /\
      (post_value_type ce (Subscript ann obj idx) <> expr_type (Subscript ann obj idx) ==>
        vv_own ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u) /\
      (~expr_has_effect (Subscript ann obj idx) ==> vv_storage_live fp.jc_cx vv ee u) /\
      (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
      (post_value_type ce (Subscript ann obj idx) <> NoneT /\
       ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
       ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) /\
       (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript ann obj idx)) = SOME tv' ==>
        ?w a k. eval_operand (vv_operand vv) u = SOME w /\
          a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
          a + k < dimword (:256) /\
          (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `supported_expr fp.jc_tops idx` by
    (drule supported_subscript_index >> simp[]) >>
  `supported_place_type fp.jc_tops (expr_type obj)` by
    (irule supported_array_subscript_base_type >> metis_tac[]) >>
  `supported_expr fp.jc_tops obj` by
    (irule supported_subscript_value_base >> metis_tac[]) >>
  Cases_on `(!t r t'. eval_expr fp.jc_cx idx t = (INL r,t') ==>
      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t. eval_expr fp.jc_cx obj s <>
      (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
    ((~ce.ce_is_ctor /\
      !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) \/
     ((?n. bd = Fixed n) /\
      (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
      !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocMemory))`
  >- (irule intcall_subscript_array_framed_producer >> simp[] >>
      `intcall_expr_producer fp obj /\ intcall_forced_producer fp idx` by
        (conj_tac
         >- (first_x_assum (qspec_then `obj` mp_tac) >>
             simp[vyperASTTheory.expr_size_def]) >>
         first_x_assum (qspec_then `idx` mp_tac) >>
         simp[vyperASTTheory.expr_size_def]) >>
      fs[] >> qexists_tac `ty` >> simp[]) >>
  irule intcall_subscript_array_place_base_held >> simp[] >>
  conj_tac >- (qexists_tac `ty` >> simp[]) >> metis_tac[]
QED
