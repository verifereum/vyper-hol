(* Seam 2 joint induction, a held leaf of the agg step: an array subscript
   in exactly the residual case of
   exprSimSubscriptArrayTheory.compile_subscript_array_place_base_case
   (lowering/exprSimSubscriptArrayScript.sml), which is ADMITTED there
   because vv_post does not tie the base's pointer to its source place.
   Held: no run proves it; it is retired with that admission once a
   place-pointer clause (vv_place_ptr) is in vv_post. *)
Theory bodyIntCallFamAggSubscriptHeld
Ancestors
  bodyIntCallJointContract

Theorem intcall_subscript_array_place_base_held:
  !fp e ann obj idx et bd ce env es sa sb s ty vv.
    (!e'. expr_size e' < expr_size e ==>
          intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
          intcall_map_producer fp e') /\
    e = Subscript ann obj idx /\
    expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
    ~((!t r t'. eval_expr fp.jc_cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t.
         eval_expr fp.jc_cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~ce.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocMemory))) /\
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      expr_body_pre ce fp.jc_cx env e es /\
      supportedExprs$supported_expr fp.jc_tops e /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
      compile_expr ce ty e sa = (vv,sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx e) (es,s)
        (\res ee u. ?tv. res = INL tv /\
           vv_holds ce fp.jc_cx (post_value_type ce e) tv vv ee u /\
           vv_at ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u /\
           (post_value_type ce e <> expr_type e ==>
            vv_own ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u) /\
           (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) /\
           (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
           (post_value_type ce e <> NoneT /\
            ~is_word_type (post_value_type ce e) /\
            ~is_bytestring_type (post_value_type ce e) /\
            (case vv of StackValue _ _ => T
                      | LocatedValue _ p => p.ptr_location = LocMemory) ==>
            !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) =
                    SOME tv' ==>
              ?w a k. eval_operand (vv_operand vv) u = SOME w /\
                a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
                a + k < dimword (:256) /\
                (fp.jc_lo <= a \/
                 ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
           intcall_expr_cont fp ce env es sa s ee sb u)
        (\res ee r. expr_exit res r)
Proof
  cheat
QED
