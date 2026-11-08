(* The internal-call callee body's joint induction: the held case of a
   subscript of a widened internal-call result.
 *
 * TOP-LEVEL:
 *   intcall_subscript_widened_producer
 *)
Theory bodyIntCallJointWidened
Ancestors
  bodyIntCallJointContract

(* Held, like bodySimSubscriptWidenedTheory.body_subscript_widened_call_base
   (the same case for the global body induction): a subscript whose base is
   an internal call that the call's type widens (post_value_type differs from
   the source type only for such a call, post_value_type_not_int_call).
   compile_subscript reads the base at offsets taken from the base's source
   type, so for a tuple base it reads the wrong field until the subscript
   readers use the lowered layout.  Retired together with
   body_subscript_widened_call_base. *)
Theorem intcall_subscript_widened_producer:
  !fp a e1 e2 t fid cargs drv.
    e1 = Call t (IntCall fid) cargs drv /\
    (!e'. expr_size e' < expr_size (Subscript a e1 e2) ==>
          intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
          intcall_map_producer fp e') ==>
    !ce env es sa sb s ty vv.
      post_value_type ce e1 <> expr_type e1 /\
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      expr_body_pre ce fp.jc_cx env (Subscript a e1 e2) es /\
      supportedExprs$supported_expr fp.jc_tops (Subscript a e1 e2) /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr (Subscript a e1 e2)) /\
      compile_expr ce ty (Subscript a e1 e2) sa = (vv,sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      gas_admissible (eval_expr fp.jc_cx (Subscript a e1 e2)) expr_vv_res_ok es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx (Subscript a e1 e2)) (es,s)
        (\res ee u. ?tv. res = INL tv /\
           vv_holds ce fp.jc_cx (post_value_type ce (Subscript a e1 e2)) tv vv ee u /\
           vv_at ce fp.jc_cx (post_value_type ce (Subscript a e1 e2)) sa sb ee tv vv u /\
           (post_value_type ce (Subscript a e1 e2) <> expr_type (Subscript a e1 e2) ==>
            vv_own ce fp.jc_cx (post_value_type ce (Subscript a e1 e2)) sa sb ee tv vv u) /\
           (~expr_has_effect (Subscript a e1 e2) ==> vv_storage_live fp.jc_cx vv ee u) /\
           (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
           (post_value_type ce (Subscript a e1 e2) <> NoneT /\
            ~is_word_type (post_value_type ce (Subscript a e1 e2)) /\
            ~is_bytestring_type (post_value_type ce (Subscript a e1 e2)) /\
            (case vv of StackValue _ _ => T
                      | LocatedValue _ p => p.ptr_location = LocMemory) ==>
            !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript a e1 e2)) =
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
