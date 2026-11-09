(* Nested internal call, return side: from the INVOKE, with the callee's
   run as packaging gives it, to the producer's normal certificate for the
   call (intcall_expr_producer's post at the call's entry s0, es0, sa). *)
Theory bodyIntCallFamCallIntReturn
Ancestors
  bodyIntCallJointContract bodyIntCallSeamDefs
Libs
  monadsyntax

Theorem intcall_nested_return:
  !fp ce env ann name es dflt ty sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t rc rbs pvs.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    expr_body_pre ce fp.jc_cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    supportedExprs$supported_expr fp.jc_tops (Call ann (IntCall (NONE,name)) es dflt) /\
    lookup_callable_function fp.jc_cx.in_deploy name fp.jc_tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) fp.jc_tops /\
    compile_expr ce ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es0 sa s0 /\
    intcall_entry fp.jc_tops fp.jc_ctx fp.jc_func ce fp.jc_cx env name es
      sa sb vv s0 es0 (mut,args,ret,ss,rr) prev penv rtv es1 t /\
    intcall_expr_res fp ce env (es1 with scopes := prev) sa t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ce.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (fp.jc_ctx,fp.jc_func) t callee entered /\
       lookup_block t.vs_current_bb fp.jc_func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,callee)
         (intcall_callee_src fp.jc_cx name ss) (es1,entered) (\res ee r. F)
         (intcall_callee_exit fp.jc_func ce fp.jc_cx rtv rc
            (if rc = 0 /\
                ce.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
             then SOME (HD argv) else NONE)
            sa.cs_next_id sb.cs_next_id t)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (intcall_rest fp.jc_cx name mut ss prev rtv) (es1,t)
      (\res ee u. ?tv. res = INL tv /\
         vv_holds ce fp.jc_cx
           (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) tv vv ee u /\
         vv_at ce fp.jc_cx
           (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt))
           sa sb ee tv vv u /\
         (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt) <>
            expr_type (Call ann (IntCall (NONE,name)) es dflt) ==>
          vv_own ce fp.jc_cx
            (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt))
            sa sb ee tv vv u) /\
         (~expr_has_effect (Call ann (IntCall (NONE,name)) es dflt) ==>
          vv_storage_live fp.jc_cx vv ee u) /\
         (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
         (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt) <> NoneT /\
          ~is_word_type
             (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
          ~is_bytestring_type
             (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
          (case vv of StackValue _ _ => T
                    | LocatedValue _ p => p.ptr_location = LocMemory) ==>
          !tv'. evaluate_type (get_tenv fp.jc_cx)
                  (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) =
                  SOME tv' ==>
            ?w a k. eval_operand (vv_operand vv) u = SOME w /\
              a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
              a + k < dimword (:256) /\
              (fp.jc_lo <= a \/
               ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
         intcall_expr_cont fp ce env es0 sa s0 ee sb u)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED
