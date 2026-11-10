(* Nested internal call, return side: from the INVOKE, with the callee's
   run as packaging gives it, to the producer's normal certificate for the
   call (intcall_expr_producer's post at the call's entry s0, es0, sa). *)
Theory bodyIntCallFamCallIntReturn
Ancestors
  bodyIntCallJointContract bodyIntCallSeamDefs
  bodyIntCallFamCallIntReturnFrame
  vyperPlaceWriteSoundness vyperImmutableMetadataFrame
  exprLoweringProps stmtSimProps bodyMemoryDefs freshWrites
Libs
  monadsyntax

(* Resource transport uses immutable metadata, not equality of values: a
   constructor call may initialize an immutable without changing its type. *)
Theorem intcall_expr_res_metadata_frame:
  intcall_frame_ok fp /\
  intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x u = SOME w) /\
  (!n p k. local_region ce ee.scopes u n p k ==>
     local_region ce es.scopes s n p k) /\
  immutable_metadata_frame es ee ==>
  intcall_expr_res fp ce env ee sb u
Proof
  strip_tac >>
  qpat_x_assum `intcall_expr_res _ _ _ _ _ _` mp_tac >>
  simp[intcall_expr_res_def] >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `fp.jc_reserved fp.jc_rpc` by fs[intcall_frame_ok_def] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  drule immutable_metadata_frame_value_lookup >>
  disch_then (qspecl_then [`fp.jc_cx.txn.target`,`ce.ce_module`,`nm`,`tv`,`iv`]
    mp_tac) >>
  Cases_on `ALOOKUP ee.immutables fp.jc_cx.txn.target` >>
  Cases_on `ALOOKUP es.immutables fp.jc_cx.txn.target` >>
  gvs[vyperStateTheory.get_source_immutables_def] >> metis_tac[]
QED

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
