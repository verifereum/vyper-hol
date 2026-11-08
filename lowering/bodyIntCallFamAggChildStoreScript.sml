(* Seam 2 joint induction, the shared leaf of the literal families: one
   literal child evaluated, read, and stored at its destination offset in
   the aggregate's root allocation, with the root's other bytes kept. *)
Theory bodyIntCallFamAggChildStore
Ancestors
  bodyIntCallJointContract loweringPosts exprSimWordArgs
  compileEnv stmtSimProps bodyMemoryDefs freshWrites
  placeMemoryCopyEffect exprSimCopy bodyIntCallCopySharpDynamic
  venomState intCallFrame context emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomMemProps
  bodyIntCallStorePost bodyIntCallProtectedAlloc exprSimAlloc
  placeMemoryPrimitiveForward instIdxIndep exprSimProps exprSimUnwrap
  exprSimAggregateChildren bodyIntCallAggregateStoreFrame
  bodyIntCallCompletedModes intCallStep exprSimSend
  bodyIntCallWidenedChildStore typedMemoryCopy

Theorem intcall_counted_child_store:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\
  expr_body_pre ce fp.jc_cx env e es /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  intcall_joint_res fp ce env es0 s0c s0 /\
  intcall_expr_cont fp ce env es0 s0c s0 es si t /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  s0c.cs_next_var <= si.cs_next_var /\ s0c.cs_next_id <= si.cs_next_id /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (post_value_type ce e) su = ((),sb) /\
  fn_has_code si sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
  fn_has_code sn su fp.jc_func /\ fn_has_code su sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  type_widens_to env.type_defs (expr_type e) dty /\
  type_widens_to (get_tenv fp.jc_cx) (post_value_type ce e) dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME stv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) /\
  s0c.cs_next_id <= inst.inst_id /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf t = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at si x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + off + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes t name a n ==>
     regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==>
     regions_disjoint b k a n) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?v. res = INL v /\
       val_in_memory dtv v (w2n bw + off) u.vs_memory /\
       intcall_expr_cont fp ce env es0 s0c s0 ee sb u /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
       eval_operand buf u = SOME bw /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       (!name a n. local_region ce ee.scopes u name a n ==>
          regions_disjoint b k a n) /\
       (!a n. b <= a /\ a+n <= b+k /\
          (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size dtv <= a) ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n t.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  cheat
QED
