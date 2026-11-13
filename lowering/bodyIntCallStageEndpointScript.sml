(* The arguments of an internal call, staged one at a time as Vyper
   0.5.0b1 lowers them: each argument's producer runs, then the argument
   is staged at once, a word on the stack, any other value copied into a
   fresh buffer of the callee's parameter type. *)
Theory bodyIntCallStageEndpoint
Ancestors
  bodyIntCallStageList bodyIntCallStageOwned bodyIntCallStageTransport
  bodyIntCallHeldArgs exprSimWordArgs exprLoweringProps fragGasFocus
  context exprLowering compileEnv bodyIntCallJointContract
  bodyIntCallFamCallIntAllocatedStage

(* ML abbreviations only, as in bodyIntCallFamCallIntStageInterface:
   staged argument i, at type ty with flag flag, value v and operand op, in
   state s, for the staging code from start to current. *)
val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;

val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

(* RESTATED (train 17): 0.5.0b1 per-argument staging.  Replaces the batch
   endpoints over held arguments (intcall_stage_args_endpoint and its
   distinct/return variants): ops are the INVOKE's argument operands, vs the
   source values.  Restated again (argon's ruling): no freshness premise on
   t's allocations, since a loop re-enters the same ALLOCAs; instead the
   distinct memory arguments' buffers are pairwise disjoint. *)
Theorem intcall_stage_args_outcome:
  !args flags tys ce env sa ops sb es fp t.
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  (!e. MEM e args ==> intcall_expr_producer fp e /\
     supportedExprs$supported_expr fp.jc_tops e /\
     calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  (!e ee. MEM e args /\ expr_sim_inv ce fp.jc_cx env ee ==>
     expr_body_pre ce fp.jc_cx env e ee) /\
  LENGTH args <= LENGTH flags /\ LENGTH tys = LENGTH args /\
  (!i. i < LENGTH args ==>
     (EL i flags ==> is_word_type (EL i tys)) /\
     type_widens_to (get_tenv fp.jc_cx) (expr_type (EL i args)) (EL i tys) /\
     ?dtv. evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME dtv /\
       type_memory_bytes ce (EL i tys) = type_memory_size dtv /\
       MAX 32 (type_memory_size dtv) + 64 < dimword (:256)) /\
  compile_stage_intcall_args compile_expr ce args flags tys sa = (ops,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,t)
    (\res ee u. ?vs. res = INL vs /\
       ^completed_prefix fp.jc_cx sa sb tys (TAKE (LENGTH args) flags) vs ops u /\
       (!i j tv_i tv_j w_i w_j.
          i < LENGTH args /\ j < LENGTH args /\ i <> j /\
          ~EL i flags /\ ~EL j flags /\
          evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv_i /\
          evaluate_type (get_tenv fp.jc_cx) (EL j tys) = SOME tv_j /\
          eval_operand (EL i ops) u = SOME w_i /\
          eval_operand (EL j ops) u = SOME w_j ==>
          regions_disjoint (w2n w_i) (type_memory_size tv_i)
            (w2n w_j) (type_memory_size tv_j)) /\
       intcall_expr_cont fp ce env es sa t ee sb u /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes)
    (\res ee r. expr_exit res r)
Proof
  cheat
QED
