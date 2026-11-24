(* The materialization source is interpreted at the endpoint of the
   ordinary unwrap, not at the endpoint of a second execution. *)
Theory createCtorMaterializePhysicalMods
Ancestors
  createCtorMaterializePhysical createExprSizeExitDefsMods
  assignEffectfulIndexPhysical bodyMemSnapshotSourceLocation
  immutableDeployPhysicalSource aggregateEvaluatedLayout bodyFullStructLitInputs
  exprBodyPreProps exprSimHyps exprLowering context loweringPosts bodyPtrDefs
  assignTuplePtrCopyLen[qualified] loweringStateRelDefs vyperState
  vyperTypeExprSoundness valueCopyBytes finite_map pred_set

Theorem ctor_materialize_unwrap_retag_mods:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv a /\
  ~is_word_type (lowered_value_type ce e) /\
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) mid = (op,su) ==>
  unwrap_value ce vv mid = (op,su) /\
  ~is_word_type (post_value_type ce e) /\
  ?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
        (!val. read_result cx tv ee = (INL val,ee) ==> value_has_type rty val) /\
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rty /\
        type_memory_size rty < 2 ** 64
Proof
  cheat
QED

Theorem ctor_materialize_unwrap_physical_mods:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  expr_post_mods H ctx func ce cx e es sa su s0 ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gz tz z /\
  ptr_buf_ok ce e op Gz z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  wb_frame ce ee ee mid a z /\
  ghost_kept_at lo ce ee mid Ga ta a Gz tz ==>
  (?stv sw.
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
     value_has_type stv v /\ val_wf stv v /\
     type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
     eval_operand op z = SOME sw /\ op_taint tz op = {} /\
     (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
            val_in_memory stv v (w2n sw) mem) /\
     (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= z.vs_alloca_next) /\
     (0 < type_memory_size stv ==>
      ?src. op = Var src /\ ptr_covers Gz tz src z (type_memory_size stv))) /\
  (!p w aid b n.
     not_fresh_at mid p /\ lookup_var p a = SOME w /\ ptr_covers Ga ta p a n /\
     FLOOKUP a.vs_allocas aid = SOME (b,n) /\ aid < mid.cs_next_id /\
     (!id base len. local_region ce ee.scopes a id base len ==>
                    regions_disjoint b n base len) ==>
     lookup_var p z = SOME w /\ ptr_covers Gz tz p z n /\
     FLOOKUP Gz p = FLOOKUP Ga p /\ op_taint tz (Var p) = op_taint ta (Var p) /\
     FLOOKUP z.vs_allocas aid = SOME (b,n) /\
     mem_bytes_at b n z.vs_memory = mem_bytes_at b n a.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tz.t_mem ==> i IN ta.t_mem))
Proof
  cheat
QED
