(* unwrap_value's storage and transient aggregates on one joint path: a
   fresh buffer, then one load and store or the word-copy loop. *)
Theory bodyFullUnwrapSlot
Ancestors
  exprPtrUnwrapMarked exprSimMemUnwrap fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprLowering compileEnv context

(* A storage or transient aggregate is copied into a fresh buffer. *)
Theorem unwrap_slot_copy_origin_ptr:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  cheat
QED
