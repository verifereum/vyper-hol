(* A stack operand or a non-word memory pointer unwraps at the same state. *)
Theory createCtorUnwrapIdentityArrivalMods
Ancestors
  createCtorUnwrapIdentityArrival createExprSizeExitDefsMods
  createCtorSegmentArrival exprSimVVFrame exprSimUnwrapProps exprSimUnwrap
  exprSimWordArgs exprSimMemDefs fragGasOriginPtr bodyPtrDefs loweringPosts
  exprLowering compileEnv context vyperStorageFootprint relation

Theorem ctor_unwrap_identity_arrival_mods:
  ~is_word_type (post_value_type cenv e) /\
  ((?ann op0. vv = StackValue ann op0) \/
   (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory /\
                                      ~is_word_type ann)) /\
  sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G s) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn ==>
  sc = sb /\ op = vv_operand vv /\
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                  sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                  i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s s /\
  ?v. read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK s, G, tn) /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op s /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) s /\
    vv_at cenv cx (post_value_type cenv e) sa sm ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) s /\
    expr_store_bound cx (post_value_type cenv e) v op s /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
    ptr_buf_ok cenv e op G s /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op s = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    wb_frame cenv ee ee sb s s /\
    ghost_kept_at lo cenv ee sb G tn s G tn
Proof
  cheat
QED
