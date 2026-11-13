(* Record frames at the very same counted dynamic-storage endpoint. *)
Theory placeStorageDynamicFrame
Ancestors
  placeStorageDynamicEndpoint

Theorem dynamic_storage_normalized_endpoint_frame:
  compile_dynarray_to_storage src dst ((type_memory_bytes ce et+31) DIV 32)
    (type_memory_bytes ce et) tr sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s /\ alloca_history fn s /\
  evaluate_type tenv (ArrayT et (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  type_memory_bytes ce et = type_memory_size tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n p) s.vs_memory /\
  w2n p + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword(:256) /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n d = w2n k+delta /\ w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      stmt_state_rel ctx fn ce cx
        (set_storage cx es tr (apply_writes d writes (get_storage cx es tr))) t /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      t.vs_allocas = s.vs_allocas
Proof
  MATCH_ACCEPT_TAC dynamic_storage_normalized_endpoint_fields
QED
