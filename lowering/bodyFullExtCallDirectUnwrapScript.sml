Theory bodyFullExtCallDirectUnwrap
Ancestors
  bodyFullExtCallDelayedSlot abiEncodeValuesSource
  exprSafeOperand exprOperandVar fragGasOriginPtrDead freshWrites assignTuplePtrCopyLen localPtrsProps
  exprLoweringProps loweringPosts loweringStateRelDefs bodyPtrDefs
  compileEnv exprLowering context vyperValue vyperStorageFootprint
  fragExec fragGasOriginPtr ptrDiscipline venomState venomInst words finite_map
Libs pureFrameLib

(* The row consumes the original saved value. A code-free unwrap retains
   its source allocation interval, while a copy owns its new interval. *)
Theorem extcall_direct_saved_unwrap_from_side:
  saved_restore_copy_laws ctx fn explicit su sb P /\
  (!a u. ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==> P a a u u) /\
  ty = lowered_value_type ce e /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ compile_expr ce (expr_type e) e si = (saved,sm) /\
        (!x. p.ptr_operand = Var x ==> not_fresh_at sm x))) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  unwrap_value ce saved su = (src,sb) /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx ty raw saved ee t /\
  ptr_vv_ok cx ty raw saved ee G tn t /\
  vv_store_bound cx ty ty ee raw saved t /\
  ((case saved of
     StackValue tag op0 => ~is_word_type ty
   | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G t) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  vv_at ce cx ty si ss ee raw saved t /\
  (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z G' tn'.
    P su sb t z /\
    pure_frame ce fn ee su t z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G' tn' z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src G' z) /\
    (~is_word_type ty ==> !w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn')) /\
    (~is_word_type ty ==>
      ((src = vv_operand saved /\ sb = su /\ expr_val_at ce cx ty si ss ee v src z) \/
       expr_val_at ce cx ty su sb ee v src z))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all extcall_slot_unwrap_from_side >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`z`,`G'`,`tn'`] strip_assume_tac)) >>
  `!x. src = Var x ==> not_fresh_at sb x` by
    (qpat_assum `unwrap_value ce saved su = (src,sb)` mp_tac >>
     disch_tac >> drule_at (Pos hd) compiler_unwrap_value_var >>
     Cases_on `saved` >> gvs[vv_operand_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `~is_word_type ty ==>
      (src = vv_operand saved /\ sb = su /\ expr_val_at ce cx ty si ss ee v src z) \/
      expr_val_at ce cx ty su sb ee v src z` by
    (disch_tac >>
     Cases_on `(?p. saved = LocatedValue ty p /\ p.ptr_location <> LocMemory)`
     >- (disj2_tac >> metis_tac[]) >>
     `z = t` by metis_tac[] >>
     irule abi_encode_values_unwrap_source_cuts >>
     metis_tac[]) >>
  qexistsl_tac [`z`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

local
  val unobserved = SIMP_RULE bool_ss [saved_restore_copy_laws_true]
    (Q.INST [`P` |-> `\a b u z. T`] extcall_direct_saved_unwrap_from_side)
in
Theorem extcall_direct_saved_unwrap_pure:
  ^(concl unobserved)
Proof
  ACCEPT_TAC unobserved
QED
end

Theorem extcall_direct_saved_unwrap =
  pureFrameLib.drop_frame extcall_direct_saved_unwrap_pure

(* The unwrap preserves live pointers issued before its input cut.
   Prefer the provenance frame of that cut for the new head and tail
   addresses, which come after the original argument snapshots. *)
Theorem extcall_direct_unwrap_pointer:
  (!x. not_fresh_at st x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  not_fresh_at st p /\ eval_operand (Var p) s = SOME w /\ ptr_covers G tn p s n ==>
  eval_operand (Var p) t = SOME w /\ ptr_covers G' tn' p t n
Proof
  strip_tac >>
  qpat_assum `!x. not_fresh_at st x ==> _` (drule_then strip_assume_tac) >>
  fs[eval_operand_def] >> metis_tac[ptr_covers_lookup_frame]
QED

Theorem extcall_direct_unwrap_operand:
  (!x. not_fresh_at st x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ (!x. op = Var x ==> not_fresh_at st x) ==>
  eval_operand op t = eval_operand op s /\ op_taint tn' op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_taint_def] >>
  metis_tac[op_taint_def]
QED
