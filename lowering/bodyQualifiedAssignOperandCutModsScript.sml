(* The delayed unwrap lands at one common store cut for raw values and
   snapshots. The empty-mark path may be reflexive. The source operand is
   still in its original layout; widening belongs to the store suffix. *)
Theory bodyQualifiedAssignOperandCutMods
Ancestors
  bodyWriteTargetStageMods bodyFullShadowBodyInv loweringPosts
  loweringStateRelDefs bodyPtrDefs exprLowering compileEnv
  fragGasOriginPtr fragExec context vyperStorageFootprint venomState
  valueTypingMemoryProps words finite_map list

Definition qualified_assign_operand_cut_mods_def[nocompute]:
  qualified_assign_operand_cut_mods (DF,lo,d,explicit,ctx,func,PG)
    cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
    (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) <=>
    unwrap_value cenv vv st = (op,su) /\
    fn_has_code st su func /\ fn_has_code su sb func /\
    fn_inst_ids_distinct func /\
    sa.cs_next_var <= st.cs_next_var /\ st.cs_next_var <= su.cs_next_var /\
    sa.cs_next_id <= st.cs_next_id /\ st.cs_next_id <= su.cs_next_id /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (z,Gz,tz) [] (OK s,G,tn)) /\
    ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
    s.vs_inst_idx = LENGTH su.cs_current_insts /\
    z.vs_alloca_next <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    target_ptr_ok cenv (PlaceR p) dst G tn s /\
    write_target_location_mods cenv cx bt ee (PlaceR p) (Type dty) dst G s /\
    (!x. FST dst = Var x ==> not_fresh_at su x) /\
    eval_operand (FST dst) s = eval_operand (FST dst) z /\
    op_prov G (FST dst) = op_prov Gz (FST dst) /\
    op_taint tn (FST dst) = op_taint tz (FST dst) /\
    wb_frame cenv es ee sa s0 s /\ alloca_frame cenv es sa s0 cenv ee s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    local_ptrs_reserved cenv su /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
    return_buf_frame d cenv su s /\ return_buf_sep d cenv ee s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
      storage_well_formed_on cx ee (FST H)) /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    (if is_word_type (expr_type e) then
       ?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
         value_has_type rt v /\ eval_operand op s = SOME (typed_val_to_w256 rt v) /\
         op_taint tn op = {} /\ op_prov G op = NONE
     else
       ?rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
         value_has_type rt v /\ type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
         eval_operand op s = SOME w /\ op_taint tn op = {} /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
         w2n w + type_memory_size rt < dimword (:256) /\
         (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
         (0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers G tn x s (type_memory_size rt)) /\
         (~is_bytestring_type (lowered_value_type cenv e) ==>
           ?start. expr_val_at cenv cx (lowered_value_type cenv e) start su ee v op s))
End
