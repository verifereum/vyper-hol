(* The common finish boundary of both staged linked ABI payload runs. *)
Theory bodyAbiEncodePayloadLandingMods
Ancestors
  bodyFullPostsMods loweringPosts loweringStateRelDefs bodyPtrDefs
  vyperContext vyperAST venomState venomMemDefs finite_map pred_set list pair words

(* Fixed compiler/ALLOCA site facts and the static storage-size bounds
   are supplied separately to the finish rule. *)
Definition abi_encode_payload_landing_mods_def[nocompute]:
  abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
    ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
    (body_end,aid,p,cap,root,len) (bytes,limit,q,Gq,tq) <=>
    let prefix = abi_encode_method_id_bytes mid;
        e = TypeBuiltin ann (AbiEncode ensure mid) target args
    in
    ann = BaseT (BytesT (Dynamic limit)) /\
    evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
      INL (BytesV (prefix ++ bytes)) /\
    LENGTH (prefix ++ bytes) <= limit /\ 32 + LENGTH (prefix ++ bytes) <= cap /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (pre,Gpre,tnpre) [] (OK q,Gq,tq)) /\
    alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    ~q.vs_halted /\ q.vs_current_bb = body_end.cs_current_bb /\
    q.vs_inst_idx = LENGTH body_end.cs_current_insts /\
    allocas_from lo q /\ alloca_inv q /\ lo <= p /\ q.vs_alloca_next < dimword (:256) /\
    eval_operand (Var root) q = SOME (n2w p) /\ ptr_covers Gq tq root q cap /\
    eval_operand len q = SOME (n2w (LENGTH bytes)) /\ op_taint tq len = {} /\
    not_fresh_at body_end root /\ (!x. len = Var x ==> not_fresh_at body_end x) /\
    FLOOKUP q.vs_allocas aid = SOME (p,cap) /\
    not_local_ptr ce ee.scopes root /\ local_ptrs_rel func ce ee.scopes q /\
    local_ptrs_reserved ce sa /\ sa.cs_next_var <= body_end.cs_next_var /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x) /\
    return_buf_frame d ce body_end q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ wb_frame ce es ee sa s0 q /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 q) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee q /\ immutable_frame_mods func ce cx ee q /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gq tq q) /\
    mem_bytes_at (p+32) (LENGTH prefix) q.vs_memory = prefix /\
    mem_bytes_at (p+32+LENGTH prefix) (LENGTH bytes) q.vs_memory = bytes /\
    (!i. p+32 <= i /\ i < p+32+LENGTH prefix+LENGTH bytes ==> i NOTIN tq.t_mem)
End

Theorem abi_encode_payload_landing_action_path_mods:
  abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
    ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
    (body_end,aid,p,cap,root,len) (bytes,limit,q,Gq,tq) ==>
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
    INL (BytesV (abi_encode_method_id_bytes mid ++ bytes)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (pre,Gpre,tnpre) [] (OK q,Gq,tq))
Proof
  simp_tac bool_ss [abi_encode_payload_landing_mods_def, LET_THM] >>
  strip_tac >> simp_tac bool_ss [] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
