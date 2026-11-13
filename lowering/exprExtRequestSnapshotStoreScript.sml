(* Public snapshot prefix adapter: discharge the independently proved store fold. *)
Theory exprExtRequestSnapshotStore
Ancestors
  exprExtRequestSnapshotStoreFold exprExtRequestSnapshotStorePrefix

Theorem extrequest_snapshot_tuple_prefix_endpoint:
  EVERY (extrequest_snapshot_cell ctx func ce cx ee sa s) cells /\
  vals = MAP (\(vv,ty,tv,v). vv) cells /\ vals <> [] /\
  tys = MAP (\(vv,ty,tv,v). ty) cells /\
  tvs = MAP (\(vv,ty,tv,v). tv) cells /\
  vs = MAP (\(vv,ty,tv,v). v) cells /\
  sz = SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) /\
  assignable_type (get_tenv cx) (TupleT tys) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  type_memory_size (TupleTV tvs) <= sz /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) /\
  extrequest_compile_prefix ce vals tys sz abisz (ce.ce_method_id fname ats)
    retsz ei sa = ((bufop,offset,len),sp) /\
  32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <=
    MAX abisz retsz + 32 /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ ee.gas_obs = [] /\
  sz < dimword (:256) /\ MAX abisz retsz + 32 < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t (w:bytes32). gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    eval_operand len t = SOME
      (n2w (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av))) /\
    eval_operand offset t = SOME (n2w (w2n w+28)) /\
    read_memory (w2n w+28)
      (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av)) t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
        enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,MAX abisz retsz+32) /\
    w2n w + retsz < dimword (:256) /\
    local_ptrs_reserved ce sp /\ safe_operand sp len /\ safe_operand sp offset /\
    eval_operand bufop t = SOME w /\
    (!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
       lookup_var x t = SOME z) /\
    (!name p k. local_region ce ee.scopes s name p k ==>
       mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (ce.ce_is_ctor ==> !name tv v p.
       FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
       mem_bytes_at p (type_memory_size tv) t.vs_memory =
         mem_bytes_at p (type_memory_size tv) s.vs_memory) /\
    (!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       FLOOKUP t.vs_allocas aid = SOME (p,k)) /\
    extrequest_history_frame ce cx ee sa s ee sp t /\
    wb_frame ce ee ee sa s t /\ safe_operand sp bufop
Proof
  mp_tac extrequest_snapshot_tuple_prefix_from_store >>
  simp[extrequest_snapshot_store_fold]
QED
