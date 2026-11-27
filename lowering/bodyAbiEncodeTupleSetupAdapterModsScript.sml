(* Pass the actual ready buffer and caller frames to the wrapped landing. *)
Theory bodyAbiEncodeTupleSetupAdapterMods
Ancestors
  bodyAbiEncodeTupleLandingMods

Theorem abi_encode_tuple_from_setup_mods:
  mods = ce.ce_modules /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
      args svs sa st es s0 G0 tn0 H (INL vs : value list + 'err) ee G tn s) /\
  compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) svs
    (MAP (lowered_value_type ce) args) (Var dp) ready = (len,body_end) /\
  fn_has_code ready body_end func /\ fn_inst_ids_distinct func /\
  prefix = abi_encode_method_id_bytes mid /\ LENGTH prefix = k /\
  cap = 32 + 32 * word_size (abi_size_bound ce.ce_struct_fields
    (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
     else TupleT (MAP (lowered_value_type ce) args)) + k) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  st.cs_next_id < ready.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  lo <= p /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
       FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  wb_frame ce es ee sa s0 pre /\
  (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp (32+k) prefix ready pre Gpre tnpre ==>
  ?bytes limit q Gq tq.
    abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
      ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
      (body_end,st.cs_next_id,p,cap,root,len) (bytes,limit,q,Gq,tq)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cap = 32 + 32 * word_size (abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) args)) + k)` by
    (qpat_assum `cap = _` mp_tac >>
     qpat_assum `~(LENGTH args = 1 /\ ~ensure)` (fn th => simp_tac bool_ss [th])) >>
  `k = LENGTH prefix` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_at (Pat `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_encode_tuple_landing_mods >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env args svs sa st es s0 G0 tn0
      H _ ee G tn s`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_payload _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `_ = abi_encode_method_id_bytes _`)) >>
  disch_then irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
