(* Join the source/layout and reached-topic packets before payload allocation. *)
Theory bodyLogSuccessInputsMods
Ancestors
  bodyLogSuccessSourceLayoutMods bodyLogSuccessTopicsMods
  bodyAbiEncodePackedPostMods vyperStorageFootprint

Theorem log_success_inputs_mods:
  let tenv = get_tenv cx in
  let atys = MAP (lowered_value_type ce) args in
  let rows = SND (split_log_ops (ZIP (saved,atys)) flags) in
  let ats = vyper_to_abi_types tenv (log_non_indexed_types flags atys) in
  let hl = head_lengths ats 0 in
  let cap = abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) in
  let topic_rows = FST (split_log_ops (ZIP (saved,atys)) flags) in
  contract_inv mods exps ctx ce cx /\ contract_namespaces_ok dep mods /\
  stmt_exprs_ok ce (Log id args) /\
  ce.ce_event_info (nsid_to_string id) = SOME (h,dtys,flags) /\
  lookup_event_metadata tenv cx.sources cx.txn.target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL (\dty e. event_arg_compatible dty (expr_type e)) dtys args /\
  EVERY (assignable_type tenv) dtys /\
  EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty)
    (ZIP (dtys,flags)) /\
  expr_sim_inv_mods mods ce cx env entry /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e entry) args /\
  eval_exprs cx args entry = (INL vs,mid) /\
  LENGTH (FILTER I flags) <= 3 /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    abi_encode_packed_post_mods ce.ce_modules DF lo d ctx func ce cx env
      args saved sa sm es s0 G0 tn0 H (INL vs) mid G1 tn1 t /\
    (!bw capacity. d = SOME (bw,capacity) ==>
      allocas_from (w2n bw + capacity) t)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo ce cx) /\
  ci_mono sa sm /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_log_saved_topics ce topic_rows sm = (ops,se) /\
  fn_has_code sm se func ==>
  ?topics avs u Gu tu.
    let bytes = enc (Tuple ats) (ListV avs) in
    LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\
    LENGTH flags = LENGTH vs /\
    encode_indexed_event_topics flags atys vs = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags atys)
      (log_non_indexed_values flags vs) = SOME avs /\
    encode_source_event tenv cx.sources cx.txn.target id vs =
      SOME <|logger := cx.txn.target; topics := n2w h::topics;
             data := bytes|> /\
    EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (atys,flags)) /\
    (!j. j < LENGTH flags ==>
      expr_body_pre_mods mods ce cx env (EL j args) entry /\
      ?rt. evaluate_type tenv (EL j atys) = SOME rt /\
        value_has_type rt (EL j vs) /\
        type_memory_bytes ce (EL j atys) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!ty rt. evaluate_type tenv ty = SOME rt ==>
      type_memory_bytes ce ty = type_memory_size rt) /\
    MAP SND rows = log_non_indexed_types flags atys /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    (rows <> [] ==> LENGTH bytes <= cap /\ cap < dimword (:256)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = se.cs_current_bb /\
    u.vs_inst_idx = LENGTH se.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    sm.cs_next_id <= se.cs_next_id /\ sm.cs_next_var <= se.cs_next_var /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
    local_ptrs_reserved ce se /\ return_buf_frame d ce se u /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func ce cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u /\
      immutable_frame_mods func ce cx mid u) /\
    MAP FDOM mid.scopes = MAP FDOM es.scopes /\
    wb_frame ce es mid sa s0 u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\
    EVERY (safe_operand se) (Lit (n2w h)::ops) /\
    EVERY (\op. op_taint tu op = {}) (Lit (n2w h)::ops) /\
    eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics) /\
    LENGTH (Lit (n2w h)::ops) < dimword (:256) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      LIST_REL (\(e,sv) v. ?si sm0 ss vv copy.
        abi_encode_saved_row_mods lo ce cx sa se e sv v si sm0 ss vv copy
          H mid Gu tu u)
        (select_log_args F flags (ZIP (args,saved)))
        (select_log_args F flags vs))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  `LENGTH saved = LENGTH args` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     rewrite_tac[abi_encode_packed_post_mods_def] >>
     disch_then (qx_choose_then `values` (ACCEPT_TAC o el 2 o CONJUNCTS))) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] log_success_source_layout_mods)) >>
  disch_then (qx_choosel_then [`topics`,`avs`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] log_success_topics_mods)) >>
  disch_then (qspecl_then [`h`,`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`topics`,`avs`,`u`,`Gu`,`tu`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
