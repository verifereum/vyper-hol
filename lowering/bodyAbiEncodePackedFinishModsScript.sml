(* Finish either staged payload at the point actually reached by its run. *)
Theory bodyAbiEncodePackedFinishMods
Ancestors
  bodyAbiEncodePayloadLandingMods bodyAbiEncodeFinishMods fragGasOriginPtrLoop
  abiBuiltinEncodeCode valueEncodingDefs exprLoweringProps bodyFullPostsMods
  loweringPosts loweringStateRelDefs bodyPtrDefs vyperAST venomState venomMemDefs

Theorem abi_encode_packed_finish_mods:
  let prefix = abi_encode_method_id_bytes mid;
      e = TypeBuiltin ann (AbiEncode ensure mid) target args;
      payload = prefix ++ bytes;
      vv = LocatedValue ann (mk_ptr (Var root) LocMemory)
  in
  abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
    ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
    (a,aid,p,cap,root,lenop) (bytes,limit,s,G,tn) /\
  abi_builtin_encode_finish (Var root) lenop (LENGTH prefix) a = ((),sb) /\
  fn_has_code a sb func /\ fn_inst_ids_distinct func /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  sa.cs_next_id <= aid /\ aid < a.cs_next_id /\
  val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV payload) <= cap /\
  type_memory_bytes ce (lowered_value_type ce e) <= cap ==>
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
    INL (BytesV payload) /\
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (pre,Gpre,tnpre) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d ce sb t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p mem) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee (Value (BytesV payload)) vv t /\
    ptr_vv_ok cx (post_value_type ce e) (Value (BytesV payload)) vv ee Gf tf t /\
    ptr_buf_ok ce e (Var root) Gf t /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value (BytesV payload)) vv t /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf t)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qhdtm_x_assum `abi_encode_payload_landing_mods`
    (strip_assume_tac o SIMP_RULE bool_ss [abi_encode_payload_landing_mods_def, LET_THM]) >>
  qpat_x_assum `ann = BaseT _` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (SIMP_RULE bool_ss [LET_THM, expr_type_def] abi_encode_bytes_finish_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  conj_tac >> first_x_assum irule
QED
