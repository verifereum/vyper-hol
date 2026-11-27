(* Full linked RawCreate bytecode cut: read, snapshot, header, and continuation. *)
Theory bodyCreateRawBytecodeMods
Ancestors
  bodyCreateRawHeadMods bodyCreateRawSnapshotMods bodyCreateRawHeaderMods
  bodyAugGuardedPrefixMods bodyFullPredsMods bodyFullPostsMods
  bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs bodyMemoryDefs loweringPosts
  gasOutcomeFullMods exprSimHyps exprSimMemorySource exprLoweringProps
  compileEnv gasShadowState gasShadow vyperStorageFootprint vyperState
  vyperInterpreter fragGasOriginPtr contextRawReachable allocaHistory
  valueEncoding words arithmetic list
Libs monadsyntax

Theorem raw_create_bytecode_cut_mods:
  body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env code es /\
  body_expr_full_ok_mods mods exps cx code /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_expr (gas_shadow_env T cenv) (expr_type code) (gas_shadow_expr code) sh = (vv,sha) /\
  compile_create_snapshot cenv vv (lowered_value_type cenv code) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap;Lit 32w] c = (data,sb) /\
  gas_shadow_state sa sh /\ gas_shadow_state a sha /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code sh sha shadow_func /\
  fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c sb func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx code) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!bs ee z Gz tz marks src owner pbase cap site.
    LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (BytesV bs),ee with gas_obs := tail)) /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    storage_trace_domain cx st0 ee.storage_trace /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\
    return_buf_frame d cenv sb z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\
      stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ site.inst_id < sb.cs_next_id /\
    FLOOKUP z.vs_allocas site.inst_id = SOME (pbase,cap) /\
    pbase + cap <= z.vs_alloca_next /\ pbase + cap < dimword (:256) /\ 32 + LENGTH bs <= cap /\
    data = Var src /\ not_fresh_at sb src /\ lookup_var src z = SOME (n2w (pbase + 32)) /\
    ptr_covers Gz tz src z (LENGTH bs) /\ op_taint tz (Var src) = {} /\
    (!x. len = Var x ==> not_fresh_at sb x) /\ (!l. len <> Label l) /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE /\
    read_memory (pbase + 32) (LENGTH bs) z = bs /\
    (!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tz.t_mem) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next (BytesV bs)) (ee,z,Gz,tz) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx code) (read_result cx)) next)
    (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac raw_create_head_read_cut_mods >>
  (impl_tac >- (
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    qx_genl_tac [`marks`,`raw`,`v`,`ee`,`t`,`G1`,`tn1`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    suspend "reached")) >>
  disch_then ACCEPT_TAC
QED

Resume raw_create_bytecode_cut_mods[reached]:
  mp_tac raw_create_reached_snapshot_mods >>
  (impl_tac >- (
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    gen_tac >> disch_tac >>
    qpat_assum `!H. _ ==> (vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then (qx_choosel_then [`bs`,`k`,`cap`,`owner`,`pbase`,`site`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx es s /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac raw_create_header_lands_mods >>
  (impl_tac >- (
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    gen_tac >> disch_tac >>
    qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\ _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`root`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  irule augassign_zero_prefix_guarded_mods >>
  conj_tac >-
    (qpat_assum `!v. storage_trace_frame (next v)` (qspec_then `BytesV bs` ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gz`,`z`,`tz`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!bs ee z Gz tz marks src owner pbase cap site. _ ==> _`
    (qspecl_then [`bs`,`ee`,`z`,`Gz`,`tz`,`marks`,`root`,`owner`,`pbase`,`cap`,`site`] mp_tac) >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then ACCEPT_TAC
QED

Finalise raw_create_bytecode_cut_mods
