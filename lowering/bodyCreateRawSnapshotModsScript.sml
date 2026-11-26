(* Join the reached linked RawCreate operand to its actual snapshot landing. *)
Theory bodyCreateRawSnapshotMods
Ancestors
  bodyCreateRawSnapshotSelectMods bodyCreateRawSnapshotFrameMods
  bodyCreateRawMemoryResidualMods bodyCreateRawSlotResidualMods bodyCreateRawCodeResidualMods
  loweringPosts valueEncodingDefs words arithmetic
Libs monadsyntax

val residual_end = ``\u Gu tu.
  typed_copy_state_frame m pbase cap j u /\
  (!x. not_fresh_at m x ==> FLOOKUP Gu x = FLOOKUP Gj x /\
    op_taint tu (Var x) = op_taint tj (Var x)) /\
  (!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
  tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\ tu.t_imm = tj.t_imm /\
  lookup_var owner u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
  mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
  (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
  ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu))``;

Theorem raw_create_reached_snapshot_mods:
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env code es /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_create_snapshot cenv vv (lowered_value_type cenv code) a = (snap,b) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ee.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. eval_expr cx code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,ee with gas_obs := tail)) /\
  read_result cx raw ee = (INL v,ee) /\
  (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  (!H : (bool # bytes32 # type_value) list # num list.
    valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
    vv_store_bound cx (post_value_type cenv code) (lowered_value_type cenv code) ee raw vv t /\
    t.vs_current_bb = a.cs_current_bb /\ t.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
    ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx raw ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1)) ==>
  ?bs k cap owner pbase site u Gu tu.
    v = BytesV bs /\ lowered_value_type cenv code = BaseT (BytesT (Dynamic k)) /\
    LENGTH bs <= k /\ k <= bound /\ LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
    cap = type_memory_bytes cenv (lowered_value_type cenv code) /\ 32 + LENGTH bs <= cap /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ee.gas_obs = [] /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (BytesV bs),ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) /\
    ci_mono sa a /\ wb_frame cenv es ee sa s t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\ s.vs_alloca_next <= t.vs_alloca_next /\
    snap = Var owner /\ MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
    site.inst_id = a.cs_next_id /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ not_fresh_at b owner /\
    FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
    eval_operand snap u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
    pbase+cap < dimword (:256) /\ pbase+cap <= u.vs_alloca_next /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
    wb_frame cenv ee ee a t u /\ ghost_kept_at lo cenv ee a G1 tn1 t Gu tu /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
    return_buf_frame d cenv b u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,Gu,tu))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`] raw_create_snapshot_select_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`bs`,`k`,`cap`,`buf`,`m`,`site`,`owner`,`pbase`,`j`,`Gj`,`tj`]
    (map_every assume_tac o CONJUNCTS)) >>
  `snap = Var owner` by asm_rewrite_tac[] >>
  `FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap)` by asm_rewrite_tac[] >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  qsuff_tac `?u Gu tu. (^residual_end) u Gu tu`
  >- (BETA_TAC >> disch_then (qx_choosel_then [`u`,`Gu`,`tu`]
        (map_every assume_tac o CONJUNCTS)) >> suspend "finish") >>
  BETA_TAC >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- suspend "memory" >>
  Cases_on `?tr. vv_location vv = SOME (slot_loc tr)`
  >- suspend "slot" >>
  suspend "code"
QED

Resume raw_create_reached_snapshot_mods[memory]:
  qpat_assum `vv_location vv = NONE \/ _ ==> ?len l size c. _`
    (drule_then (qx_choosel_then [`len`,`ml`,`cnt`,`mc`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `buf.buf_operand = Var owner` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`k` |-> `bound`, `e` |-> `code`] raw_create_memory_residual_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume raw_create_reached_snapshot_mods[slot]:
  qpat_x_assum `?tr. vv_location vv = SOME (slot_loc tr)` (qx_choose_then `tr` assume_tac) >>
  qpat_assum `!loc. _ ==> ?lab. compile_slot_to_memory _ _ _ loc _ = _`
    (qspec_then `slot_loc tr` mp_tac) >>
  (impl_tac >- (Cases_on `tr` >> fs[slot_loc_def])) >>
  qpat_assum `buf.buf_operand = Var owner` (fn eq =>
    disch_then (qx_choose_then `lab` (assume_tac o PURE_REWRITE_RULE [eq]))) >>
  `!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
          vv_type vv = BaseT (BytesT (Dynamic k))` by
    (gen_tac >> strip_tac >>
     qpat_assum `!loc. _ ==> vv_type vv = _ /\ _`
       (drule_all_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  mp_tac (INST_TYPE [``:'a`` |-> ``:256``] raw_create_slot_residual_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume raw_create_reached_snapshot_mods[code]:
  `vv_location vv = SOME LocCode` by
    (qpat_assum `~(?tr. vv_location vv = SOME (slot_loc tr))` mp_tac >>
     qpat_assum `~(vv_location vv = NONE \/ _)` mp_tac >>
     qpat_assum `vv_location vv <> SOME LocCalldata` mp_tac >>
     Cases_on `vv_location vv` >> simp[NoAsms] >> Cases_on `x` >>
     simp[NoAsms] >> metis_tac[slot_loc_def]) >>
  qpat_assum `vv_location vv = SOME LocCode ==> compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
    (drule_then assume_tac) >>
  qpat_assum `buf.buf_operand = Var owner` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qabbrev_tac `D0 = DF H0` >>
  mp_tac (Q.INST [`G` |-> `G1`, `tn` |-> `tn1`, `H` |-> `H0`, `D` |-> `D0`]
    (INST_TYPE [``:'a`` |-> ``:256``] raw_create_code_residual_mods)) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then ACCEPT_TAC
QED

Resume raw_create_reached_snapshot_mods[finish]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    stmt_state_rel H ctx func cenv cx ee j /\ immutable_frame_mods func cenv cx ee j /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gj tj j /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK j,Gj,tj)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee j /\ _` (drule_then strip_assume_tac) >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at a x ==> lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)` by
    (gen_tac >> disch_tac >> qpat_assum `!x. _ ==> not_fresh_at m x /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  qpat_assum `!H. _ ==> vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac raw_create_snapshot_frame_mods >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qunabbrev_tac `explicit` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace` (drule_then assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code)` by
    asm_rewrite_tac[vyperTypeSystemTheory.bytelike_type_bound_def,vyperASTTheory.bound_length_def] >>
  `eval_operand snap u = SOME (n2w pbase)` by asm_rewrite_tac[] >>
  qexistsl [`bs`,`k`,`cap`,`owner`,`pbase`,`site`,`u`,`Gu`,`tu`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
QED

Finalise raw_create_reached_snapshot_mods
