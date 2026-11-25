(* Byte-address prefix of a snapshot round, before the item write. *)
Theory bodyForArraySnapshotAddressFrameMods
Ancestors
  bodyForArraySnapshotAddressMods bodyForArrayHeaderMods bodyForRangeScalarFrameMods
  bodyForRangeHeaderMods bodyFullPathHistory bodyFullShared bodySimFull bodyMemoryDefs
  vyperStorageTrace vyperStorageFootprint fragGasOriginPtr venomMemDefs
  stmtSimDefs stmtSimProps exprSimOperands exprLoweringProps loweringShapeDefs
  loweringPosts loweringStateRelDefs stateRelProj allocaHistory ptrDiscipline
  exprSimCopy bodyPtrDefs venomState finite_map words arithmetic bodyMemBopRestWordPath

Theorem snapshot_address_anchors[local]:
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn s /\
  for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tn s /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_allocas = s.vs_allocas /\ tu.t_mem = tn.t_mem /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at saLen x ==> lookup_var x u = lookup_var x s) /\
  (!nm b sz. local_region c ee.scopes u nm b sz <=> local_region c ee.scopes s nm b sz) ==>
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tu u
Proof
  strip_tac >>
  `!c0 e0 age r. alloca_frame c0 e0 age r c ee s ==>
                  alloca_frame c0 e0 age r c ee u` by
    (pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `u.vs_memory = s.vs_memory` SUBST1_TAC >>
     qpat_assum `!nm b sz. local_region c ee.scopes u nm b sz <=> _`
       (pure_rewrite_tac o single) >> simp[]) >>
  qhdtm_x_assum `for_array_outer_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_outer_frame_mods_def,range_outer_frame_mods_def]) >>
  qhdtm_x_assum `for_array_capture_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_capture_frame_mods_def]) >>
  pure_rewrite_tac[for_array_outer_frame_mods_def,range_outer_frame_mods_def,
       for_array_capture_frame_mods_def] >>
  asm_rewrite_tac[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem snapshot_address_item[local]:
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn s /\
  lookup_var xd u = lookup_var xd s /\ FLOOKUP Gu xd = FLOOKUP G xd /\
  op_taint tu (Var xd) = op_taint tn (Var xd) /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
  (!nm b sz. local_region c ee.scopes u nm b sz <=> local_region c ee.scopes s nm b sz) ==>
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee Gu tu u
Proof
  strip_tac >>
  qhdtm_x_assum `for_array_item_mods` mp_tac >>
  pure_rewrite_tac[for_array_item_mods_def,ptr_covers_def] >> asm_rewrite_tac[]
QED

Theorem for_array_snapshot_address_frame_mods:
  emit_op MUL [Var idx;Lit (n2w stride)] saAddr = (off_op,sm) /\
  (case bd of Fixed _ => sum_op = off_op /\ sn = sm
    | Dynamic _ => emit_op ADD [Lit 32w;off_op] sm = (sum_op,sn)) /\
  emit_op ADD [base_op;sum_op] sn = (addr,saCopy) /\ fn_has_code saAddr saCopy func /\
  ~s.vs_halted /\ s.vs_current_bb = saAddr.cs_current_bb /\
  s.vs_inst_idx = LENGTH saAddr.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at saAddr x) /\ (!lbl. base_op <> Label lbl) /\
  eval_operand base_op s = SOME bw /\ op_taint tn base_op = {} /\
  lookup_var idx s = SOME (n2w k) /\ op_taint tn (Var idx) = {} /\ FLOOKUP G idx = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= saAddr.cs_next_var /\ saLen.cs_next_var <= saAddr.cs_next_var /\
  local_ptrs_reserved c saAddr /\ not_fresh_at saAddr xd /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn s /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn s /\
  for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tn s /\
  immutable_frame_mods func c cx ee s /\
  ret_pc_ok c sa s /\ return_buf_frame d c sa s /\ return_buf_sep d c ee s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func c cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d c cx ee G tn s) ==>
  ?out u Gu tu.
    addr = Var out /\ not_fresh_at saCopy out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    u.vs_current_bb = saCopy.cs_current_bb /\ u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\
    ~u.vs_halted /\
    lookup_var out u = SOME (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k*stride)) /\
    op_taint tu addr = {} /\ op_prov Gu addr = op_prov G base_op /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_immutables = s.vs_immutables /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_data_section = s.vs_data_section /\ u.vs_fmp = s.vs_fmp /\
    u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_requests = s.vs_requests /\ u.vs_labels = s.vs_labels /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!x. not_fresh_at saAddr x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!op. copy_old_operand saAddr op ==> eval_operand op u = eval_operand op s /\
      op_prov Gu op = op_prov G op /\ op_taint tu op = op_taint tn op) /\
    (!nm b sz. local_region c ee.scopes u nm b sz <=> local_region c ee.scopes s nm b sz) /\
    for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee Gu tu u /\
    for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gu tu u /\
    for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tu u /\
    immutable_frame_mods func c cx ee u /\
    ret_pc_ok c sa u /\ return_buf_frame d c sa u /\ return_buf_sep d c ee u /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func c cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d c cx ee Gu tu u
Proof
  strip_tac >>
  `alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] for_array_snapshot_address_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `addr = Var out` >> rename1 `u.vs_current_bb = saCopy.cs_current_bb` >>
  `!x. not_fresh_at sa x ==> not_fresh_at saAddr x` by metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at saLen x ==> not_fresh_at saAddr x` by metis_tac[not_fresh_at_mono] >>
  `!nm b sz. local_region c ee.scopes u nm b sz <=> local_region c ee.scopes s nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `saAddr` >> simp[]) >>
  `for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee Gu tu u` by
    (irule snapshot_address_item >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func c cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  suspend "frames"
QED

Resume for_array_snapshot_address_frame_mods[frames]:
  `alloca_inv s` by drule_then ACCEPT_TAC rest_word_state_alloca_inv >>
  `alloca_history func u` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gu tu u /\
   for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tu u` by
    (irule snapshot_address_anchors >> asm_rewrite_tac[] >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `immutable_frame_mods func c cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`ee`,`s`,`saAddr`] >> simp[]) >>
  `ret_pc_ok c sa u` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`c`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  `return_buf_frame d c sa u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`c`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  `return_buf_sep d c ee u` by
    (Cases_on `d` >- simp[return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME p) _ _ _` >> PairCases_on `p` >>
     qpat_assum `return_buf_sep _ _ _ s` mp_tac >>
     pure_rewrite_tac[return_buf_sep_def,allocas_from_def] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`out`,`u`,`Gu`,`tu`] >> simp[] >> conj_tac
  >- (Cases >> simp[copy_old_operand_def,eval_operand_def,op_prov_def,op_taint_def]) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >> irule ghost_inv_at_mods_exterior_frame >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G tn s` (irule_at Any) >>
  qexists_tac `saAddr` >> simp[] >> metis_tac[]
QED

Finalise for_array_snapshot_address_frame_mods
