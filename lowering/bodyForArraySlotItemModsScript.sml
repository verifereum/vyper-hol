(* One reached storage/transient element, read at the current horizon. *)
Theory bodyForArraySlotItemMods
Ancestors
  bodyForArrayRouteMods bodyForArrayHeaderMods bodyForRangeHeaderMods bodyFullForStorage
  stmtSimDefs bodyFullSubscriptArrayCodeOps loweringShapeRules
  bodyFullPathHistory decoderOriginAllocationFrame
  bodyFullShadowBodyInv bodyForRangeScalarFrameMods exprPtrUnwrapStoragePost
  exprPtrUnwrapCopyPost exprPtrUnwrapRuntimeFrame exprPtrUnwrapLoopInvariant
  exprSimStorageCopy exprSimCopy robustCopyTransportPtr slotCopyExecution copyExecution assignTuplePtrCopyLen
  stmtSimAppendStorageCompose exprSimPtrLiteralBuffer bodyMemBopRestWordPath
  bodyFullShared ptrDiscipline stmtSimProps bodyMemoryDefs bodySimFull
  bodyPtrDefs loweringPosts bodyFullPostsMods exprLoweringProps valueEncodingProps
  exprSimFieldLayout vyperStorageTrace vyperStoragePlaceObserved vyperStorageFootprint
  loweringStateRelDefs bodyFullGhostFrame contextCodegenRel bodyInvSplit loweringSlice
  stateRelProj accountsRelProps sourceUnitExecution stmtLowering exprLowering
  fragGasOriginPtr fragGasOriginPtrLoop fragExec allocaHistory
  emitHelper context compileEnv venomState venomInst venomExecSemantics
  vyperAST vyperState words finite_map pred_set list arithmetic

Theorem slot_item_child_ptr_mods[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  stor_taint_ok_at D tn s /\ dead_lo_ok_mods H D lo cenv cx /\
  storage_place_observed H (StoragePlace tr slot tv) /\
  0 < type_slot_size tv /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME slot /\ op_taint tn op = {} ==>
  ptr_vv_ok cx ty (PlaceR (StoragePlace tr slot tv))
    (LocatedValue ty (mk_ptr op (slot_loc tr))) ee G tn s
Proof
  strip_tac >> drule stmt_state_rel_state_rel >> strip_tac >>
  drule state_rel_call_ctx_rel >> simp[call_ctx_rel_def] >> strip_tac >>
  drule_all storage_place_observed_read_live >>
  disch_then (qspec_then
    `if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage` assume_tac) >>
  Cases_on `tr` >> gvs[ptr_vv_ok_def, slot_loc_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  simp[storage_read_live_def] >>
  disch_then (qspecl_then [`w2n k`, `b`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >>
     gvs[stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def, SUBSET_DEF] >>
     simp[pairTheory.FORALL_PROD] >> strip_tac >> first_x_assum drule >> simp[])) >>
  simp[]
QED

(* The code writes into an existing allocation, even for a one-slot item.
   It neither allocates nor takes a snapshot of the whole array. *)
Theorem slot_item_counted_run_mods[local]:
  compile_slot_to_memory src (Var xd) n (slot_loc tr) saCopy =
    (slot_copy_body saCopy,sbCopy) /\
  eval_operand src u = SOME addr /\ lookup_var xd u = SOME dw /\
  op_taint tu src = {} /\ slot_copy_external saCopy src /\ not_fresh_at saCopy xd /\
  ptr_covers Gu tu xd u cap /\ 32*n <= cap /\
  w2n dw+cap < dimword (:256) /\ w2n dw+cap <= u.vs_alloca_next /\
  u.vs_current_bb = saCopy.cs_current_bb /\
  u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\ ~u.vs_halted /\
  lookup_block saCopy.cs_current_bb func.fn_blocks =
    SOME <|bb_label := saCopy.cs_current_bb;
           bb_instructions := saCopy.cs_current_insts ++ slot_copy_init_insts saCopy|> /\
  lookup_block (slot_copy_cond saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_cond saCopy;
           bb_instructions := slot_copy_cond_insts saCopy n|> /\
  lookup_block (slot_copy_body saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_body saCopy;
           bb_instructions := slot_copy_body_insts saCopy src (Var xd)
             (if tr then TLOAD else SLOAD)|> /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  ?z Gf tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gu,tu) [] (OK z,Gf,tf)) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\
    z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\ z.vs_inst_idx = 0 /\ ~z.vs_halted /\
    slot_copy_inv saCopy (if tr then TLOAD else SLOAD) u addr dw n [] n z /\
    slot_copy_ghost_inv saCopy (if tr then TLOAD else SLOAD)
      addr dw xd n Gu tu n Gf tf z /\
    slot_copy_runtime_frame saCopy dw n u z /\
    lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z)
Proof
  strip_tac >>
  `slot_copy_external saCopy (Var xd)` by simp[slot_copy_not_fresh_external] >>
  `ptr_covers Gu tu xd u (32*n)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `cap` >> simp[]) >>
  `n < 2**256 /\ w2n dw+32*n < 2**256 /\ w2n dw+32*n <= u.vs_alloca_next` by
    (fs[dimword_def] >> decide_tac) >>
  `?ce tyarr ann nid ca place cb. compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb)` by
    (qexistsl_tac [`ARB`,`ARB`,`ARB`,`ARB`,`ARB`] >>
     Cases_on `compile_expr ARB ARB (TopLevelName ARB ARB) ARB` >> simp[]) >>
  `compile_iter_elem_copy ce' src (Var xd) n (slot_loc tr) T ty ty saCopy = ((),sbCopy)` by
    simp[compile_iter_elem_copy_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) for_storage_element_copy_run >>
  disch_then (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`,`ctx`,`func`,`PG`,`Gu`,`tu`,`dw`,`[]`] mp_tac) >>
  (impl_tac >- simp[createSourceCallbackTheory.create_memory_snapshot_def]) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`] strip_assume_tac) >>
  `eval_operand (Var xd) z = eval_operand (Var xd) u` by
    fs[slot_copy_runtime_frame_def] >>
  `ptr_covers Gf tf xd z cap` by
    (drule copy_external_ptr_covers >> disch_then (qspecl_then [`xd`,`u`,`cap`] mp_tac) >> simp[]) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> fs[eval_operand_def]
QED

Theorem slot_item_copy_immutable_mods[local]:
  immutable_frame_mods func cenv cx ee u /\ local_ptrs_reserved cenv saCopy /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (dst,cap) /\
  z.vs_data_section = u.vs_data_section /\ z.vs_allocas = u.vs_allocas /\
  z.vs_alloca_next = u.vs_alloca_next /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at saCopy x ==> lookup_var x z = lookup_var x u) /\
  (!off sz. off+sz <= dst \/ dst+cap <= off ==>
    mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory) ==>
  immutable_frame_mods func cenv cx ee z
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule immutables_rel_mem_agree >>
      qexists_tac `u` >> simp[] >> rpt strip_tac >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx ee u` by metis_tac[] >>
      fs[immutable_alloca_sep_def] >>
      qpat_x_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >>
      asm_rewrite_tac[] >> disch_then drule_all >> strip_tac >>
      first_x_assum irule >>
      qpat_x_assum `!i b sz. _ ==> regions_disjoint _ _ b sz`
        (qspecl_then [`inst`,`dst`,`cap`] mp_tac) >> simp[regions_disjoint_def, ADD_COMM]) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`u`,`ee`] >> simp[] >> rpt strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) ee.scopes z id b sz <=>
   local_region (cenv with ce_module := src) ee.scopes u id b sz` by
    (irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]) >>
  fs[]
QED

Theorem slot_item_copy_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\ local_ptrs_reserved cenv saCopy /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saCopy x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saCopy x) /\
  (!x. not_fresh_at saCopy x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
     lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p u = SOME w ==>
     val_wf entry.type entry.value /\
     !i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==> i NOTIN written) /\
  (!i. i NOTIN written ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo u.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx ee Gf tf z
Proof
  strip_tac >>
  `!p sz. not_fresh_at saCopy p /\ ptr_covers G tn p u sz ==> ptr_covers Gf tf p z sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`u`,`tn`] >> simp[]) >>
  fs[ghost_inv_at_mods_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at saCopy p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >> irule robust_val_in_memory_exterior_frame >>
      `lookup_var p u = SOME w` by metis_tac[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`u.vs_memory`,`z.vs_memory`,`tn.t_mem`,`tf.t_mem`,`written`] >>
      metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem slot_item_old_rows[local]:
  alloca_frame cenv old age entry cenv ee u /\
  (!aid row. FLOOKUP entry.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  allocas_non_overlapping u /\ FLOOKUP u.vs_allocas item_id = SOME (dst,cap) /\
  age.cs_next_id <= item_id /\
  (!nm b sz. local_region cenv ee.scopes z nm b sz ==> local_region cenv ee.scopes u nm b sz) /\
  (!b sz. b+sz <= dst \/ dst+cap <= b ==> mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory) /\
  (!i. i < dst \/ dst+cap <= i ==> (i IN tf.t_mem <=> i IN tu.t_mem)) ==>
  alloca_frame cenv old age entry cenv ee z /\
  !aid off sz i. FLOOKUP entry.vs_allocas aid = SOME (off,sz) /\
    aid < age.cs_next_id /\ off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tu.t_mem
Proof
  strip_tac >>
  `!aid off sz. FLOOKUP entry.vs_allocas aid = SOME (off,sz) /\
    aid < age.cs_next_id ==> off+sz <= dst \/ dst+cap <= off` by
    (rpt strip_tac >>
     `aid <> item_id` by decide_tac >>
     qpat_x_assum `allocas_non_overlapping u` mp_tac >>
     simp[venomMemDefsTheory.allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`aid`,`item_id`,`off`,`sz`,`dst`,`cap`] mp_tac) >> simp[]) >>
  conj_tac
  >- (fs[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
      `mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory` by metis_tac[] >>
      qpat_assum `!a b n. _ ==> mem_bytes_at _ _ u.vs_memory = _ /\ _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> simp[] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!nm b sz. local_region _ _ z nm b sz ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!nm b sz. local_region _ _ u nm b sz ==> _`
        (drule_then ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  `off+sz <= dst \/ dst+cap <= off` by metis_tac[] >>
  `i < dst \/ dst+cap <= i` by decide_tac >> metis_tac[]
QED

Theorem slot_item_after_copy_frames[local]:
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tu u /\
  allocas_non_overlapping u /\ FLOOKUP u.vs_allocas item_id = SOME (dst,cap) /\
  sa.cs_next_id <= item_id /\ saExpr.cs_next_id <= item_id /\
  z.vs_alloca_next = u.vs_alloca_next /\ z.vs_allocas = u.vs_allocas /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
    op_taint tf (Var x) = op_taint tu (Var x)) /\
  (!x. not_fresh_at saLen x ==> lookup_var x z = lookup_var x u) /\
  (!nm b sz. local_region cenv ee.scopes z nm b sz ==> local_region cenv ee.scopes u nm b sz) /\
  (!b sz. b+sz <= dst \/ dst+cap <= b ==> mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory) /\
  (!i. i < dst \/ dst+cap <= i ==> (i IN tf.t_mem <=> i IN tu.t_mem)) ==>
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z
Proof
  simp[for_array_outer_frame_mods_def,range_outer_frame_mods_def,
       for_array_capture_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv ee z /\
   !aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa.cs_next_id /\ off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tu.t_mem` by
    (irule slot_item_old_rows >> qexistsl_tac [`cap`,`dst`,`item_id`,`u`] >> simp[] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv em saExpr q cenv ee z /\
   !aid off sz i. FLOOKUP q.vs_allocas aid = SOME (off,sz) /\
     aid < saExpr.cs_next_id /\ off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tu.t_mem` by
    (irule slot_item_old_rows >> qexistsl_tac [`cap`,`dst`,`item_id`,`u`] >> simp[] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (drule_all_then assume_tac) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
        (drule_all_then ACCEPT_TAC)) >>
  rpt strip_tac >>
  qpat_assum `!aid off sz i. FLOOKUP q.vs_allocas aid = _ /\ _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_assum `!aid off sz i. FLOOKUP q.vs_allocas aid = _ /\ _ ==> i IN tq.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

(* Transport the outer linked state at the actual end of the copy, before
   introducing the new scope or interpreting the copied bytes as a local. *)
Theorem slot_item_linked_endpoint[local]:
  slot_copy_runtime_frame saCopy dw n u z /\
  slot_copy_ghost_inv saCopy load addr dw xd n Gu tu n Gf tf z /\
  32*n <= cap /\ allocas_from lo u /\ allocas_from lo z /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ z.vs_inst_idx = 0 /\
  stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee Gu tu u /\
  ret_pc_ok cenv sa u /\ return_buf_frame d cenv sa u /\ return_buf_sep d cenv ee u /\
  local_ptrs_reserved cenv saCopy /\
  (!x. not_fresh_at sa x ==> not_fresh_at saCopy x) /\
  (!x. not_fresh_at saLen x ==> not_fresh_at saCopy x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tu u /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gu tu u /\
  lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA ==>
  stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
  ghost_inv_at_mods D lo d cenv cx ee Gf tf z /\
  ret_pc_ok cenv sa z /\ return_buf_frame d cenv sa z /\ return_buf_sep d cenv ee z /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
  (!op. slot_copy_external saCopy op ==>
    eval_operand op z = eval_operand op u /\ op_prov Gf op = op_prov Gu op /\
    op_taint tf op = op_taint tu op)
Proof
  strip_tac >> drule_all_then strip_assume_tac slot_copy_semantic_frame >>
  `!a. ~(w2n dw <= a /\ a < w2n dw+32*n) ==>
    mem_bytes_at a 1 z.vs_memory = mem_bytes_at a 1 u.vs_memory /\
    (a IN tf.t_mem <=> a IN tu.t_mem)` by
    (fs[slot_copy_runtime_frame_def,slot_copy_ghost_inv_def] >> metis_tac[]) >>
  `!x. not_fresh_at saCopy x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >> drule slot_copy_not_fresh_external >> strip_tac >>
     fs[slot_copy_ghost_inv_def]) >>
  `!op. slot_copy_external saCopy op ==> eval_operand op z = eval_operand op u /\
    op_prov Gf op = op_prov Gu op /\ op_taint tf op = op_taint tu op` by
    (fs[slot_copy_runtime_frame_def,slot_copy_ghost_inv_def] >>
     Cases >> simp[op_taint_def,op_prov_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[op_taint_def]) >>
  `z.vs_immutables = u.vs_immutables` by
    (qpat_assum `copy_static z = copy_static u`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [copy_static_def] o
       AP_TERM ``\r:venom_state. r.vs_immutables``)) >>
  drule_then strip_assume_tac copy_static_fields >>
  `!nm b sz. local_region cenv ee.scopes z nm b sz <=>
             local_region cenv ee.scopes u nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `saCopy` >> simp[]) >>
  fs[for_array_item_mods_def] >>
  `stmt_state_rel H ctx func cenv cx ee z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n dw`,`inst`,`u`,`saCopy`,`cap`] >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_frame_mods func cenv cx ee z` by
    (irule slot_item_copy_immutable_mods >>
     qexistsl_tac [`cap`,`w2n dw`,`inst`,`saCopy`,`u`] >>
     simp[] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  suspend "frame"
QED

Resume slot_item_linked_endpoint[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)` by metis_tac[] >>
  `ret_pc_ok cenv sa z /\ return_buf_frame d cenv sa z` by
    (conj_tac >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`u`,`sa`] >> simp[] >> metis_tac[]) >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`sa`] >> simp[] >> metis_tac[]) >>
  `return_buf_sep d cenv ee z` by
    (Cases_on `d` >- simp[return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME rb) _ _ _` >> PairCases_on `rb` >>
     fs[return_buf_sep_def,allocas_from_def] >> metis_tac[]) >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo u` (strip_assume_tac o REWRITE_RULE [allocas_from_def]) >> metis_tac[]) >>
  `!i. i < w2n dw \/ cap+w2n dw <= i ==> (i IN tf.t_mem <=> i IN tu.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!a. _ ==> mem_bytes_at a 1 z.vs_memory = _ /\ _`
       (qspec_then `i` mp_tac) >>
     `~(w2n dw <= i /\ i < w2n dw+32*n)` by decide_tac >> simp[]) >>
  `allocas_non_overlapping u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
       (mp_tac o MATCH_MP rest_word_state_alloca_inv) >> simp[venomMemDefsTheory.alloca_inv_def]) >>
  `alloca_history func z` by
    (irule alloca_history_jump >> simp[] >> qexists_tac `u` >> fs[for_array_outer_frame_mods_def,
                                                       range_outer_frame_mods_def]) >>
  `for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
   for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z` by
    (irule slot_item_after_copy_frames >> simp[] >>
     qexistsl_tac [`Gu`,`cap`,`w2n dw`,`inst.inst_id`,`tu`,`u`] >>
     simp[] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> decide_tac)
     >- first_assum ACCEPT_TAC >>
     metis_tac[]) >>
  simp[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule slot_item_copy_ghost_mods >> simp[] >>
  conj_tac >- fs[stor_taint_ok_at_def,ghost_inv_at_mods_def,slot_copy_ghost_inv_def] >>
  qexistsl_tac [`Gu`,`saCopy`,`tu`,`u`,`{a | w2n dw <= a /\ a < w2n dw+32*n}`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_region cenv ee.scopes u name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      `w2n dw + cap <= w2n w \/ w2n w+sz <= w2n dw` by metis_tac[ADD_COMM] >>
      `w2n w+sz <= w2n dw \/ w2n dw+32*n <= w2n w` by decide_tac >>
      qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
        (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          (Q.INST [`a` |-> `w2n (dw:bytes32)`,`bytes` |-> `32*n`]
             for_storage_outer_local_footprint)) th)) >>
      simp[] >> metis_tac[ADD_COMM])
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a. _ ==> mem_bytes_at a 1 z.vs_memory = _ /\ _`
        (qspec_then `i` mp_tac) >> simp[] >> decide_tac)
  >- (rpt strip_tac >> qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tu.t_mem)`
        (qspec_then `i` mp_tac) >> `i < w2n dw` by decide_tac >> simp[]) >>
  first_x_assum irule >> decide_tac
QED

Finalise slot_item_linked_endpoint[local]

Theorem slot_item_copied_value[local]:
  valid_horizon cx st0 H ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
  storage_place_observed H (StoragePlace tr addr tv) /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee Gu tu u /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand src u = SOME addr /\ op_taint tu src = {} /\
  slot_copy_inv saCopy (if tr then TLOAD else SLOAD) u addr dw
    (type_slot_size tv) [] (type_slot_size tv) z /\
  slot_copy_ghost_inv saCopy (if tr then TLOAD else SLOAD) addr dw xd
    (type_slot_size tv) Gu tu (type_slot_size tv) Gf tf z ==>
  ?v. read_result cx (PlaceR (StoragePlace tr addr tv)) ee = (INL v,ee) /\
    value_has_type tv v /\ val_wf tv v /\
    !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tv v (w2n dw) mem
Proof
  strip_tac >>
  `regions_consistent (FST H)` by fs[valid_horizon_def] >>
  drule_all_then assume_tac for_storage_current_child_holds >>
  `stor_taint_ok_at D tu u` by fs[ghost_inv_at_mods_def] >>
  drule_all_then assume_tac slot_item_child_ptr_mods >>
  drule_then assume_tac copy_prefix_words >> drule_then assume_tac copy_prefix_taint >>
  `?v. read_result cx (PlaceR (StoragePlace tr addr tv)) ee = (INL v,ee) /\
       !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tv v (w2n dw) mem` by
    (irule unwrap_storage_copied_robust >>
     qexistsl_tac [`Gu`,`mk_ptr src (slot_loc tr)`,`u`,`ty`,`ty`,`tu`,`tr`,`addr`] >>
     Cases_on `tr` >> fs[mk_ptr_def] >> metis_tac[]) >>
  drule_all for_storage_current_read_push >>
  disch_then (qspec_then `ARB` (qx_choose_then `v'` strip_assume_tac)) >>
  `v' = v` by
    (qpat_x_assum `read_result cx _ ee = (INL v',ee)` mp_tac >> simp[]) >>
  qexists_tac `v` >> gvs[]
QED

(* Execute the address slice at the successful test landing. The header
   contributes one slot only for Dynamic arrays. *)
Theorem for_array_slot_address_mods:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (Var off,sm) /\
  (case bd of Fixed _ => sn = sm /\ sum = off
    | Dynamic _ => emit_op ADD [Lit 1w;Var off] sm = (Var sum,sn)) /\
  emit_op ADD [base_op;Var sum] sn = (Var ep,saCopy) /\ fn_has_code sa saCopy func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\ (!lbl. base_op <> Label lbl) /\
  eval_operand base_op s = SOME slot /\ op_taint tn base_op = {} /\
  lookup_var idx s = SOME (n2w k) /\ op_taint tn (Var idx) = {} /\ FLOOKUP G idx = NONE /\
  allocas_from lo s /\ fn_inst_ids_distinct func ==>
  ?u Gu tu.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    u.vs_current_bb = saCopy.cs_current_bb /\
    u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var ep) u = SOME
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) + n2w (k * stride)) /\
    op_taint tu (Var ep) = {} /\ op_prov Gu (Var ep) = op_prov G base_op /\
    u.vs_immutables = s.vs_immutables /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_data_section = s.vs_data_section /\ u.vs_fmp = s.vs_fmp /\
    u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_requests = s.vs_requests /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q u = lookup_var q s /\ FLOOKUP Gu q = FLOOKUP G q /\
      op_taint tu (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es u)
Proof
  strip_tac >> Cases_on `bd` >> gvs[]
  >- (`eval_operand (Var idx) s = SOME (n2w k) /\ op_prov G (Var idx) = NONE` by
        simp[eval_operand_def,op_prov_def] >>
      drule_all scalar_mul_add_joint_frame >> disch_then (qspec_then `PG` mp_tac) >>
      disch_then (qx_choosel_then [`Gu`,`tu`,`u`] strip_assume_tac) >>
      `u.vs_initial_fmp = s.vs_initial_fmp` by
        (qpat_assum `!D lo explicit. allocas_from lo s ==> _`
           (qspecl_then [`ARB`,`lo`,`ARB`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
         drule_all_then strip_assume_tac decoder_origin_path_allocation_frame >> simp[]) >>
      qexistsl [`u`,`Gu`,`tu`] >> simp[eval_operand_def]) >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn saCopy` by
    metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `fn_has_code sa sn func /\ fn_has_code sn saCopy func` by
    metis_tac[ci_mono_def,cs_extends_trans,fn_has_code_split] >>
  `eval_operand (Var idx) s = SOME (n2w k) /\ op_prov G (Var idx) = NONE` by
    simp[eval_operand_def,op_prov_def] >>
  `(!x. Lit 1w = Var x ==> not_fresh_at sa x) /\ (!l. Lit 1w <> Label l) /\
   eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  drule_all (scalar_mul_add_joint_frame |> Q.INST [`base_op` |-> `Lit 1w`]) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac) >>
  `s1.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `!D lo explicit. allocas_from lo s ==> _`
      (qspecl_then [`ARB`,`lo`,`ARB`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     drule_all_then strip_assume_tac decoder_origin_path_allocation_frame >> simp[]) >>
  `op_prov G1 (Var sum) = NONE` by simp[op_prov_def] >>
  `eval_operand base_op s1 = SOME slot /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = op_prov G base_op` by
    (Cases_on `base_op` >> gvs[eval_operand_def,op_taint_def,op_prov_def]) >>
  `eval_operand (Var sum) s1 = SOME (1w + n2w (k * stride))` by simp[eval_operand_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by simp[allocas_below_fmp_def] >> simp[]) >>
  drule_all (scalar_binop_joint_frame |> Q.INST
    [`opc` |-> `ADD`, `w` |-> `a + b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac) >>
  qexistsl [`s2`,`G2`,`tn2`] >> simp[eval_operand_def,WORD_ADD_ASSOC] >> conj_tac
  >- (map_every qx_gen_tac [`D`,`cut`,`explicit`] >> disch_tac >>
      `allocas_from cut s1` by
        (qpat_x_assum `allocas_from cut s` mp_tac >> simp[allocas_from_def]) >>
      `gas_origin_ptr_path (D,cut,explicit,ctx,func,PG) (s,G,tn) [] (OK s1,G1,tn1)` by simp[] >>
      `gas_origin_ptr_path (D,cut,explicit,ctx,func,PG) (s1,G1,tn1) [] (OK s2,G2,tn2)` by simp[] >>
      drule_all_then ACCEPT_TAC gas_origin_ptr_path_trans) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn q` by metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sn` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

(* Copy entry is the landing of the scalar prefix: the offset is taken from
   the actual saved base/index and is tied to the captured place suffix. *)
Theorem for_array_slot_item_mods:
  vs = GENLIST (\i. PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (i * type_slot_size tv)) tv)) len /\
  a::rs = DROP k vs /\ compatible_bound bd len /\
  MEM (StorageRoot tr off root) em.storage_trace /\
  storage_subregion root path delta (ArrayTV tv bd) /\ slot = n2w off + n2w delta /\
  ee.storage_trace = em.storage_trace ++ extra /\ storage_trace_domain cx st0 ee.storage_trace /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ well_formed_type_value tv /\
  0 < type_slot_size tv /\ 32 * type_slot_size tv <= cap /\
  addr = (case bd of Fixed _ => slot | Dynamic _ => slot + 1w) + n2w (k * type_slot_size tv) /\
  eval_operand src u = SOME addr /\ op_taint tu src = {} /\
  slot_copy_external saCopy src /\ not_fresh_at saCopy xd /\
  compile_slot_to_memory src (Var xd) (type_slot_size tv) (slot_loc tr) saCopy =
    (slot_copy_body saCopy,sbCopy) /\
  u.vs_current_bb = saCopy.cs_current_bb /\
  u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\ ~u.vs_halted /\
  lookup_block saCopy.cs_current_bb func.fn_blocks =
    SOME <|bb_label := saCopy.cs_current_bb;
           bb_instructions := saCopy.cs_current_insts ++ slot_copy_init_insts saCopy|> /\
  lookup_block (slot_copy_cond saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_cond saCopy;
           bb_instructions := slot_copy_cond_insts saCopy (type_slot_size tv)|> /\
  lookup_block (slot_copy_body saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_body saCopy;
           bb_instructions := slot_copy_body_insts saCopy src (Var xd)
             (if tr then TLOAD else SLOAD)|> /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  local_ptrs_reserved cenv saCopy /\
  (!x. not_fresh_at sa x ==> not_fresh_at saCopy x) /\
  (!x. not_fresh_at saLen x ==> not_fresh_at saCopy x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tu u /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gu tu u /\
  ret_pc_ok cenv sa u /\ return_buf_frame d cenv sa u /\ return_buf_sep d cenv ee u /\
  immutable_frame_mods func cenv cx ee u /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
     dead_lo_ok_mods H (DF H) lo cenv cx /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u) ==>
  ?v z Gf tf.
    read_result cx a ee = (INL v,ee) /\ value_has_type tv v /\ val_wf tv v /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\
    z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\ ~z.vs_halted /\
    (!op. slot_copy_external saCopy op ==>
      eval_operand op z = eval_operand op u /\ op_prov Gf op = op_prov Gu op /\
      op_taint tf op = op_taint tu op) /\
    for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
    for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
    for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z /\
    immutable_frame_mods func cenv cx ee z /\
    ret_pc_ok cenv sa z /\ return_buf_frame d cenv sa z /\ return_buf_sep d cenv ee z /\
    allocas_from lo z /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf) /\
      stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf z
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     a = PlaceR (StoragePlace tr addr tv) /\ storage_place_observed H (StoragePlace tr addr tv)` by
    (rpt strip_tac >> drule_all_then strip_assume_tac for_array_storage_round_input_mods >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `?z Gf tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\ z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
    z.vs_inst_idx = 0 /\ ~z.vs_halted /\ slot_copy_inv saCopy (if tr then TLOAD else SLOAD) u addr dw
      (type_slot_size tv) [] (type_slot_size tv) z /\
    slot_copy_ghost_inv saCopy (if tr then TLOAD else SLOAD) addr dw xd
       (type_slot_size tv) Gu tu (type_slot_size tv) Gf tf z /\
    slot_copy_runtime_frame saCopy dw (type_slot_size tv) u z /\
    lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (irule slot_item_counted_run_mods >>
     fs[for_array_item_mods_def,for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
     qexists_tac `src` >> simp[]) >>
  suspend "value"
QED

Resume for_array_slot_item_mods[value]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ storage_place_observed H _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac slot_item_copied_value >>
  qexistsl_tac [`v`,`z`,`Gf`,`tf`] >>
  conj_tac >- (qpat_assum `a = PlaceR _` (once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  simp[] >> suspend "post"
QED

Resume for_array_slot_item_mods[post]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf z /\
     ret_pc_ok cenv sa z /\ return_buf_frame d cenv sa z /\ return_buf_sep d cenv ee z /\
     for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
     for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z /\
     for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
     (!op. slot_copy_external saCopy op ==>
       eval_operand op z = eval_operand op u /\ op_prov Gf op = op_prov Gu op /\
       op_taint tf op = op_taint tu op)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     irule slot_item_linked_endpoint >> simp[] >>
     qexistsl_tac [`addr`,`if tr then TLOAD else SLOAD`,`type_slot_size tv`] >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >> fs[]
QED

Finalise for_array_slot_item_mods
