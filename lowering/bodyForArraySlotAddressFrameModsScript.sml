(* The storage address slice preserves the capture and allocation anchors. *)
Theory bodyForArraySlotAddressFrameMods
Ancestors
  bodyForArraySlotItemMods bodyForArrayHeaderMods bodyForRangeScalarFrameMods
  bodyForRangeHeaderMods bodyFullPathHistory bodyFullShared bodySimFull bodyMemoryDefs
  vyperStorageTrace vyperStorageFootprint fragGasOriginPtr gasOriginPtrLabels venomMemDefs
  stmtSimDefs stmtSimProps exprSimOperands exprLoweringProps loweringShapeDefs
  loweringPosts loweringStateRelDefs stateRelProj allocaHistory ptrDiscipline
  exprSimCopy bodyPtrDefs venomState finite_map words arithmetic bodyMemBopRestWordPath

Theorem slot_address_anchors[local]:
  for_array_item_mods c sa0 sbExpr (xd,dw,cap,aid) es Gh th sh /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gh th sh /\
  for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es th sh /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  u.vs_memory = sh.vs_memory /\ u.vs_allocas = sh.vs_allocas /\
  u.vs_alloca_next = sh.vs_alloca_next /\ tu.t_mem = th.t_mem /\
  (!x. not_fresh_at sa0 x \/ x = xd ==>
    lookup_var x u = lookup_var x sh /\ FLOOKUP Gu x = FLOOKUP Gh x /\
    op_taint tu (Var x) = op_taint th (Var x)) /\
  (!x. not_fresh_at saL x ==> lookup_var x u = lookup_var x sh) /\
  (!nm b sz. local_region c es.scopes u nm b sz <=> local_region c es.scopes sh nm b sz) ==>
  for_array_item_mods c sa0 sbExpr (xd,dw,cap,aid) es Gu tu u /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gu tu u /\
  for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es tu u
Proof
  strip_tac >>
  `!c0 e0 age r. alloca_frame c0 e0 age r c es sh ==> alloca_frame c0 e0 age r c es u` by
    (pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `u.vs_memory = sh.vs_memory` SUBST1_TAC >>
     qpat_assum `!nm b sz. local_region c es.scopes u nm b sz <=> _`
       (pure_rewrite_tac o single) >> simp[]) >>
  `lookup_var xd u = lookup_var xd sh /\ FLOOKUP Gu xd = FLOOKUP Gh xd /\
   op_taint tu (Var xd) = op_taint th (Var xd)` by simp[] >>
  conj_tac
  >- (qhdtm_x_assum `for_array_item_mods` mp_tac >>
      pure_rewrite_tac[for_array_item_mods_def,ptr_covers_def] >> asm_rewrite_tac[]) >>
  qhdtm_x_assum `for_array_outer_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_outer_frame_mods_def,range_outer_frame_mods_def]) >>
  qhdtm_x_assum `for_array_capture_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_capture_frame_mods_def]) >>
  pure_rewrite_tac[for_array_outer_frame_mods_def,range_outer_frame_mods_def,
                  for_array_capture_frame_mods_def] >>
  asm_rewrite_tac[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem for_array_slot_address_frame_mods:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (Var off,sm) /\
  (case bd of Fixed _ => sn = sm /\ sum = off
    | Dynamic _ => emit_op ADD [Lit 1w;Var off] sm = (Var sum,sn)) /\
  emit_op ADD [base_op;Var sum] sn = (Var ep,saCopy) /\ fn_has_code sa saCopy func /\
  ~sh.vs_halted /\ sh.vs_current_bb = sa.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa base_op /\ copy_old_operand sa len_op /\
  not_fresh_at sa idx /\ (!lbl. base_op <> Label lbl) /\
  eval_operand base_op sh = SOME slot /\ op_taint th base_op = {} /\
  lookup_var idx sh = SOME (n2w k) /\ op_taint th (Var idx) = {} /\ FLOOKUP Gh idx = NONE /\
  allocas_from lo sh /\ lo <= sh.vs_alloca_next /\ fn_inst_ids_distinct func /\
  sa0.cs_next_var <= sa.cs_next_var /\ saL.cs_next_var <= sa.cs_next_var /\
  local_ptrs_reserved c sa /\ not_fresh_at sa xd /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  for_array_item_mods c sa0 sbExpr (xd,dw,cap,aid) es Gh th sh /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gh th sh /\
  for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es th sh /\
  immutable_frame_mods func c cx es sh /\
  ret_pc_ok c sa0 sh /\ return_buf_frame d c sa0 sh /\ return_buf_sep d c es sh /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func c cx es sh /\ storage_well_formed_on cx es (FST H) /\
    dead_lo_ok_mods H (DF H) lo c cx /\ ghost_inv_at_mods (DF H) lo d c cx es Gh th sh) ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK u,Gu,tu)) /\
    u.vs_current_bb = saCopy.cs_current_bb /\ u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\
    ~u.vs_halted /\ eval_operand (Var ep) u = SOME
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) + n2w (k * stride)) /\
    op_taint tu (Var ep) = {} /\ op_prov Gu (Var ep) = op_prov Gh base_op /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = FLOOKUP Gh idx /\
    op_taint tu (Var idx) = op_taint th (Var idx) /\
    eval_operand base_op u = eval_operand base_op sh /\
    eval_operand len_op u = eval_operand len_op sh /\
    (!x. not_fresh_at saL x ==>
      lookup_var x u = lookup_var x sh /\ FLOOKUP Gu x = FLOOKUP Gh x /\
      op_taint tu (Var x) = op_taint th (Var x)) /\
    for_array_item_mods c sa0 sbExpr (xd,dw,cap,aid) es Gu tu u /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gu tu u /\
    for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es tu u /\
    immutable_frame_mods func c cx es u /\
    ret_pc_ok c sa0 u /\ return_buf_frame d c sa0 u /\ return_buf_sep d c es u /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func c cx es u /\ storage_well_formed_on cx es (FST H) /\
      dead_lo_ok_mods H (DF H) lo c cx /\ ghost_inv_at_mods (DF H) lo d c cx es Gu tu u
Proof
  strip_tac >>
  `alloca_history func sh /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sh)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  qpat_assum `copy_old_operand sa base_op`
    (assume_tac o REWRITE_RULE[copy_old_operand_def]) >>
  drule_all (INST_TYPE [alpha |-> ``:256``] for_array_slot_address_mods) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (conj_tac >-
       (qpat_assum `allocas_from lo sh` mp_tac >>
        pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sh` mp_tac >>
     pure_rewrite_tac[allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at saL x ==> not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
  `!nm b sz. local_region c es.scopes u nm b sz <=> local_region c es.scopes sh nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func c cx es sh` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  `alloca_inv sh` by drule_then ACCEPT_TAC rest_word_state_alloca_inv >>
  `gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK u,Gu,tu)` by simp[] >>
  `u.vs_labels = sh.vs_labels` by drule_then ACCEPT_TAC gas_origin_ptr_path_preserves_labels >>
  `alloca_history func u` by drule_all_then ACCEPT_TAC body_full_path_alloca_history >>
  suspend "frames"
QED

Resume for_array_slot_address_frame_mods[frames]:
  `for_array_item_mods c sa0 sbExpr (xd,dw,cap,aid) es Gu tu u /\
   for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gu tu u /\
   for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es tu u` by
    (irule slot_address_anchors >> asm_rewrite_tac[] >>
     qexistsl_tac [`Gh`,`sh`,`th`] >> simp[] >> metis_tac[]) >>
  `immutable_frame_mods func c cx es u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`es`,`sh`,`sa`] >> simp[]) >>
  `ret_pc_ok c sa0 u` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`c`,`sh`,`sa0`] >> simp[]) >>
  `return_buf_frame d c sa0 u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`c`,`sh`,`sa0`] >> simp[]) >>
  `return_buf_sep d c es u` by
    (Cases_on `d` >- simp[return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME p) _ _ _` >> PairCases_on `p` >>
     qpat_assum `return_buf_sep _ _ _ sh` mp_tac >>
     pure_rewrite_tac[return_buf_sep_def,allocas_from_def] >> asm_rewrite_tac[]) >>
  `!op. copy_old_operand sa op ==> eval_operand op u = eval_operand op sh` by
    (Cases >> simp[copy_old_operand_def,eval_operand_def]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >> irule ghost_inv_at_mods_exterior_frame >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ Gh th sh` (irule_at Any) >>
  qexists_tac `sa` >> simp[]
QED

Finalise for_array_slot_address_frame_mods
