(* Dispatch the old-word load at the location of the reached source place. *)
Theory bodyAugSelectedLoadMods
Ancestors
  bodyAugMemoryLoadMods bodyAugSlotLoadMods bodyAugCtorLoadMods
  exprSimWordArgs exprSimUnwrap emitHelperProps loweringShapeRules
  bodyPtrDefs bodyFullPostsMods targetPlaceSim context bodyWriteTargetStageMods
  loweringPosts vyperState venomInst fragGasOriginPtr vyperStorageFootprint
  emitHelper fragExec

Theorem augassign_target_start_obs_mods[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt (es with gas_obs := gs)
    sa sb s0 mid pv vt r G0 tn0 G tn t <=>
  write_target_post_mods H D lo d ctx func cenv cx bt es
    sa sb s0 mid pv vt r G0 tn0 G tn t
Proof
  simp[write_target_post_mods_def, wb_frame_def, locals_kept_def, popped_kept_def, ghost_kept_at_def]
QED

Theorem augassign_reached_location_mods:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sT s0 mid
    (PlaceR p) (Type ty) r G0 tn0 Gtarget tt t ==>
  FST (SND r) = SOME (case p of StoragePlace tr slot tv => slot_loc tr
                            | MemoryPlace id path => LocMemory
                            | ImmutablePlace owner id path => LocCode)
Proof
  Cases_on `p` >> simp[write_target_post_mods_def, write_target_location_mods_def,
                       place_ptr_rel_def] >> strip_tac >> simp[]
QED

Theorem augassign_emit_load_shape[local]:
  emit_op opc [a] sT = (old,s1) /\ opc <> ALLOCA ==>
  s1.cs_current_bb = sT.cs_current_bb /\
  s1.cs_current_insts = sT.cs_current_insts ++ emitted_insts sT s1 /\
  sT.cs_next_var <= s1.cs_next_var /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sT s1) /\
  (!l. old <> Label l)
Proof
  strip_tac >> drule_then strip_assume_tac emit_op_facts >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  simp[mk_inst_def]
QED

Theorem augassign_selected_load_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env mid /\
  is_word_type ty /\ storage_trace_domain cx st0 mid.storage_trace /\
  eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
      (PlaceR p) (Type ty) r G0 tn0 Gtarget tt t) /\
  (!id path. p = MemoryPlace id path ==>
    ?entry cur. lookup_scopes id mid.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL cur) /\
  local_ptrs_reserved cenv sT /\ fn_has_code sT s1 func /\
  FST (SND r) = SOME loc /\
  (if loc = LocCode then
     compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
   else emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
            [FST r]) sT = (old,s1) ==>
  ?addr cur ptv u Gu tu.
    eval_operand (FST r) t = SOME addr /\
    read_place cx p mid = (INL cur,mid) /\
    place_type_value cx p mid = (INL ptv,mid) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,Gtarget,tt) [] (OK u,Gu,tu)) /\
    eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
    eval_operand (FST r) u = SOME addr /\
    op_taint tu old = {} /\ op_prov Gu old = NONE /\
    (!q. old = Var q ==> not_fresh_at s1 q) /\ (!l. old <> Label l) /\
    (!q. FST r = Var q ==> not_fresh_at s1 q) /\
    ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
    u.vs_inst_idx = LENGTH s1.cs_current_insts /\
    state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
    s1.cs_current_bb = sT.cs_current_bb /\
    s1.cs_current_insts = sT.cs_current_insts ++ emitted_insts sT s1 /\
    sT.cs_next_var <= s1.cs_next_var /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sT s1) /\
    tu.t_mem = tt.t_mem /\ tu.t_stor = tt.t_stor /\
    tu.t_trans = tt.t_trans /\ tu.t_imm = tt.t_imm /\
    (!q. not_fresh_at sT q ==> lookup_var q u = lookup_var q t /\
         FLOOKUP Gu q = FLOOKUP Gtarget q /\ op_taint tu (Var q) = op_taint tt (Var q))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (assume_tac o MATCH_MP augassign_reached_location_mods)) >>
  Cases_on `p` >> fs[Excl "state_frame_def"]
  >- suspend "storage"
  >- suspend "memory"
  >> suspend "immutable"
QED

Resume augassign_selected_load_mods[storage]:
  rename1 `eval_target_place _ _ _ = (INL (StoragePlace tr slot tv),mid)` >>
  `emit_op (if tr then TLOAD else SLOAD) [FST r] sT = (old,s1)` by
    (Cases_on `tr` >> gvs[slot_loc_def]) >>
  drule (Q.INST [`opc` |-> `if tr then TLOAD else SLOAD`] augassign_emit_load_shape) >>
  `(if tr then TLOAD else SLOAD) <> ALLOCA` by (Cases_on `tr` >> simp[]) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       dead_lo_ok_mods H (DF H) lo cenv cx /\
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt
         (es with gas_obs := reads) sa sT s0 mid (PlaceR (StoragePlace tr slot tv))
         (Type ty) r G0 tn0 Gtarget tt t` by
    simp[augassign_target_start_obs_mods] >>
  drule_all augassign_slot_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`slot`,`cur`,`tv`,`u`,`G1`,`tn1`] >>
  fs[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality]
QED

Resume augassign_selected_load_mods[memory]:
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >> fs[] >>
  rename1 `eval_target_place _ _ _ = (INL (MemoryPlace id path),mid)` >>
  drule augassign_emit_load_shape >> simp[] >> strip_tac >>
  Q_TAC (C SUBGOAL_THEN assume_tac)
    `?entry cur. lookup_scopes id mid.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL cur`
  >- (qexistsl_tac [`entry`,`cur`] >> simp[]) >>
  drule_all augassign_memory_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then
    [`addr`,`loaded`,`ptv`,`u`,`G1`,`tn1`] strip_assume_tac)) >>
  qexistsl_tac [`addr`,`loaded`,`ptv`,`u`,`G1`,`tn1`] >>
  fs[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality]
QED

Resume augassign_selected_load_mods[immutable]:
  gvs[] >>
  rename1 `eval_target_place _ _ _ = (INL (ImmutablePlace owner id path),mid)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       dead_lo_ok_mods H (DF H) lo cenv cx /\
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
         (PlaceR (ImmutablePlace owner id path)) (Type ty) r G0 tn0 Gtarget tt t` by simp[] >>
  drule_all augassign_ctor_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!l. old <> Label l` by
    (Cases_on `cenv.ce_imm_alloca` >> fs[compile_ptr_load_def, compile_imm_load_word_no_base]
     >- (drule_then strip_assume_tac emit_op_facts >> simp[]) >>
     drule_then strip_assume_tac compile_imm_load_word_ctor_result >> simp[]) >>
  qexistsl_tac [`n2w (off + k)`,`cur`,`ptv`,`u`,`G1`,`tn1`] >>
  fs[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality]
QED

Finalise augassign_selected_load_mods
