(* Linked resources at the supplied endpoint of a read-only AugAssign slice. *)
Theory bodyAugReadOnlyFrameMods
Ancestors
  augAssignFullLoadFrame bodyWriteTargetStageMods bodyFullShadowBodyInv bodyFullPostsMods
  assignTuplePtrLoadStep bodyFullUnwrapRun bodyFullTargetDefs bodyMemoryDefs bodyInvSplit
  targetPlaceSimCasesBase exprSimWordArgs exprLoweringProps loweringStateRelDefs
  loweringPosts bodyPtrDefs ptrDiscipline freshWrites compileEnv stateFrame venomState
  venomInst finite_map list

Theorem aug_readonly_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables ==>
  ghost_inv_at_mods D lo d cenv cx es G1 tn1 u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers G1 tn1 p u sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem aug_readonly_immutable_mods[local]:
  immutable_frame_mods func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next ==>
  immutable_frame_mods func cenv cx es u
Proof
  strip_tac >> simp[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`, `es`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  qmatch_asmsub_rename_tac `local_region (cenv with ce_module := src) _ _ _ _ _` >>
  `local_region (cenv with ce_module := src) es.scopes u id b sz <=>
   local_region (cenv with ce_module := src) es.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >>
     metis_tac[local_ptrs_reserved_def]) >> gs[]
QED

(* A saved operand retains its value, provenance and taint, regardless of
   the new destinations introduced by the slice. *)
Theorem aug_readonly_saved_operand_mods:
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  u.vs_labels = s.vs_labels ==>
  eval_operand op u = eval_operand op s /\
  op_prov G1 op = op_prov G op /\ op_taint tn1 op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
  metis_tac[]
QED

Theorem aug_readonly_target_ptr_mods[local]:
  target_ptr_ok cenv pv r G tn s /\ local_ptrs_reserved cenv sa /\
  op_prov G1 (FST r) = op_prov G (FST r) /\
  op_taint tn1 (FST r) = op_taint tn (FST r) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G x) ==>
  target_ptr_ok cenv pv r G1 tn1 u
Proof
  gvs[target_ptr_ok_def] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* This transport uses the same source state and the same selected place.
   It applies before the RHS; it does not assert that an RHS preserves the
   source contents of a saved place. *)
Theorem aug_readonly_target_location_mods:
  write_target_location_mods cenv cx bt es pv vt r G s /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  eval_operand (FST r) u = eval_operand (FST r) s /\
  op_prov G1 (FST r) = op_prov G (FST r) ==>
  write_target_location_mods cenv cx bt es pv vt r G1 u
Proof
  Cases_on `pv`
  >- simp[write_target_location_mods_def, place_ptr_rel_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      gvs[write_target_location_mods_def] >> rpt strip_tac >>
      metis_tac[place_ptr_rel_vars_frame]) >>
  gvs[write_target_location_mods_def, place_ptr_rel_def]
QED

Theorem augassign_read_only_frame_mods:
  stmt_state_rel H ctx func cenv cx st s /\
  immutable_frame_mods func cenv cx st s /\ storage_well_formed_on cx st (FST H) /\
  ghost_inv_at_mods D lo d cenv cx st G tn s /\
  target_ptr_ok cenv pv r G tn s /\
  ghost_kept_at lo cenv es entry G0 tn0 s0 G tn /\
  wb_frame cenv es st entry s0 s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  entry.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sa s /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!x. FST r = Var x ==> not_fresh_at sa x) /\
  alloca_history func s /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stmt_state_rel H ctx func cenv cx st u /\
  immutable_frame_mods func cenv cx st u /\ storage_well_formed_on cx st (FST H) /\
  ghost_inv_at_mods D lo d cenv cx st G1 tn1 u /\
  target_ptr_ok cenv pv r G1 tn1 u /\
  ghost_kept_at lo cenv es entry G0 tn0 s0 G1 tn1 /\
  wb_frame cenv es st entry s0 u /\
  return_buf_frame d cenv sb u /\ local_ptrs_reserved cenv sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\
  eval_operand (FST r) u = eval_operand (FST r) s /\
  op_prov G1 (FST r) = op_prov G (FST r) /\ op_taint tn1 (FST r) = op_taint tn (FST r) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (allocas_below_fmp s ==> allocas_below_fmp u) /\
  (~s.vs_halted ==> ~u.vs_halted) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
   u.vs_labels = s.vs_labels /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp /\
   u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `state_frame _ = _` mp_tac >> simp[state_frame_def]) >>
  drule_all_then strip_assume_tac aug_readonly_saved_operand_mods >>
  simp[] >>
  conj_tac >- (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  conj_tac >- (irule aug_readonly_immutable_mods >> metis_tac[]) >>
  conj_tac >- (irule aug_readonly_ghost_mods >> metis_tac[]) >>
  conj_tac >- (irule aug_readonly_target_ptr_mods >> metis_tac[]) >>
  conj_tac >-
    (irule ghost_kept_at_clean_suffix >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >-
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  conj_tac >-
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >>
     simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- (simp[allocas_below_fmp_def] >> strip_tac >> simp[]) >>
  irule augassign_load_endpoint_history >> metis_tac[]
QED
