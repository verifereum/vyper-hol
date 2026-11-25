(* Common frame of the scalar writes and jump on either Array control edge. *)
Theory bodyForArrayControlFrameMods
Ancestors
  bodyForArrayHeaderMods bodyForRangeHeaderMods bodyForRangeScalarFrameMods
  bodyFullShared bodySimFull
  bodyMemoryDefs allocaHistory exprSimOperands exprLoweringProps
  stmtSimDefs stmtSimProps loweringPosts loweringStateRelDefs
  loweringShapeDefs venomState finite_map ptrDiscipline bodyPtrDefs

Theorem scalar_jump_alloca_frame[local]:
  alloca_frame c0 e0 a s0 c ee s /\
  not_local_ptr c ee.scopes x /\ not_local_ptr c ee.scopes y ==>
  alloca_frame c0 e0 a s0 c ee (jump_to lbl (update_var x vx (update_var y vy s)))
Proof
  strip_tac >> irule alloca_frame_same_state >>
  qexists_tac `update_var x vx (update_var y vy s)` >> simp[jump_to_def] >>
  irule alloca_frame_update_var >> simp[] >>
  irule alloca_frame_update_var >> simp[]
QED

Theorem for_array_control_scalar_frame_mods:
  sa.cs_next_var <= saLen.cs_next_var /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at saLen x /\ ~not_fresh_at saLen y /\ xd <> x /\ xd <> y /\
  (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  for_array_item_mods cenv sa saExpr (xd,dw,capacity,aidItem) ee G tn s /\
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sa s /\ return_buf_sep d cenv ee s /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn s /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,u,tu) ee tn s ==>
  let t = jump_to lbl (update_var x vx (update_var y vy s));
      G1 = DRESTRICT (DRESTRICT G (COMPL {y})) (COMPL {x});
      tn1 = tn with t_var := tn.t_var |+ (y,{}) |+ (x,{})
  in
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ t.vs_halted = s.vs_halted /\
    (!q. q <> x /\ q <> y ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
        op_taint tn1 (Var q) = op_taint tn (Var q)) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    t.vs_requests = s.vs_requests /\ t.vs_labels = s.vs_labels /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    for_array_item_mods cenv sa saExpr (xd,dw,capacity,aidItem) ee G1 tn1 t /\
    stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ret_pc_ok cenv sa t /\ return_buf_frame d cenv sa t /\ return_buf_sep d cenv ee t /\
    ghost_inv_at_mods D lo d cenv cx ee G1 tn1 t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 t /\
    for_array_capture_frame_mods cenv (em,saExpr,saLen,u,tu) ee tn1 t
Proof
  strip_tac >> simp[LET_THM, Excl "DRESTRICT_DRESTRICT"] >>
  qabbrev_tac `t = jump_to lbl (update_var x vx (update_var y vy s))` >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT G (COMPL {y})) (COMPL {x})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (y,{}) |+ (x,{})` >>
  `!q. q <> x /\ q <> y ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)` by
    simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  `!q. not_fresh_at saLen q ==> q <> x /\ q <> y` by (rpt strip_tac >> gvs[]) >>
  `!q. not_fresh_at saLen q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)` by
    (gen_tac >> disch_tac >> qpat_assum `!q. q <> x /\ q <> y ==> _` irule >> simp[]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at saLen q` by
    (gen_tac >> disch_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!q. not_fresh_at saLen q ==> lookup_var q t = _ /\ _` irule >> simp[]) >>
  `~not_fresh_at sa x /\ ~not_fresh_at sa y` by
    (conj_tac >> disch_tac >> qpat_assum `!q. not_fresh_at sa q ==> not_fresh_at saLen q` drule >> simp[]) >>
  `not_local_ptr cenv ee.scopes x /\ not_local_ptr cenv ee.scopes y` by
    (conj_tac >> irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[]) >>
  `t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ t.vs_halted = s.vs_halted /\
   t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_requests = s.vs_requests /\ t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, update_var_def] >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by simp[Abbr `tn1`] >>
  simp[] >>
  conj_tac >- suspend "item" >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- suspend "pc" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "separation" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  conj_tac >- suspend "outer" >>
  suspend "capture"
QED

Resume for_array_control_scalar_frame_mods[item]:
  `lookup_var xd t = lookup_var xd s /\ FLOOKUP G1 xd = FLOOKUP G xd /\
   op_taint tn1 (Var xd) = op_taint tn (Var xd)` by
    (qpat_assum `!q. q <> x /\ q <> y ==> _` irule >> simp[]) >>
  `!nm b sz. local_region cenv ee.scopes t nm b sz <=>
             local_region cenv ee.scopes s nm b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sa p` by
       (qpat_x_assum `local_ptrs_reserved cenv sa`
          (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 p sz1 sz2. _` drule >> simp[]) >> simp[]) >>
  `ptr_covers G1 tn1 xd t capacity <=> ptr_covers G tn xd s capacity` by
    simp[ptr_covers_def] >>
  qhdtm_x_assum `for_array_item_mods` mp_tac >>
  simp[for_array_item_mods_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_control_scalar_frame_mods[state]:
  simp[Abbr `t`, stmt_state_rel_jump_to] >>
  irule stmt_state_rel_update_var >> simp[] >> irule stmt_state_rel_update_var >> simp[]
QED

Resume for_array_control_scalar_frame_mods[immutable]:
  irule immutable_frame_mods_exterior_frame >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  qexists_tac `sa` >> simp[]
QED

Resume for_array_control_scalar_frame_mods[pc]:
  irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[]
QED

Resume for_array_control_scalar_frame_mods[buffer]:
  irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]
QED

Resume for_array_control_scalar_frame_mods[separation]:
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  irule return_buf_sep_locals_kept >> simp[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (irule_at Any) >>
  qexists_tac `sa` >> simp[]
QED

Resume for_array_control_scalar_frame_mods[ghost]:
  irule ghost_inv_at_mods_exterior_frame >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `sa` >> simp[]
QED

Resume for_array_control_scalar_frame_mods[outer]:
  qhdtm_x_assum `for_array_outer_frame_mods` mp_tac >>
  simp[for_array_outer_frame_mods_def, range_outer_frame_mods_def] >> strip_tac >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    (simp[Abbr `t`] >> irule scalar_jump_alloca_frame >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Resume for_array_control_scalar_frame_mods[capture]:
  qhdtm_x_assum `for_array_capture_frame_mods` mp_tac >>
  simp[for_array_capture_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv em saExpr u cenv ee t` by
    (simp[Abbr `t`] >> irule scalar_jump_alloca_frame >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise for_array_control_scalar_frame_mods
