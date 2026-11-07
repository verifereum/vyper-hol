Theory fnPlanLineageResourceProbe
Ancestors fnPlanLineage fnPlanLineageEntryProbe fnPlanLineageNativeOriginProbe fnPlanLineagePhiBoundaryProbe
  codegenReadyCompute
Libs wordsLib fnPlanLineageProbeLib

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY];

(* Finite diagnostic measurements, not an invariant or coverage assertion. *)
Definition resource_probe_row_def:
  resource_probe_row ps names = MAP (\v.
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      if Var v IN FDOM ps.ps_spilled then 1 else 0) names
End

Theorem dead_phi_resource_rows:
  resource_probe_row (phi_boundary_setup 1)
    (live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 0) = [1;0] /\
  resource_probe_row (phi_boundary_setup 2)
    (live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 0) = [0;1] /\
  EVERY (\side. resource_probe_row (phi_boundary_written side)
    (live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 1) = []) [1;2]
Proof
  mp_tac phi_boundary_dead_frontiers >>
  simp_tac (srw_ss()) [listTheory.EVERY_DEF] >> strip_tac >>
  simp[resource_probe_row_def, rich_listTheory.LIST_ELEM_COUNT_DEF]
QED

Theorem dead_phi_native_entry:
  dfs_aux_call (liveness_analyze phi_boundary_dead_fn)
    (dfg_build_function phi_boundary_dead_fn) (cfg_analyze phi_boundary_dead_fn)
    phi_boundary_dead_fn (init_cleanup_plan_state NONE [] 0 0)
    ["entry"] [] (init_cleanup_plan_state NONE [] 0 0)
Proof
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem dead_phi_native_right:
  dfs_aux_call (liveness_analyze phi_boundary_dead_fn)
    (dfg_build_function phi_boundary_dead_fn) (cfg_analyze phi_boundary_dead_fn)
    phi_boundary_dead_fn (init_cleanup_plan_state NONE [] 0 0)
    ["R"] ["entry"]
    (SND (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0))))
Proof
  irule native_origin_first_branch >> conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `["L"]` >> EVAL_TAC) >>
  qexistsl_tac [`EL 0 phi_boundary_dead_fn.fn_blocks`,
    `FST (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0)))`,
    `init_cleanup_plan_state NONE [] 0 0`] >>
  simp[dead_phi_native_entry] >> EVAL_TAC
QED

Theorem dead_phi_native_join:
  dfs_aux_call (liveness_analyze phi_boundary_dead_fn)
    (dfg_build_function phi_boundary_dead_fn) (cfg_analyze phi_boundary_dead_fn)
    phi_boundary_dead_fn (init_cleanup_plan_state NONE [] 0 0)
    ["J"] ["R";"entry"] (phi_boundary_incoming 2)
Proof
  irule native_origin_first_branch >> conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `[]` >> EVAL_TAC) >>
  qexistsl_tac [`EL 2 phi_boundary_dead_fn.fn_blocks`,
    `FST (THE (phi_boundary_step 2
      (SND (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0))))))`,
    `SND (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0)))`] >>
  simp[dead_phi_native_right] >> EVAL_TAC
QED

(* The existing selective suite has no post-instruction live spills
   (selective_cases_spill_phase_table).  One smaller adaptation forces a
   dead deep input below 17 still-live values in the native entry block. *)
Definition resource_spill_fn_def:
  resource_spill_fn = residual_pressure_fn with fn_blocks :=
    LUPDATE ((EL 0 residual_pressure_fn.fn_blocks) with bb_instructions :=
      [mk_inst 500 ADD [Lit 2w; Lit 3w] ["deep"]] ++
      TAKE 17 (EL 0 residual_pressure_fn.fn_blocks).bb_instructions ++
      [mk_inst 501 ADD [Var "deep"; Lit 1w] ["gone"]] ++
      DROP 17 (EL 0 residual_pressure_fn.fn_blocks).bb_instructions)
      0 residual_pressure_fn.fn_blocks
End

Theorem resource_spill_ready:
  codegen_ready_fn resource_spill_fn
Proof
  EVAL_TAC >> simp[]
QED

Definition resource_spill_lv_def:
  resource_spill_lv = liveness_analyze resource_spill_fn
End
Definition resource_spill_dg_def:
  resource_spill_dg = dfg_build_function resource_spill_fn
End
Definition resource_spill_cg_def:
  resource_spill_cg = cfg_analyze resource_spill_fn
End
Definition resource_spill_walk_def:
  resource_spill_walk lv dg cg fn 0 = entry_probe_start /\
  resource_spill_walk lv dg cg fn (SUC i) = SND (THE (generate_inst_plan
    lv dg cg fn (EL i (EL 0 fn.fn_blocks).bb_instructions)
    (live_vars_at lv "entry" (SUC i)) F
    (is_terminator (EL (SUC i)
      (EL 0 fn.fn_blocks).bb_instructions).inst_opcode)
    "entry" (resource_spill_walk lv dg cg fn i)))
End
Definition resource_spill_phase_def:
  resource_spill_phase i = resource_spill_walk resource_spill_lv
    resource_spill_dg resource_spill_cg resource_spill_fn i
End

Theorem resource_spill_obstruction:
  (resource_spill_phase 18).ps_stack = MAP Var residual_pressure_names ++ [Var "deep"]
Proof
  rewrite_tac[resource_spill_phase_def] >>
  CONV_TAC (eval_def_occurrences resource_spill_lv_def) >>
  CONV_TAC (eval_def_occurrences resource_spill_dg_def) >>
  CONV_TAC (eval_def_occurrences resource_spill_cg_def) >>
  EVAL_TAC
QED

(* One replacement: OFFSET pushes bypass optimistic output placement, so
   the deep dead input remains below the live entry-defined values. *)
Definition resource_offset_fn_def:
  resource_offset_fn = resource_spill_fn with fn_blocks :=
    LUPDATE ((EL 0 resource_spill_fn.fn_blocks) with bb_instructions :=
      TAKE 1 (EL 0 resource_spill_fn.fn_blocks).bb_instructions ++
      MAPi (\i v. mk_inst (10+i) OFFSET [Lit 0w; Label "J"] [v])
        residual_pressure_names ++
      DROP 18 (EL 0 resource_spill_fn.fn_blocks).bb_instructions)
      0 resource_spill_fn.fn_blocks
End
Definition resource_offset_lv_def:
  resource_offset_lv = liveness_analyze resource_offset_fn
End
Definition resource_offset_dg_def:
  resource_offset_dg = dfg_build_function resource_offset_fn
End
Definition resource_offset_cg_def:
  resource_offset_cg = cfg_analyze resource_offset_fn
End
Definition resource_offset_phase_def:
  resource_offset_phase i = resource_spill_walk resource_offset_lv
    resource_offset_dg resource_offset_cg resource_offset_fn i
End

Theorem resource_offset_ready:
  codegen_ready_fn resource_offset_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem resource_offset_cut_cache:
  resource_offset_phase 19 = entry_probe_start with
    <|ps_stack := [Var "v16"; Var "v00"; Var "v01"; Var "v02";
        Var "v03"; Var "v04"; Var "v05"; Var "v06"; Var "v07";
        Var "v08"; Var "v09"; Var "v10"; Var "v11"; Var "v12"; Var "v13"];
      ps_spilled := FEMPTY |+ (Var "v15",0) |+ (Var "v14",32);
      ps_alloc := <|sa_free_slots := []; sa_next_offset := 64; sa_spill_base := 0|> |>
Proof
  rewrite_tac[resource_offset_phase_def] >>
  CONV_TAC (eval_def_occurrences resource_offset_lv_def) >>
  CONV_TAC (eval_def_occurrences resource_offset_dg_def) >>
  CONV_TAC (eval_def_occurrences resource_offset_cg_def) >> EVAL_TAC >>
  qmatch_goalsub_abbrev_tac `FOLDL f st xs` >>
  `xs = []` by
    (simp[Abbr `xs`, listTheory.FILTER_EQ_NIL, listTheory.EVERY_MAP,
       listTheory.EVERY_MEM, listTheory.MEM_SET_TO_LIST] >>
     rpt strip_tac >> gvs[]) >>
  simp[Abbr `st`]
QED

Theorem resource_offset_cut_measurements:
  resource_probe_row (resource_offset_phase 19) residual_pressure_names = REPLICATE 17 1 /\
  (resource_offset_phase 19).ps_spilled <> FEMPTY /\
  EVERY (\v. MEM v (live_vars_at resource_offset_lv "entry" 19)) ["v14";"v15"] /\
  EVERY (\v. ~MEM (Var v) (resource_offset_phase 19).ps_stack) ["v14";"v15"]
Proof
  rewrite_tac[resource_offset_cut_cache] >>
  CONV_TAC (eval_def_occurrences resource_offset_lv_def) >> EVAL_TAC >> simp[]
QED

(* Output-origin support is separate from resource counts.  The name set
   below is computed from strictly earlier original entry instructions. *)
Theorem resource_offset_cut_origins:
  EVERY (\op. ?v. op = Var v /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (TAKE 19 (EL 0 resource_offset_fn.fn_blocks).bb_instructions))))
    (resource_offset_phase 19).ps_stack /\
  (!v. Var v IN FDOM (resource_offset_phase 19).ps_spilled ==>
    MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (TAKE 19 (EL 0 resource_offset_fn.fn_blocks).bb_instructions))))
Proof
  rewrite_tac[resource_offset_cut_cache] >>
  CONV_TAC (eval_def_occurrences resource_offset_fn_def) >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem pressure_join_resource_rows:
  resource_probe_row (residual_pressure_incoming 2)
    (live_vars_at native_pressure_lv "J" 0) =
      REPLICATE 17 1 ++ [0;1] /\
  resource_probe_row residual_pressure_post_phi
    (live_vars_at native_pressure_lv "J" 1) = REPLICATE 18 1 /\
  resource_probe_row residual_pressure_post_ordinary
    (live_vars_at native_pressure_lv "J" 2) = REPLICATE 17 1
Proof
  rewrite_tac[native_pressure_lv_def, residual_pressure_liveness_cache] >> EVAL_TAC >> simp[]
QED


Theorem dead_phi_native_origins:
  EVERY (\op. ?v. op = Var v /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (EL 2 phi_boundary_dead_fn.fn_blocks).bb_instructions)))
    (phi_boundary_setup 2).ps_stack /\
  (phi_boundary_written 2).ps_stack = [] /\
  (phi_boundary_written 2).ps_spilled = FEMPTY
Proof
  mp_tac phi_boundary_dead_frontiers >>
  simp_tac (srw_ss()) [listTheory.EVERY_DEF] >> strip_tac >>
  simp[] >> EVAL_TAC
QED

Theorem pressure_join_setup_and_origins:
  prepare_params_plan native_pressure_lv residual_pressure_fn
    (residual_pressure_incoming 2) = ([],residual_pressure_incoming 2) /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (FLAT (MAP (\bb. FLAT (MAP (\inst. inst.inst_outputs)
      bb.bb_instructions))
      [EL 2 residual_pressure_fn.fn_blocks; EL 0 residual_pressure_fn.fn_blocks])))
    (residual_pressure_incoming 2).ps_stack /\
  EVERY (\op. ?v. op = Var v /\
    MEM v ("x" :: residual_pressure_names)) residual_pressure_post_phi.ps_stack /\
  EVERY (\op. ?v. op = Var v /\ MEM v residual_pressure_names)
    residual_pressure_post_ordinary.ps_stack /\
  residual_pressure_post_ordinary.ps_spilled = FEMPTY
Proof
  rewrite_tac[native_pressure_lv_def, residual_pressure_liveness_cache] >> EVAL_TAC >> simp[]
QED

(* Actual saved sibling inventories, not the result inventory of R's subtree. *)
Theorem pressure_sibling_resource_rows:
  resource_probe_row native_pressure_left_start residual_pressure_names = REPLICATE 17 1 /\
  resource_probe_row native_pressure_left_after ("a" :: residual_pressure_names) =
    REPLICATE 18 1 /\
  native_pressure_left_start.ps_spilled = FEMPTY /\
  native_pressure_left_after.ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED
