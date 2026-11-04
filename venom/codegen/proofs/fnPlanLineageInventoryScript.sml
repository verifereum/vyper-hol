Theory fnPlanLineageInventory
Ancestors
  fnPlanLineageReplay stackPlanGen stackModel list rich_list
Libs
  pred_setTheory finite_mapTheory stackPlanOpsTheory

(* Stack-only comparison; state-field agreement is a separate obligation. *)
Definition bottom_dead_equiv_def:
  bottom_dead_equiv xs ys <=>
    ?m n core.
      xs = REPLICATE m dead_stack_marker ++ core /\
      ys = REPLICATE n dead_stack_marker ++ core /\
      ~MEM dead_stack_marker core
End

Theorem bottom_dead_equiv_refl:
  !xs. ~MEM dead_stack_marker xs ==> bottom_dead_equiv xs xs
Proof
  rpt strip_tac >> simp[bottom_dead_equiv_def] >>
  qexistsl_tac [`0`, `0`, `xs`] >> simp[]
QED

Theorem bottom_dead_equiv_sym:
  !xs ys. bottom_dead_equiv xs ys ==> bottom_dead_equiv ys xs
Proof
  simp[bottom_dead_equiv_def] >> metis_tac[]
QED

Theorem bottom_dead_equiv_depth:
  !xs ys op. bottom_dead_equiv xs ys /\ op <> dead_stack_marker ==>
    stack_get_depth op xs = stack_get_depth op ys
Proof
  rpt gen_tac >> simp[bottom_dead_equiv_def] >> rpt strip_tac >>
  gvs[stack_get_depth_bottom_dead]
QED

Theorem bottom_dead_equiv_below_all_live:
  !xs ys op inputs.
    bottom_dead_equiv xs ys /\ op <> dead_stack_marker ==>
    below_all_live op inputs xs = below_all_live op inputs ys
Proof
  rpt strip_tac >>
  `stack_get_depth op xs = stack_get_depth op ys` by
    metis_tac[bottom_dead_equiv_depth] >>
  simp[below_all_live_def] >>
  Cases_on `stack_get_depth op ys` >> simp[] >>
  `!v. stack_get_depth (Var v) xs = stack_get_depth (Var v) ys` by
    (gen_tac >> irule bottom_dead_equiv_depth >>
     simp[dead_stack_marker_def]) >>
  simp[]
QED

(* Negative interface probe: coverage cannot replace physical swap bounds.
   This is not a counterexample to lineage_state_block_plan. *)
Theorem short_stack_swap_prefix_probe[local]:
  stack_swap 2 [dead_stack_marker; Var "a"] <>
    dead_stack_marker :: stack_swap 2 [Var "a"]
Proof
  EVAL_TAC
QED

Theorem bottom_dead_equiv_physical:
  !xs ys ops.
    bottom_dead_equiv xs ys /\ ~MEM dead_stack_marker ops ==>
    FILTER (\op. IS_SOME (stack_get_depth op xs)) ops =
    FILTER (\op. IS_SOME (stack_get_depth op ys)) ops
Proof
  Induct_on `ops` >> simp[] >> rpt strip_tac >>
  `stack_get_depth h xs = stack_get_depth h ys` by
    metis_tac[bottom_dead_equiv_depth] >>
  first_x_assum drule >> simp[] >> disch_then SUBST1_TAC >> simp[]
QED

(* Mixed stack/spill inventory: only the spilled target is restored, and the
   dead bottom extension does not change emitted code. *)
Theorem mixed_restore_prefix_probe[local]:
  FST (restore_spilled_plan [Var "a"; Var "b"]
    ((init_plan_state 0) with <|
      ps_stack := [Var "a"];
      ps_spilled := FEMPTY |+ (Var "b", 0) |>)) = [SORestore 0] /\
  FST (restore_spilled_plan [Var "a"; Var "b"]
    ((init_plan_state 0) with <|
      ps_stack := [dead_stack_marker; Var "a"];
      ps_spilled := FEMPTY |+ (Var "b", 0) |>)) = [SORestore 0]
Proof
  EVAL_TAC
QED

(* Shared PHI alternatives do not need to be distinct for slot selection. *)
Theorem shared_phi_depth_probe[local]:
  stack_get_phi_depth [Var "a"; Var "a"] [Var "a"] = SOME 0 /\
  stack_get_phi_depth [Var "a"; Var "a"]
    [dead_stack_marker; Var "a"] = SOME 0
Proof
  EVAL_TAC
QED

(* Concrete wide targets exercise both sides of SWAP16. *)
Definition probe_targets_def:
  probe_targets n = GENLIST (\i. Var (IMPLODE (REPLICATE (SUC i) #"x"))) n
End

Definition probe_join_def:
  probe_join targets ps =
    (FST (restore_spilled_plan targets ps) ++
       FST (reorder_plan dfg_empty targets
         (SND (restore_spilled_plan targets ps))),
     SND (reorder_plan dfg_empty targets
       (SND (restore_spilled_plan targets ps))))
End

Definition probe_spilled_state_def:
  probe_spilled_state targets prefix =
    (init_plan_state 0) with <|
      ps_stack := prefix;
      ps_spilled := FEMPTY |++ MAPi (\i op. (op, 32 * i)) targets |>
End

Theorem all_spilled_join_prefix_probe[local]:
  EVERY (\n.
    FST (probe_join (probe_targets n)
      (probe_spilled_state (probe_targets n) [])) =
    FST (probe_join (probe_targets n)
      (probe_spilled_state (probe_targets n) [dead_stack_marker])))
    [16; 17; 18]
Proof
  simp [EVERY_DEF] >> rpt conj_tac >>
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

Theorem mixed_wide_join_prefix_probe[local]:
  EVERY (\n.
    FST (probe_join (probe_targets n)
      (probe_spilled_state (TL (probe_targets n)) [HD (probe_targets n)])) =
    FST (probe_join (probe_targets n)
      (probe_spilled_state (TL (probe_targets n))
        [dead_stack_marker; HD (probe_targets n)]))) [17; 18]
Proof
  simp [EVERY_DEF] >> rpt conj_tac >>
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

Theorem spilled_join_stack_probe[local]:
  EVERY (\n.
    (SND (probe_join (probe_targets n)
      (probe_spilled_state (probe_targets n) [dead_stack_marker]))).ps_stack =
    dead_stack_marker ::
    (SND (probe_join (probe_targets n)
      (probe_spilled_state (probe_targets n) []))).ps_stack) [16; 17; 18]
Proof
  simp [EVERY_DEF] >> rpt conj_tac >>
  CONV_TAC (LAND_CONV EVAL) >> CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

Definition probe_param_fn_def:
  probe_param_fn = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [Lit 0w] ["x"];
       mk_inst 1 RETPC_PARAM [] ["retpc"];
       mk_inst 2 RET [Var "x"; Var "retpc"] []] |>]
End

Theorem param_setup_prefix_probe[local]:
  FST (prepare_params_plan (liveness_analyze probe_param_fn) probe_param_fn
    (init_plan_state 0)) =
  FST (prepare_params_plan (liveness_analyze probe_param_fn) probe_param_fn
    ((init_plan_state 0) with ps_stack := [dead_stack_marker])) /\
  (SND (prepare_params_plan (liveness_analyze probe_param_fn) probe_param_fn
    ((init_plan_state 0) with ps_stack := [dead_stack_marker]))).ps_stack =
  dead_stack_marker ::
  (SND (prepare_params_plan (liveness_analyze probe_param_fn) probe_param_fn
    (init_plan_state 0))).ps_stack
Proof
  conj_tac >> CONV_TAC (LAND_CONV EVAL) >>
  CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

Theorem shared_phi_rename_probe[local]:
  generate_phi_plan (mk_inst 0 PHI [Var "a"; Var "a"] ["out"])
    ["out"] F ((init_plan_state 0) with ps_stack := [dead_stack_marker; Var "a"]) =
  ([SOPoke 0 (Var "out")],
    (init_plan_state 0) with ps_stack := [dead_stack_marker; Var "out"])
Proof
  irule EQ_TRANS >>
  irule_at Any generate_phi_plan_rename_only >>
  qexists_tac `0` >> EVAL_TAC
QED

(* Retaining the dead bottom segment preserves a marker-free live core;
   empty inputs permit retaining the entire physical stack. *)
Theorem cleanup_mark_partition_probe[local]:
  FILTER (\op. below_all_live op ["c"] [Var "a"; Var "b"; Var "c"])
    [Var "a"; Var "b"] = [Var "a"; Var "b"] /\
  mark_dead_stack [Var "a"; Var "b"] [Var "a"; Var "b"; Var "c"] =
    [dead_stack_marker; dead_stack_marker; Var "c"] /\
  FILTER (\op. below_all_live op [] [Var "a"; Var "b"])
    [Var "a"; Var "b"] = [Var "a"; Var "b"] /\
  mark_dead_stack [Var "a"; Var "b"] [Var "a"; Var "b"] =
    [dead_stack_marker; dead_stack_marker]
Proof
  EVAL_TAC
QED

Definition lineage_core_def:
  lineage_core m core ps <=>
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core
End

Definition lineage_inventory_def:
  lineage_inventory S ps <=>
    ?m core. lineage_core m core ps /\ ALL_DISTINCT core /\
      EVERY is_var_operand core /\
      DISJOINT (set core) (FDOM ps.ps_spilled) /\
      set core UNION FDOM ps.ps_spilled = S /\
      (!op. op IN FDOM ps.ps_spilled ==> is_var_operand op)
End

Theorem lineage_inventory_stack_subset:
  !S ps. lineage_inventory S ps ==>
    set ps.ps_stack SUBSET (dead_stack_marker INSERT S)
Proof
  simp[lineage_inventory_def, lineage_core_def] >> rpt strip_tac >>
  gvs[SUBSET_DEF, MEM_APPEND, MEM_REPLICATE] >> metis_tac[IN_UNION]
QED

Theorem lineage_inventory_spilled_subset:
  !S ps. lineage_inventory S ps ==> FDOM ps.ps_spilled SUBSET S
Proof
  simp[lineage_inventory_def] >> SET_TAC[]
QED

Theorem do_restore_lineage_inventory:
  !S ps op. lineage_inventory S ps ==>
    lineage_inventory S (SND (do_restore op ps))
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ps.ps_spilled op`
  >- simp[do_restore_def] >>
  simp[do_restore_def, lineage_inventory_def, lineage_core_def] >>
  rpt strip_tac >>
  `op IN FDOM ps.ps_spilled` by gvs[FLOOKUP_DEF] >>
  `~MEM op core` by metis_tac[DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] >>
  qexistsl_tac [`m`, `core ++ [op]`] >>
  simp[stack_push_def, ALL_DISTINCT_APPEND, EVERY_APPEND, FDOM_DOMSUB] >>
  ASM_SET_TAC[]
QED

Theorem restore_spilled_plan_lineage_inventory:
  !ops S ps. lineage_inventory S ps ==>
    lineage_inventory S (SND (restore_spilled_plan ops ps))
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt strip_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[do_restore_lineage_inventory, pairTheory.SND]
QED

Theorem do_restore_spilled_domain:
  !op ps. FDOM (SND (do_restore op ps)).ps_spilled =
    FDOM ps.ps_spilled DELETE op
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, FDOM_DOMSUB] >>
  gvs[FLOOKUP_DEF] >> ASM_SET_TAC[]
QED

Theorem restore_spilled_plan_domain:
  !ops ps. FDOM (SND (restore_spilled_plan ops ps)).ps_spilled =
    FDOM ps.ps_spilled DIFF set ops
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspec_then `ps1` mp_tac) >> simp[] >> strip_tac >>
  qspecl_then [`h`, `ps`] mp_tac do_restore_spilled_domain >>
  simp[] >> strip_tac >> ASM_SET_TAC[]
QED

Theorem restore_spilled_plan_inventory_exhausted:
  !S ps ops. lineage_inventory S ps /\ S SUBSET set ops ==>
    (SND (restore_spilled_plan ops ps)).ps_spilled = FEMPTY
Proof
  rpt strip_tac >>
  drule lineage_inventory_spilled_subset >> strip_tac >>
  simp[GSYM FDOM_EQ_EMPTY, restore_spilled_plan_domain] >> ASM_SET_TAC[]
QED

Theorem lineage_inventory_target_suffix:
  !targets ps.
    lineage_inventory (set targets) ps /\ ALL_DISTINCT targets /\
    ~MEM dead_stack_marker targets /\
    (?prefix. ps.ps_stack = prefix ++ targets) ==>
    ps.ps_spilled = FEMPTY /\
    ?m. ps.ps_stack = REPLICATE m dead_stack_marker ++ targets
Proof
  simp[lineage_inventory_def, lineage_core_def] >> rpt strip_tac >>
  `FILTER (\op. op <> dead_stack_marker) core = core` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >> ASM_SET_TAC[]) >>
  `FILTER (\op. op <> dead_stack_marker) targets = targets` by
    simp[FILTER_EQ_ID, EVERY_MEM] >>
  `FILTER (\op. op <> dead_stack_marker) (REPLICATE m dead_stack_marker) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >>
  `core = FILTER (\op. op <> dead_stack_marker) prefix ++ targets` by
    (qpat_x_assum `ps.ps_stack = prefix ++ targets` (mp_tac o
       AP_TERM ``FILTER (\op. op <> dead_stack_marker)``) >>
     simp[FILTER_APPEND]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  `FILTER (\op. op <> dead_stack_marker) prefix = []` by
    (Cases_on `FILTER (\op. op <> dead_stack_marker) prefix` >>
     gvs[] >> ASM_SET_TAC[]) >>
  gvs[] >>
  `FDOM ps.ps_spilled = {}` by ASM_SET_TAC[] >>
  gvs[FDOM_EQ_EMPTY] >> metis_tac[]
QED
