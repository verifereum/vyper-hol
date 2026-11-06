Theory fnPlanLineageInventory
Ancestors
  fnPlanLineageSort fnPlanLineageSuffix fnPlanLineageReplay fnPlanLineageReduction genericInputReady reorderSim fnPlanLineageReorder doSwapSim stackPlanGen stackModel list rich_list
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

Theorem release_spill_pairs_domain[local]:
  !pairs ps.
    FDOM (FOLDL (\ps' (op,off).
      ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps pairs).ps_spilled =
    FDOM ps.ps_spilled DIFF set (MAP FST pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  simp[FDOM_DOMSUB] >> ASM_SET_TAC[]
QED

Theorem release_dead_spills_domain:
  !next ps. FDOM (release_dead_spills next ps).ps_spilled =
    FDOM ps.ps_spilled INTER set (MAP Var next)
Proof
  rpt gen_tac >>
  simp[release_dead_spills_def, release_spill_pairs_domain, EXTENSION,
       MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD,
       alistTheory.MEM_pair_fmap_to_alist_FLOOKUP] >>
  gen_tac >> Cases_on `x` >> simp[] >>
  gvs[FLOOKUP_DEF] >> metis_tac[]
QED

(* JMP integration boundary (not a reachable-state replay theorem):
   compute_operands JMP = [], and a well-formed JMP has no outputs.
   Thus its input emission and subsequent reorder of [] are identities;
   consuming zero operands and pushing no outputs do not change the map.
   generate_emit_ops for JMP changes no persistent spills.  Its join branch
   restores targets then reorders them, and its no-output postfix releases
   dead spills, exactly the three map stages below.
   For an actual edge cur -> target, targets are
     MAP Var (input_vars_from cur target_bb.bb_instructions
                (live_vars_at liveness target 0)).
   The remaining consumer premise is inclusion of MAP Var next_liveness
   in these targets (at the terminal JMP, next_liveness is the predecessor's
   analyzed live-out).  This inclusion is not supplied by this generic
   boundary, nor does empty persistent domain equate scratch allocators
   or establish temporal PHI shielding of residual stack prefixes. *)
Theorem restore_reorder_release_spilled_empty:
  !targets next dfg ps rOps psR qOps psQ.
    restore_spilled_plan targets ps = (rOps,psR) /\
    reorder_plan dfg targets psR = (qOps,psQ) /\
    set (MAP Var next) SUBSET set targets ==>
    (release_dead_spills next psQ).ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `FDOM psR.ps_spilled = FDOM ps.ps_spilled DIFF set targets` by
    (qspec_then `targets` (qspec_then `ps` mp_tac)
      restore_spilled_plan_domain >> simp[]) >>
  simp[GSYM FDOM_EQ_EMPTY, release_dead_spills_domain, EXTENSION] >>
  gen_tac >> Cases_on `MEM x (MAP Var next)` >> simp[] >>
  `MEM x targets /\ x NOTIN FDOM psR.ps_spilled` by ASM_SET_TAC[] >>
  drule_all reorder_plan_pending_not_spilled >>
  disch_then (qspec_then `dfg` mp_tac) >> simp[]
QED

Theorem generate_inst_plan_jmp_spilled_empty:
  !liveness dfg cfg fn inst next halt term cur ps targets ops ps'.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops liveness fn cur inst = SOME targets /\
    set (MAP Var next) SUBSET set targets /\
    generate_inst_plan liveness dfg cfg fn inst next halt term cur ps =
      SOME (ops,ps') ==> ps'.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rOps,psR)` >>
  Cases_on `reorder_plan dfg targets psR` >> simp[stack_pop_def] >>
  strip_tac >> gvs[] >>
  drule_all restore_reorder_release_spilled_empty >> simp[]
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

Theorem do_swap_core:
  !d ps prefix core.
    ps.ps_stack = prefix ++ core /\ d < LENGTH core /\
    ALL_DISTINCT core ==>
    (SND (do_swap d ps)).ps_stack = prefix ++ stack_swap d core /\
    ALL_DISTINCT (stack_swap d core) /\
    set (stack_swap d core) = set core
Proof
  rpt strip_tac
  >- (simp[do_swap_stack_result, stack_swap_bottom_extension])
  >- (Cases_on `d = 0`
      >- simp[stack_swap_def, LUPDATE_SAME]
      >> (`0 < d` by simp[] >> metis_tac[stack_swap_permutation]))
  >> Cases_on `d = 0`
  >- simp[stack_swap_def, LUPDATE_SAME]
  >> (`0 < d` by simp[] >> metis_tac[stack_swap_permutation])
QED

Theorem stack_pop_swap_core:
  !d prefix core.
    d < LENGTH core /\ ALL_DISTINCT core ==>
    ?core'.
      stack_pop 1 (stack_swap d (prefix ++ core)) = prefix ++ core' /\
      ALL_DISTINCT core' /\
      set core' = set core DELETE (stack_peek d core)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (stack_swap d core) /\
   set (stack_swap d core) = set core` by
    (Cases_on `d = 0`
     >- simp[stack_swap_def, LUPDATE_SAME]
     >> `0 < d` by simp[] >> metis_tac[stack_swap_permutation]) >>
  `stack_swap d core <> []` by
    (Cases_on `stack_swap d core` >> gvs[]) >>
  `LAST (stack_swap d core) = stack_peek d core` by
    (`PRE (LENGTH core) = LENGTH core - 1` by decide_tac >>
     simp[LAST_EL, stack_swap_def, stack_peek_def, EL_LUPDATE] >>
     rpt IF_CASES_TAC >> gvs[]) >>
  qexists_tac `FRONT (stack_swap d core)` >>
  conj_tac
  >- (`LENGTH prefix <= LENGTH core + LENGTH prefix - 1` by decide_tac >>
      simp[stack_swap_bottom_extension, stack_pop_def, TAKE_APPEND,
           FRONT_BY_TAKE, TAKE_LENGTH_TOO_LONG]) >>
  conj_tac >- simp[ALL_DISTINCT_FRONT] >>
  `SNOC (LAST (stack_swap d core)) (FRONT (stack_swap d core)) =
     stack_swap d core` by simp[SNOC_LAST_FRONT] >>
  `~MEM (LAST (stack_swap d core)) (FRONT (stack_swap d core))` by
    metis_tac[ALL_DISTINCT_SNOC] >>
  `set core = stack_peek d core INSERT set (FRONT (stack_swap d core))` by
    (qpat_x_assum `SNOC _ _ = _`
       (mp_tac o AP_TERM ``set : 'a list -> 'a set``) >>
     simp[SNOC_APPEND] >> SET_TAC[]) >>
  ASM_SET_TAC[]
QED

Theorem stack_get_depth_core:
  !core prefix op.
    MEM op core ==>
    ?d. stack_get_depth op (prefix ++ core) = SOME d /\
        d < LENGTH core /\ stack_peek d core = op
Proof
  Induct_on `core` using SNOC_INDUCT >> simp[] >>
  rpt gen_tac >> disch_tac >>
  rename1 `op = last \/ MEM op core` >>
  Cases_on `op = last`
  >- (gvs[] >> qexists_tac `0` >>
      simp[SNOC_APPEND, stack_get_depth_def, REVERSE_APPEND,
           stack_find_def, stack_peek_def, EL_APPEND_EQN]) >>
  gvs[MEM_SNOC] >>
  first_x_assum drule >> disch_then (qspec_then `prefix` strip_assume_tac) >>
  qexists_tac `SUC d` >>
  conj_tac
  >- gvs[stack_get_depth_def, REVERSE_SNOC, stack_find_def] >>
  `SUC d = d + 1` by decide_tac >>
  simp[] >> gvs[stack_peek_def, SNOC_APPEND, EL_APPEND_EQN]
QED

Theorem pop_core_operand:
  !op prefix core ps.
    MEM op core /\ ps.ps_stack = prefix ++ core /\ ALL_DISTINCT core ==>
    ?d core'.
      stack_get_depth op ps.ps_stack = SOME d /\
      stack_pop 1 (SND (do_swap d ps)).ps_stack = prefix ++ core' /\
      ALL_DISTINCT core' /\ set core' = set core DELETE op
Proof
  rpt gen_tac >> strip_tac >>
  drule stack_get_depth_core >>
  disch_then (qspec_then `prefix` strip_assume_tac) >>
  `d < LENGTH ps.ps_stack` by simp[] >>
  drule_all stack_pop_swap_core >>
  disch_then (qspec_then `prefix` strip_assume_tac) >>
  qexistsl_tac [`d`, `core'`] >>
  simp[do_swap_stack_result]
QED

Theorem popmany_fold_core[local]:
  !to_pop prefix core ops ps.
    ps.ps_stack = prefix ++ core /\ ALL_DISTINCT core /\
    DISJOINT (set prefix) (set to_pop) ==>
    ?core'.
      (SND (FOLDL (\(ops, ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops, ps)
        | SOME dist =>
            (ops ++ FST (if dist = 0 then ([], ps) else do_swap dist ps) ++ [SOPop 1],
             (SND (if dist = 0 then ([], ps) else do_swap dist ps)) with
               ps_stack := stack_pop 1
                 (SND (if dist = 0 then ([], ps) else do_swap dist ps)).ps_stack))
        (ops, ps) to_pop)).ps_stack = prefix ++ core' /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set to_pop
Proof
  Induct_on `to_pop` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM h core`
  >- (drule_all pop_core_operand >> strip_tac >>
      `(if d = 0 then ([], ps) else do_swap d ps) = do_swap d ps` by
        (Cases_on `d = 0` >> simp[do_swap_def]) >>
      gvs[] >>
      qmatch_goalsub_abbrev_tac `FOLDL delete_step (newops, newps) to_pop` >>
      first_x_assum (qspecl_then [`prefix`, `core'`, `newops`, `newps`] mp_tac) >>
      simp[Abbr `newps`] >>
      `set core DELETE h DIFF set to_pop = set core DIFF (h INSERT set to_pop)` by
        SET_TAC[] >>
      simp[Abbr `delete_step`]) >>
  `stack_get_depth h ps.ps_stack = NONE` by
    (simp[stack_get_depth_NONE] >> rpt strip_tac >>
     `MEM (stack_peek d (prefix ++ core)) (prefix ++ core)` by
       (pure_rewrite_tac[stack_peek_def] >> irule EL_MEM >> simp[]) >> gvs[]) >>
  gvs[] >>
  `set core DIFF (h INSERT set to_pop) = set core DIFF set to_pop` by ASM_SET_TAC[] >>
  simp[] >> first_x_assum irule >> simp[]
QED

Theorem popmany_individual_core:
  !to_pop prefix core ps.
    ps.ps_stack = prefix ++ core /\ ALL_DISTINCT core /\
    DISJOINT (set prefix) (set to_pop) ==>
    ?core'.
      (SND (popmany_individual to_pop ps)).ps_stack = prefix ++ core' /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set to_pop
Proof
  rpt gen_tac >> strip_tac >>
  simp[popmany_individual_def, LET_THM, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `FOLDL delstep _ sorted` >>
  `set sorted = set to_pop` by simp[Abbr `sorted`, EXTENSION, sortingTheory.QSORT_MEM] >>
  qspec_then `sorted` mp_tac (SRULE [pairTheory.pair_CASE_def, pairTheory.UNCURRY] popmany_fold_core) >>
  disch_then (qspecl_then [`prefix`, `core`, `[]`, `ps`] mp_tac) >>
  simp[Abbr `delstep`]
QED

Theorem popmany_individual_spilled_unchanged:
  !to_pop ps. (SND (popmany_individual to_pop ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >>
  simp[popmany_individual_def, LET_THM, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `FOLDL delstep _ sorted` >>
  `!xs acc. (SND (FOLDL delstep acc xs)).ps_spilled = (SND acc).ps_spilled` by
    (Induct >> simp[] >> rpt gen_tac >> Cases_on `acc` >>
     simp[Abbr `delstep`] >>
     Cases_on `stack_get_depth h r.ps_stack` >> simp[] >>
     Cases_on `x = 0` >> simp[do_swap_spilled_unchanged]) >>
  simp[]
QED

Theorem popmany_plan_spilled_unchanged:
  !to_pop ps. (SND (popmany_plan to_pop ps)).ps_spilled = ps.ps_spilled
Proof
  Cases >> simp[popmany_plan_def, LET_THM] >> gen_tac >>
  IF_CASES_TAC >> simp[popmany_individual_spilled_unchanged] >>
  IF_CASES_TAC >> simp[popmany_individual_spilled_unchanged] >>
  pairarg_tac >> gvs[] >> metis_tac[do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem stack_pop_contiguous:
  !base removed top.
    stack_pop (LENGTH removed)
      (stack_swap (LENGTH removed) (base ++ removed ++ [top])) = base ++ [top]
Proof
  rpt gen_tac >> Cases_on `removed`
  >- simp[stack_pop_def, stack_swap_def, LUPDATE_SAME] >>
  simp[stack_pop_def, stack_swap_def, EL_APPEND_EQN, LUPDATE_APPEND2,
       LUPDATE_APPEND1, APPEND_ASSOC, LUPDATE_def, TAKE_APPEND,
       TAKE_LENGTH_TOO_LONG, arithmeticTheory.ADD1]
QED

Theorem stack_peek_contiguous:
  !base removed top.
    MAP (\d. stack_peek d (base ++ removed ++ [top]))
      (GENLIST SUC (LENGTH removed)) = REVERSE removed
Proof
  rpt gen_tac >> simp[LIST_EQ_REWRITE] >> rpt strip_tac >>
  simp[EL_MAP, EL_GENLIST, stack_peek_def, EL_REVERSE, EL_APPEND_EQN,
       arithmeticTheory.ADD1] >>
  `LENGTH removed - (x + 1) = PRE (LENGTH removed - x)` by decide_tac >> simp[]
QED

Theorem pop_contiguous_core:
  !ps prefix base removed top to_pop.
    ps.ps_stack = prefix ++ (base ++ removed ++ [top]) /\
    ALL_DISTINCT (base ++ removed ++ [top]) /\ set to_pop = set removed ==>
    stack_pop (LENGTH removed) (SND (do_swap (LENGTH removed) ps)).ps_stack =
      prefix ++ (base ++ [top]) /\
    ALL_DISTINCT (base ++ [top]) /\
    set (base ++ [top]) = set (base ++ removed ++ [top]) DIFF set to_pop
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH removed < LENGTH ps.ps_stack` by simp[] >>
  conj_tac
  >- (simp[do_swap_stack_result, APPEND_ASSOC, stack_pop_contiguous]) >>
  gvs[ALL_DISTINCT_APPEND] >> ASM_SET_TAC[]
QED

Theorem contiguous_depths_core[local]:
  !to_pop prefix core ps.
    ps.ps_stack = prefix ++ core /\ set to_pop SUBSET set core /\
    to_pop <> [] /\
    is_contiguous_top (MAP THE (MAP (\op. stack_get_depth op ps.ps_stack) to_pop)) ==>
    LENGTH to_pop < LENGTH core /\
    set to_pop = set (MAP (\d. stack_peek d core) (GENLIST SUC (LENGTH to_pop)))
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op to_pop ==> ?d.
     stack_get_depth op ps.ps_stack = SOME d /\
     d < LENGTH core /\ stack_peek d core = op` by
    (rpt strip_tac >> `MEM op core` by ASM_SET_TAC[] >>
     drule stack_get_depth_core >> disch_then (qspec_then `prefix` mp_tac) >> simp[]) >>
  qabbrev_tac `depths = MAP THE (MAP (\op. stack_get_depth op ps.ps_stack) to_pop)` >>
  `!d. MEM d depths <=> ?op. MEM op to_pop /\ stack_get_depth op ps.ps_stack = SOME d` by
    (simp[Abbr `depths`, MEM_MAP] >> metis_tac[optionTheory.THE_DEF]) >>
  `!d. MEM d depths <=> MEM d (GENLIST SUC (LENGTH to_pop))` by
    (qpat_x_assum `is_contiguous_top _` mp_tac >>
     simp[is_contiguous_top_def, LET_THM, Abbr `depths`] >>
     strip_tac >>
     qpat_x_assum `QSORT _ _ = _` (mp_tac o AP_TERM ``set : num list -> num set``) >>
     simp[EXTENSION, sortingTheory.QSORT_MEM] >> metis_tac[]) >>
  conj_tac
  >- (`0 < LENGTH to_pop` by (Cases_on `to_pop` >> gvs[]) >>
      `MEM (LENGTH to_pop) (GENLIST SUC (LENGTH to_pop))` by
        (simp[MEM_GENLIST] >> qexists_tac `LENGTH to_pop - 1` >> simp[]) >>
      `MEM (LENGTH to_pop) depths` by metis_tac[] >>
      qpat_x_assum `!d. MEM d depths <=> ?op. _`
        (qspec_then `LENGTH to_pop` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  qpat_x_assum `ps.ps_stack = _` kall_tac >>
  qpat_x_assum `set _ SUBSET _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `is_contiguous_top _` kall_tac >>
  simp[EXTENSION, MEM_MAP] >> gen_tac >> eq_tac
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      qexists_tac `d` >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `MEM d depths` by metis_tac[] >>
  qpat_x_assum `!d. MEM d depths <=> ?op. _` (qspec_then `d` mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem popmany_contiguous_core[local]:
  !to_pop prefix core ps.
    ps.ps_stack = prefix ++ core /\ ALL_DISTINCT core /\
    set to_pop SUBSET set core /\ to_pop <> [] /\
    is_contiguous_top (MAP THE (MAP (\op. stack_get_depth op ps.ps_stack) to_pop)) ==>
    ?core'.
      stack_pop (LENGTH to_pop) (SND (do_swap (LENGTH to_pop) ps)).ps_stack =
        prefix ++ core' /\ ALL_DISTINCT core' /\
      set core' = set core DIFF set to_pop
Proof
  rpt gen_tac >> strip_tac >> drule_all contiguous_depths_core >> strip_tac >>
  `core <> []` by (strip_tac >> gvs[]) >>
  `?rest top. core = SNOC top rest` by metis_tac[SNOC_CASES] >>
  `LENGTH to_pop <= LENGTH rest` by gvs[] >>
  `?base removed top. core = base ++ removed ++ [top] /\
     LENGTH removed = LENGTH to_pop` by
    (qexistsl_tac [`TAKE (LENGTH rest - LENGTH to_pop) rest`,
                   `DROP (LENGTH rest - LENGTH to_pop) rest`, `top`] >>
     conj_tac
     >- (pure_rewrite_tac[GSYM APPEND_ASSOC, TAKE_DROP] >> simp[SNOC_APPEND]) >>
     simp[LENGTH_DROP]) >>
  `set to_pop = set removed` by
    (qpat_x_assum `LENGTH removed = _` (assume_tac o SYM) >>
     gvs[stack_peek_contiguous]) >>
  qpat_x_assum `core = SNOC _ _` kall_tac >>
  qpat_x_assum `set to_pop = set (MAP _ _)` kall_tac >>
  qpat_x_assum `is_contiguous_top _` kall_tac >>
  qpat_x_assum `core = _` SUBST_ALL_TAC >>
  drule pop_contiguous_core >>
  disch_then (qspec_then `to_pop` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem popmany_plan_core:
  !to_pop prefix core ps.
    ps.ps_stack = prefix ++ core /\ ALL_DISTINCT core /\
    DISJOINT (set prefix) (set to_pop) ==>
    ?core'.
      (SND (popmany_plan to_pop ps)).ps_stack = prefix ++ core' /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set to_pop
Proof
  Cases >- simp[popmany_plan_def] >> rpt gen_tac >> strip_tac >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`set (h::t) SUBSET set core` by
            (rewrite_tac[SUBSET_DEF, LIST_TO_SET] >> gen_tac >> disch_tac >>
             `IS_SOME (stack_get_depth x ps.ps_stack)` by
               (fs[EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
             Cases_on `stack_get_depth x ps.ps_stack` >- fs[] >>
             drule stack_get_depth_props >> strip_tac >>
             `MEM x ps.ps_stack` by
               (qpat_x_assum `stack_peek _ _ = x` (SUBST1_TAC o SYM) >>
                pure_rewrite_tac[stack_peek_def] >> irule EL_MEM >> gvs[]) >>
             gvs[] >> ASM_SET_TAC[]) >>
          drule popmany_contiguous_core >>
          disch_then (qspec_then `h::t` mp_tac) >> simp[] >>
          pairarg_tac >> gvs[]) >>
      drule popmany_individual_core >> disch_then (qspec_then `h::t` mp_tac) >> simp[]) >>
  drule popmany_individual_core >> disch_then (qspec_then `h::t` mp_tac) >> simp[]
QED

Theorem popmany_plan_lineage_inventory:
  !S ps to_pop.
    lineage_inventory S ps /\ ~MEM dead_stack_marker to_pop ==>
    lineage_inventory (S DIFF (set to_pop INTER set ps.ps_stack))
      (SND (popmany_plan to_pop ps))
Proof
  rpt gen_tac >> simp[lineage_inventory_def, lineage_core_def] >>
  rpt strip_tac >>
  `DISJOINT (set (REPLICATE m dead_stack_marker)) (set to_pop)` by
    (simp[DISJOINT_DEF, EXTENSION, MEM_REPLICATE] >> metis_tac[]) >>
  drule_all popmany_plan_core >> strip_tac >>
  qexistsl_tac [`m`, `core'`] >>
  simp[lineage_core_def, popmany_plan_spilled_unchanged] >>
  conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      `MEM e core` by ASM_SET_TAC[] >> metis_tac[]) >>
  conj_tac >- ASM_SET_TAC[] >>
  ASM_SET_TAC[]
QED

Theorem stack_find_append_miss:
  !xs ys p. EVERY (\x. ~p x) xs ==>
    stack_find p (xs ++ ys) =
      OPTION_MAP (\d. LENGTH xs + d) (stack_find p ys)
Proof
  Induct >> simp[stack_find_def] >> rpt strip_tac >>
  simp[] >> Cases_on `stack_find p ys` >> simp[]
QED

Theorem stack_get_depth_cons_other:
  !op h core. op <> h ==>
    stack_get_depth op (h::core) = stack_get_depth op core
Proof
  simp[stack_get_depth_def, REVERSE_DEF, stack_find_append_excluded]
QED

Theorem stack_get_depth_cons_head:
  !h core. ~MEM h core ==>
    stack_get_depth h (h::core) = SOME (LENGTH core)
Proof
  simp[stack_get_depth_def, REVERSE_DEF, stack_find_append_miss,
       EVERY_MEM, stack_find_def]
QED

Theorem below_all_live_cons_other:
  !op h core inputs.
    op <> h /\ ~MEM h (MAP Var inputs) ==>
    below_all_live op inputs (h::core) = below_all_live op inputs core
Proof
  rpt strip_tac >>
  `!v. MEM v inputs ==> Var v <> h` by (fs[MEM_MAP] >> metis_tac[]) >>
  simp[below_all_live_def, stack_get_depth_cons_other] >>
  Cases_on `stack_get_depth op core` >> simp[EVERY_MEM] >>
  metis_tac[stack_get_depth_cons_other]
QED

Theorem below_all_live_cons_head:
  !h core inputs. ~MEM h core /\ ~MEM h (MAP Var inputs) ==>
    below_all_live h inputs (h::core)
Proof
  rpt strip_tac >> simp[below_all_live_def, stack_get_depth_cons_head, EVERY_MEM] >>
  rpt strip_tac >>
  `Var v <> h` by (fs[MEM_MAP] >> metis_tac[]) >>
  simp[stack_get_depth_cons_other] >>
  Cases_on `stack_get_depth (Var v) core` >> simp[] >>
  metis_tac[stack_get_depth_props]
QED

Theorem below_all_live_cons_input:
  !h core inputs op.
    ~MEM h core /\ MEM h (MAP Var inputs) /\ MEM op core ==>
    ~below_all_live op inputs (h::core)
Proof
  rpt gen_tac >> strip_tac >>
  `op <> h` by metis_tac[] >>
  drule stack_get_depth_core >> disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[] >> simp[below_all_live_def, stack_get_depth_cons_other, EVERY_MEM] >>
  fs[MEM_MAP] >> qexists_tac `y` >>
  gvs[stack_get_depth_cons_head]
QED

Theorem below_all_live_prefix:
  !core inputs. ALL_DISTINCT core ==>
    ?pre tail. core = pre ++ tail /\
      DISJOINT (set pre) (set (MAP Var inputs)) /\
      (!op. MEM op core /\ ~MEM op (MAP Var inputs) ==>
        (below_all_live op inputs core <=> MEM op pre))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM h (MAP Var inputs)`
  >- (qexistsl_tac [`[]`, `h::core`] >> simp[] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[below_all_live_cons_input]) >>
  first_x_assum drule >> disch_then (qspec_then `inputs` strip_assume_tac) >>
  qexistsl_tac [`h::pre`, `tail`] >>
  simp[] >>
  rpt strip_tac >> Cases_on `op = h`
  >- (gvs[] >> irule below_all_live_cons_head >> simp[]) >>
  simp[below_all_live_cons_other] >> gvs[] >> metis_tac[]
QED

Theorem below_all_live_core_prefix:
  !m core inputs. ALL_DISTINCT core /\ EVERY is_var_operand core ==>
    ?pre tail. core = pre ++ tail /\
      DISJOINT (set pre) (set (MAP Var inputs)) /\
      (!op. MEM op core /\ ~MEM op (MAP Var inputs) ==>
        (below_all_live op inputs (REPLICATE m dead_stack_marker ++ core) <=>
         MEM op pre))
Proof
  rpt gen_tac >> strip_tac >>
  `~is_var_operand dead_stack_marker` by
    simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
  `~MEM dead_stack_marker core` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `bottom_dead_equiv (REPLICATE m dead_stack_marker ++ core) core` by
    (simp[bottom_dead_equiv_def] >> qexistsl_tac [`m`, `0`, `core`] >> simp[]) >>
  drule below_all_live_prefix >> disch_then (qspec_then `inputs` strip_assume_tac) >>
  qexistsl_tac [`pre`, `tail`] >> simp[] >> rpt strip_tac >>
  `op <> dead_stack_marker` by (gvs[] >> metis_tac[]) >>
  drule_all bottom_dead_equiv_below_all_live >> simp[] >> gvs[] >> metis_tac[]
QED

Theorem stack_get_depth_is_some:
  !op stk. IS_SOME (stack_get_depth op stk) <=> MEM op stk
Proof
  rpt gen_tac >> Cases_on `stack_get_depth op stk` >> simp[]
  >- (strip_tac >> drule stack_get_depth_core >>
      disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule stack_get_depth_props >> strip_tac >>
  qpat_x_assum `stack_peek _ _ = op` (SUBST1_TAC o SYM) >>
  pure_rewrite_tac[stack_peek_def] >> irule EL_MEM >> simp[]
QED

Theorem mark_dead_stack_prefix:
  !m pre live retained.
    set retained = set pre /\ DISJOINT (set pre) (set live) ==>
    mark_dead_stack retained (REPLICATE m dead_stack_marker ++ pre ++ live) =
      REPLICATE (m + LENGTH pre) dead_stack_marker ++ live
Proof
  rpt gen_tac >> strip_tac >>
  `MAP (\op. if MEM op retained then dead_stack_marker else op) pre =
     REPLICATE (LENGTH pre) dead_stack_marker` by
    (simp[LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE] >> rpt strip_tac >>
     `MEM (EL x pre) pre` by metis_tac[EL_MEM] >> ASM_SET_TAC[]) >>
  `MAP (\op. if MEM op retained then dead_stack_marker else op) live = live` by
    (simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
     `MEM (EL x live) live` by metis_tac[EL_MEM] >>
     `~MEM (EL x live) pre` by ASM_SET_TAC[] >> simp[]) >>
  simp[mark_dead_stack_def, LIST_EQ_REWRITE, EL_APPEND_EQN, EL_REPLICATE]
QED

Theorem cleanup_physical_core:
  !S ps m core inputs layout physical.
    lineage_inventory S ps /\ lineage_core m core ps /\
    DISJOINT (set core) (FDOM ps.ps_spilled) /\
    set core UNION FDOM ps.ps_spilled = S /\
    S SUBSET set (MAP Var inputs) UNION set (MAP Var layout) UNION FDOM ps.ps_spilled /\
    physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack))
      (MAP Var (FILTER (\v. ~MEM v inputs) layout)) ==>
    set physical = set core DIFF set (MAP Var inputs)
Proof
  rpt gen_tac >> strip_tac >>
  `set (MAP Var (FILTER (\v. ~MEM v inputs) layout)) =
     set (MAP Var layout) DIFF set (MAP Var inputs)` by
    (simp[EXTENSION, MEM_MAP, MEM_FILTER] >> Cases >> simp[] >> metis_tac[]) >>
  `set physical = set (MAP Var (FILTER (\v. ~MEM v inputs) layout)) INTER
     set ps.ps_stack` by
    (simp[EXTENSION, MEM_FILTER, stack_get_depth_is_some] >> metis_tac[]) >>
  `~MEM dead_stack_marker (MAP Var layout)` by
    simp[MEM_MAP, dead_stack_marker_def] >>
  `DISJOINT (set (REPLICATE m dead_stack_marker)) (set (MAP Var layout))` by
    (simp[DISJOINT_DEF, EXTENSION, MEM_REPLICATE] >> metis_tac[]) >>
  gvs[lineage_core_def] >> ASM_SET_TAC[]
QED

Theorem clean_stack_plan_noop:
  !liveness cfg fn bb ps.
    ~(?pred_lbl pred_bb.
      cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
      1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
      lookup_block pred_lbl fn.fn_blocks = SOME pred_bb) ==>
    clean_stack_plan liveness cfg fn bb ps = ([], ps)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- simp[clean_stack_plan_def] >>
  Cases_on `t`
  >- (Cases_on `LENGTH (cfg_succs_of cfg h) <= 1`
      >- simp[clean_stack_plan_def] >>
      `lookup_block h fn.fn_blocks = NONE` by
        (`1 < LENGTH (cfg_succs_of cfg h)` by decide_tac >>
         Cases_on `lookup_block h fn.fn_blocks` >> simp[] >> metis_tac[]) >>
      simp[clean_stack_plan_def]) >>
  simp[clean_stack_plan_def]
QED

(* The cleanup partition is independent of a bottom dead extension. *)
Theorem bottom_dead_equiv_cleanup_partitions:
  !xs ys ops inputs.
    bottom_dead_equiv xs ys /\ ~MEM dead_stack_marker ops ==>
    FILTER (\op. below_all_live op inputs xs)
      (FILTER (\op. IS_SOME (stack_get_depth op xs)) ops) =
    FILTER (\op. below_all_live op inputs ys)
      (FILTER (\op. IS_SOME (stack_get_depth op ys)) ops) /\
    FILTER (\op. ~MEM op
      (FILTER (\p. below_all_live p inputs xs)
        (FILTER (\p. IS_SOME (stack_get_depth p xs)) ops)))
      (FILTER (\op. IS_SOME (stack_get_depth op xs)) ops) =
    FILTER (\op. ~MEM op
      (FILTER (\p. below_all_live p inputs ys)
        (FILTER (\p. IS_SOME (stack_get_depth p ys)) ops)))
      (FILTER (\op. IS_SOME (stack_get_depth op ys)) ops)
Proof
  rpt gen_tac >> strip_tac >>
  `FILTER (\op. IS_SOME (stack_get_depth op xs)) ops =
   FILTER (\op. IS_SOME (stack_get_depth op ys)) ops` by
    metis_tac[bottom_dead_equiv_physical] >>
  `!op. MEM op ops ==> below_all_live op inputs xs =
                        below_all_live op inputs ys` by
    (rpt strip_tac >> irule bottom_dead_equiv_below_all_live >>
     simp[] >> metis_tac[]) >>
  `FILTER (\op. below_all_live op inputs xs)
     (FILTER (\op. IS_SOME (stack_get_depth op ys)) ops) =
   FILTER (\op. below_all_live op inputs ys)
     (FILTER (\op. IS_SOME (stack_get_depth op ys)) ops)` by
    (qpat_x_assum `!op. _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Induct_on `ops` >> simp[] >> rpt strip_tac >>
     Cases_on `IS_SOME (stack_get_depth h ys)` >> simp[] >>
     metis_tac[]) >>
  simp[]
QED

(* Deep popmany uses the bulk do_swap path, which allocates scratch slots.
   Thus a binary replay interface cannot preserve every nonstack field. *)
Theorem popmany_deep_allocator_probe[local]:
  (SND (popmany_plan [Var (IMPLODE [#"x"])]
    ((init_plan_state 0) with ps_stack := probe_targets 18))).ps_alloc <>
  (init_plan_state 0).ps_alloc
Proof
  EVAL_TAC
QED

(* Scratch allocation is shared, but need not equal the input allocator. *)
Theorem do_swap_prefix_replay:
  !d ps qs prefix prefix' core.
    d < LENGTH core /\ ps.ps_stack = prefix ++ core /\
    qs.ps_stack = prefix' ++ core /\ ps.ps_alloc = qs.ps_alloc ==>
    ?ops al.
      do_swap d ps =
        (ops, ps with <|ps_stack := prefix ++ stack_swap d core;
                       ps_alloc := al|>) /\
      do_swap d qs =
        (ops, qs with <|ps_stack := prefix' ++ stack_swap d core;
                       ps_alloc := al|>)
Proof
  rpt strip_tac >> Cases_on `d <= 16`
  >- (Cases_on `d = 0`
      >- (qexistsl_tac [`[]`, `ps.ps_alloc`] >>
          simp[do_swap_def, stack_swap_def, LUPDATE_SAME,
               stackPlanTypesTheory.plan_state_component_equality]) >>
      qexistsl_tac [`[SOSwap d]`, `ps.ps_alloc`] >>
      simp[do_swap_def, stack_swap_bottom_extension,
           stackPlanTypesTheory.plan_state_component_equality]) >>
  `top_n (d + 1) ps.ps_stack = top_n (d + 1) core /\
   top_n (d + 1) qs.ps_stack = top_n (d + 1) core` by
    simp[top_n_def, TAKE_APPEND] >>
  `d < LENGTH ps.ps_stack /\ d < LENGTH qs.ps_stack` by simp[] >>
  `((SND (do_swap d ps)).ps_stack = prefix ++ stack_swap d core) /\
   ((SND (do_swap d qs)).ps_stack = prefix' ++ stack_swap d core)` by
    simp[do_swap_stack_result, stack_swap_bottom_extension] >>
  qspec_then `d` mp_tac do_swap_big_decompose >>
  disch_then (qspec_then `ps` mp_tac) >>
  qspec_then `d` mp_tac do_swap_big_decompose >>
  disch_then (qspec_then `qs` mp_tac) >>
  simp[LET_THM] >> rpt strip_tac >>
  gvs[] >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED


Theorem popmany_fold_prefix_replay[local]:
  !b c p q requests core al ops0.
    ALL_DISTINCT core /\ DISJOINT (set p) (set requests) /\
    DISJOINT (set q) (set requests) ==>
    ?ops core' al'.
      FOLDL (\(ops, ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops, ps)
        | SOME d =>
          (ops ++ FST (do_swap d ps) ++ [SOPop 1],
           (SND (do_swap d ps)) with ps_stack :=
             stack_pop 1 (SND (do_swap d ps)).ps_stack))
        (ops0, b with <|ps_stack := p ++ core; ps_alloc := al|>) requests =
        (ops, b with <|ps_stack := p ++ core'; ps_alloc := al'|>) /\
      FOLDL (\(ops, ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops, ps)
        | SOME d =>
          (ops ++ FST (do_swap d ps) ++ [SOPop 1],
           (SND (do_swap d ps)) with ps_stack :=
             stack_pop 1 (SND (do_swap d ps)).ps_stack))
        (ops0, c with <|ps_stack := q ++ core; ps_alloc := al|>) requests =
        (ops, c with <|ps_stack := q ++ core'; ps_alloc := al'|>) /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set requests
Proof
  ntac 4 gen_tac >> Induct_on `requests`
  >- (rpt strip_tac >> qexistsl_tac [`ops0`, `core`, `al`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~MEM h p /\ ~MEM h q` by (gvs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[stack_get_depth_bottom_excluded] >>
  Cases_on `MEM h core`
  >- (drule stack_get_depth_core >>
      disch_then (qspec_then `[]` strip_assume_tac) >> gvs[] >>
      `?ops al'.
        do_swap d (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
          (ops, b with <|ps_stack := p ++ stack_swap d core; ps_alloc := al'|>) /\
        do_swap d (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
          (ops, c with <|ps_stack := q ++ stack_swap d core; ps_alloc := al'|>)` by
        (drule do_swap_prefix_replay >>
         disch_then (qspecl_then
           [`b with <|ps_stack := p ++ core; ps_alloc := al|>`,
            `c with <|ps_stack := q ++ core; ps_alloc := al|>`, `p`, `q`] mp_tac) >>
         simp[]) >>
      `!r. stack_pop 1 (r ++ stack_swap d core) =
           r ++ stack_pop 1 (stack_swap d core)` by
        (gen_tac >> simp[stack_pop_def, TAKE_APPEND, stack_swap_def, LENGTH_TAKE]) >>
      drule_all stack_pop_swap_core >>
      disch_then (qspec_then `[]` strip_assume_tac) >>
      gvs[stack_swap_bottom_extension] >> simp[] >>
      first_x_assum (qspecl_then
        [`stack_pop 1 (stack_swap d core)`, `al'`, `ops0 ++ ops ++ [SOPop 1]`]
        mp_tac) >>
      simp[] >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >> ASM_SET_TAC[]) >>
  `stack_get_depth h core = NONE` by
    (simp[stack_get_depth_NONE, stack_peek_def] >> rpt strip_tac >>
     qpat_x_assum `~MEM h core` mp_tac >> simp[MEM_EL] >>
     qexists_tac `LENGTH core - (d + 1)` >> simp[]) >>
  `set core DIFF (h INSERT set requests) = set core DIFF set requests` by
    ASM_SET_TAC[] >>
  simp[] >> first_x_assum irule >> gvs[DISJOINT_ALT]
QED


Theorem popmany_individual_prefix_replay:
  !b c p q core al requests.
    ALL_DISTINCT core /\ DISJOINT (set p) (set requests) /\
    DISJOINT (set q) (set requests) ==>
    ?ops core' al'.
      popmany_individual requests
        (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
        (ops, b with <|ps_stack := p ++ core'; ps_alloc := al'|>) /\
      popmany_individual requests
        (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
        (ops, c with <|ps_stack := q ++ core'; ps_alloc := al'|>) /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set requests
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v requests ==>
    stack_get_depth v (p ++ core) = stack_get_depth v core /\
    stack_get_depth v (q ++ core) = stack_get_depth v core` by
    (rpt strip_tac >> irule stack_get_depth_bottom_excluded >>
     gvs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[popmany_individual_def, LET_THM, pairTheory.pair_CASE_def,
       pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `QSORT cmp1 requests` >>
  qabbrev_tac `cmp2 = (\a b. case (stack_get_depth a (q ++ core),
      stack_get_depth b (q ++ core)) of
      (SOME da, SOME db) => da <= db | _ => T)` >>
  `QSORT cmp1 requests = QSORT cmp2 requests` by
    (irule qsort_relation_on >> simp[Abbr `cmp1`, Abbr `cmp2`]) >>
  `!d ps. (if d = 0 then ([], ps) else do_swap d ps) = do_swap d ps` by
    (rpt gen_tac >> Cases_on `d = 0` >> simp[do_swap_def]) >>
  simp[] >>
  qspec_then `b` mp_tac popmany_fold_prefix_replay >>
  disch_then (qspecl_then [`c`, `p`, `q`, `QSORT cmp2 requests`] mp_tac) >>
  simp[sortingTheory.QSORT_MEM, EXTENSION] >>
  disch_then (qspecl_then [`core`, `al`, `[]`] mp_tac) >>
  simp[DISJOINT_ALT, sortingTheory.QSORT_MEM, Abbr `cmp2`,
       pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  gvs[DISJOINT_ALT]
QED

Theorem popmany_plan_prefix_replay:
  !requests b c p q core al.
    ALL_DISTINCT core /\ DISJOINT (set p) (set requests) /\
    DISJOINT (set q) (set requests) ==>
    ?ops core' al'.
      popmany_plan requests
        (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
        (ops, b with <|ps_stack := p ++ core'; ps_alloc := al'|>) /\
      popmany_plan requests
        (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
        (ops, c with <|ps_stack := q ++ core'; ps_alloc := al'|>) /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set requests
Proof
  Cases
  >- (rpt strip_tac >> qexistsl_tac [`[]`, `core`, `al`] >> simp[popmany_plan_def]) >>
  rpt gen_tac >> strip_tac >>
  `!v. MEM v (h::t) ==>
    stack_get_depth v (p ++ core) = stack_get_depth v core /\
    stack_get_depth v (q ++ core) = stack_get_depth v core` by
    (rpt strip_tac >> irule stack_get_depth_bottom_excluded >>
     gvs[DISJOINT_ALT] >> metis_tac[]) >>
  `MAP (\v. stack_get_depth v (p ++ core)) (h::t) =
   MAP (\v. stack_get_depth v core) (h::t) /\
   MAP (\v. stack_get_depth v (q ++ core)) (h::t) =
   MAP (\v. stack_get_depth v core) (h::t)` by
    (conj_tac >> irule MAP_CONG >> simp[]) >>
  gvs[] >> simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`set (h::t) SUBSET set core` by
            (rewrite_tac[SUBSET_DEF, LIST_TO_SET] >> gen_tac >> disch_tac >>
             `IS_SOME (stack_get_depth x core)` by
               (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
             Cases_on `stack_get_depth x core` >- gvs[] >>
             drule stackModelTheory.stack_get_depth_props >> strip_tac >>
             qpat_x_assum `stack_peek _ _ = x` (SUBST1_TAC o SYM) >>
             simp[stack_peek_def] >> irule EL_MEM >> simp[]) >>
          `LENGTH (h::t) < LENGTH core` by
            (irule (cj 1 contiguous_depths_core) >> simp[] >>
             qexistsl_tac [`[]`, `b with ps_stack := core`] >> simp[]) >>
          gvs[] >>
          `?core'. stack_pop (LENGTH (h::t)) (stack_swap (LENGTH (h::t)) core) = core' /\
            ALL_DISTINCT core' /\ set core' = set core DIFF set (h::t)` by
            (mp_tac popmany_contiguous_core >>
             disch_then (qspecl_then [`h::t`, `[]`, `core`, `b with ps_stack := core`] mp_tac) >>
             simp[do_swap_stack_result]) >>
          `?ops al'.
            do_swap (LENGTH (h::t)) (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
              (ops, b with <|ps_stack := p ++ stack_swap (LENGTH (h::t)) core; ps_alloc := al'|>) /\
            do_swap (LENGTH (h::t)) (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
              (ops, c with <|ps_stack := q ++ stack_swap (LENGTH (h::t)) core; ps_alloc := al'|>)` by
            (drule do_swap_prefix_replay >>
             disch_then (qspecl_then
               [`b with <|ps_stack := p ++ core; ps_alloc := al|>`,
                `c with <|ps_stack := q ++ core; ps_alloc := al|>`, `p`, `q`] mp_tac) >> simp[]) >>
          `!r. stack_pop (LENGTH (h::t)) (r ++ stack_swap (LENGTH (h::t)) core) =
               r ++ core'` by
            (gen_tac >> qpat_x_assum `stack_pop _ _ = core'` (SUBST1_TAC o SYM) >>
             simp[stack_pop_def, TAKE_APPEND, stack_swap_def, LENGTH_TAKE]) >>
          qexistsl_tac [`ops ++ [SOPop (LENGTH (h::t))]`, `core'`, `al'`] >> gvs[]) >>
      simp[] >> once_rewrite_tac[GSYM LIST_TO_SET_THM] >>
      irule popmany_individual_prefix_replay >> simp[]) >>
  simp[] >> once_rewrite_tac[GSYM LIST_TO_SET_THM] >>
      irule popmany_individual_prefix_replay >> simp[]
QED

Theorem popmany_plan_prefix_frame:
  !requests ps qs p q core.
    ALL_DISTINCT core /\ DISJOINT (set p) (set requests) /\
    DISJOINT (set q) (set requests) /\
    ps.ps_stack = p ++ core /\ qs.ps_stack = q ++ core /\
    ps.ps_alloc = qs.ps_alloc ==>
    ?ops core' al.
      popmany_plan requests ps =
        (ops, ps with <|ps_stack := p ++ core'; ps_alloc := al|>) /\
      popmany_plan requests qs =
        (ops, qs with <|ps_stack := q ++ core'; ps_alloc := al|>) /\
      ALL_DISTINCT core' /\ set core' = set core DIFF set requests
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `requests` mp_tac popmany_plan_prefix_replay >>
  disch_then (qspecl_then [`ps`, `qs`, `p`, `q`] mp_tac) >>
  disch_then (qspecl_then [`core`, `ps.ps_alloc`] mp_tac) >>
  simp[] >>
  qpat_x_assum `ps.ps_stack = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `qs.ps_stack = _` (SUBST1_TAC o SYM) >> simp[]
QED

(* Count-free physical replay: unlike the inventory interface above, this
   makes no claim that popping one occurrence removes its value from the set. *)
Theorem popmany_fold_shared_core_replay[local]:
  !b c p q requests core al ops0.
    DISJOINT (set p) (set requests) /\ DISJOINT (set q) (set requests) ==>
    ?ops core' al'.
      FOLDL (\(ops, ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops, ps)
        | SOME d =>
          (ops ++ FST (do_swap d ps) ++ [SOPop 1],
           (SND (do_swap d ps)) with ps_stack :=
             stack_pop 1 (SND (do_swap d ps)).ps_stack))
        (ops0, b with <|ps_stack := p ++ core; ps_alloc := al|>) requests =
        (ops, b with <|ps_stack := p ++ core'; ps_alloc := al'|>) /\
      FOLDL (\(ops, ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops, ps)
        | SOME d =>
          (ops ++ FST (do_swap d ps) ++ [SOPop 1],
           (SND (do_swap d ps)) with ps_stack :=
             stack_pop 1 (SND (do_swap d ps)).ps_stack))
        (ops0, c with <|ps_stack := q ++ core; ps_alloc := al|>) requests =
        (ops, c with <|ps_stack := q ++ core'; ps_alloc := al'|>)
Proof
  ntac 4 gen_tac >> Induct_on `requests`
  >- (rpt strip_tac >> qexistsl_tac [`ops0`, `core`, `al`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~MEM h p /\ ~MEM h q` by (gvs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[stack_get_depth_bottom_excluded] >>
  Cases_on `stack_get_depth h core`
  >- (simp[] >> first_x_assum irule >> gvs[DISJOINT_ALT]) >>
  rename1 `stack_get_depth h core = SOME d` >>
  drule stackModelTheory.stack_get_depth_props >> strip_tac >>
  `?ops al'.
    do_swap d (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
      (ops, b with <|ps_stack := p ++ stack_swap d core; ps_alloc := al'|>) /\
    do_swap d (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
      (ops, c with <|ps_stack := q ++ stack_swap d core; ps_alloc := al'|>)` by
    (drule do_swap_prefix_replay >>
     disch_then (qspecl_then
       [`b with <|ps_stack := p ++ core; ps_alloc := al|>`,
        `c with <|ps_stack := q ++ core; ps_alloc := al|>`, `p`, `q`] mp_tac) >>
     simp[]) >>
  `!r. stack_pop 1 (r ++ stack_swap d core) =
    r ++ stack_pop 1 (stack_swap d core)` by
    (gen_tac >> simp[stack_pop_def, TAKE_APPEND, stack_swap_def, LENGTH_TAKE]) >>
  simp[] >> first_x_assum irule >> gvs[DISJOINT_ALT]
QED

Theorem popmany_individual_shared_core_replay[local]:
  !b c p q core al requests.
    DISJOINT (set p) (set requests) /\ DISJOINT (set q) (set requests) ==>
    ?ops core' al'.
      popmany_individual requests
        (b with <|ps_stack := p ++ core; ps_alloc := al|>) =
        (ops, b with <|ps_stack := p ++ core'; ps_alloc := al'|>) /\
      popmany_individual requests
        (c with <|ps_stack := q ++ core; ps_alloc := al|>) =
        (ops, c with <|ps_stack := q ++ core'; ps_alloc := al'|>)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v requests ==>
    stack_get_depth v (p ++ core) = stack_get_depth v core /\
    stack_get_depth v (q ++ core) = stack_get_depth v core` by
    (rpt strip_tac >> irule stack_get_depth_bottom_excluded >>
     gvs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[popmany_individual_def, LET_THM, pairTheory.pair_CASE_def,
       pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `QSORT cmp1 requests` >>
  qabbrev_tac `cmp2 = (\a b. case (stack_get_depth a (q ++ core),
      stack_get_depth b (q ++ core)) of
      (SOME da, SOME db) => da <= db | _ => T)` >>
  `QSORT cmp1 requests = QSORT cmp2 requests` by
    (irule qsort_relation_on >> simp[Abbr `cmp1`, Abbr `cmp2`]) >>
  `!d ps. (if d = 0 then ([], ps) else do_swap d ps) = do_swap d ps` by
    (rpt gen_tac >> Cases_on `d = 0` >> simp[do_swap_def]) >>
  simp[] >>
  qspec_then `b` mp_tac popmany_fold_shared_core_replay >>
  disch_then (qspecl_then [`c`, `p`, `q`, `QSORT cmp2 requests`] mp_tac) >>
  simp[sortingTheory.QSORT_MEM, EXTENSION] >>
  disch_then (qspecl_then [`core`, `al`, `[]`] mp_tac) >>
  simp[DISJOINT_ALT, sortingTheory.QSORT_MEM, Abbr `cmp2`,
       pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  gvs[DISJOINT_ALT]
QED

Theorem contiguous_top_depth_floor[local]:
  !requests core.
    requests <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v core) requests) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v core) requests)) ==>
    LENGTH requests < LENGTH core
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (LENGTH requests) (GENLIST SUC (LENGTH requests))` by
    (simp[MEM_GENLIST] >> qexists_tac `PRE (LENGTH requests)` >>
     Cases_on `requests` >> gvs[]) >>
  `MEM (LENGTH requests) (MAP THE (MAP (\v. stack_get_depth v core) requests))` by
    (gvs[is_contiguous_top_def] >> metis_tac[sortingTheory.QSORT_MEM]) >>
  gvs[MEM_MAP, EVERY_MEM] >>
  `IS_SOME (stack_get_depth v core)` by metis_tac[] >>
  Cases_on `stack_get_depth v core` >> gvs[] >>
  metis_tac[stackModelTheory.stack_get_depth_props]
QED

Theorem popmany_plan_shared_core_replay:
  !requests ps qs p q core.
    DISJOINT (set p) (set requests) /\ DISJOINT (set q) (set requests) /\
    ps.ps_stack = p ++ core /\ qs.ps_stack = q ++ core /\
    ps.ps_alloc = qs.ps_alloc ==>
    ?ops core' al.
      popmany_plan requests ps =
        (ops, ps with <|ps_stack := p ++ core'; ps_alloc := al|>) /\
      popmany_plan requests qs =
        (ops, qs with <|ps_stack := q ++ core'; ps_alloc := al|>)
Proof
  Cases
  >- (rpt strip_tac >> qexistsl_tac [`[]`, `core`, `ps.ps_alloc`] >>
      simp[popmany_plan_def, stackPlanTypesTheory.plan_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  `!v. MEM v (h::t) ==>
    stack_get_depth v (p ++ core) = stack_get_depth v core /\
    stack_get_depth v (q ++ core) = stack_get_depth v core` by
    (rpt strip_tac >> irule stack_get_depth_bottom_excluded >>
     gvs[DISJOINT_ALT] >> metis_tac[]) >>
  `MAP (\v. stack_get_depth v (p ++ core)) (h::t) =
   MAP (\v. stack_get_depth v core) (h::t) /\
   MAP (\v. stack_get_depth v (q ++ core)) (h::t) =
   MAP (\v. stack_get_depth v core) (h::t)` by
    (conj_tac >> irule MAP_CONG >> simp[]) >>
  gvs[] >> simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- suspend "contiguous"
      >> suspend "noncontiguous") >>
  suspend "missing"
QED

Resume popmany_plan_shared_core_replay[noncontiguous]:
  simp[] >>
  `ps = ps with <|ps_stack := p ++ core; ps_alloc := qs.ps_alloc|>` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  `qs = qs with <|ps_stack := q ++ core; ps_alloc := qs.ps_alloc|>` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  qspec_then `ps` mp_tac popmany_individual_shared_core_replay >>
  disch_then (qspecl_then [`qs`, `p`, `q`, `core`, `qs.ps_alloc`, `h::t`] mp_tac) >>
  simp[] >>
  qpat_x_assum `ps.ps_stack = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `qs.ps_stack = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `ps.ps_alloc = _` (SUBST1_TAC o SYM) >> simp[]
QED

Resume popmany_plan_shared_core_replay[missing]:
  simp[] >>
  `ps = ps with <|ps_stack := p ++ core; ps_alloc := qs.ps_alloc|>` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  `qs = qs with <|ps_stack := q ++ core; ps_alloc := qs.ps_alloc|>` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  qspec_then `ps` mp_tac popmany_individual_shared_core_replay >>
  disch_then (qspecl_then [`qs`, `p`, `q`, `core`, `qs.ps_alloc`, `h::t`] mp_tac) >>
  simp[] >>
  qpat_x_assum `ps.ps_stack = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `qs.ps_stack = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `ps.ps_alloc = _` (SUBST1_TAC o SYM) >> simp[]
QED

Resume popmany_plan_shared_core_replay[contiguous]:
  `LENGTH (h::t) < LENGTH core` by
    (irule contiguous_top_depth_floor >> simp[]) >>
  `?ops al.
    do_swap (LENGTH (h::t)) ps =
      (ops, ps with <|ps_stack := p ++ stack_swap (LENGTH (h::t)) core; ps_alloc := al|>) /\
    do_swap (LENGTH (h::t)) qs =
      (ops, qs with <|ps_stack := q ++ stack_swap (LENGTH (h::t)) core; ps_alloc := al|>)` by
    (drule do_swap_prefix_replay >>
     disch_then (qspecl_then [`ps`, `qs`, `p`, `q`] mp_tac) >> simp[]) >>
  `!r. stack_pop (LENGTH (h::t)) (r ++ stack_swap (LENGTH (h::t)) core) =
    r ++ stack_pop (LENGTH (h::t)) (stack_swap (LENGTH (h::t)) core)` by
    (gen_tac >> fs[stack_pop_def, TAKE_APPEND, stack_swap_def, LENGTH_TAKE] >> decide_tac) >>
  qexistsl_tac [`ops ++ [SOPop (LENGTH (h::t))]`,
    `stack_pop (LENGTH (h::t)) (stack_swap (LENGTH (h::t)) core)`, `al`] >> fs[]
QED

Finalise popmany_plan_shared_core_replay

Theorem cleanup_retained_prefix_replay:
  !m n core ps qs inputs physical retained removed.
    lineage_core m core ps /\ lineage_core n core qs /\
    ALL_DISTINCT core /\ EVERY is_var_operand core /\
    ps.ps_alloc = qs.ps_alloc /\
    set physical = set core DIFF set (MAP Var inputs) /\
    retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical /\
    removed = FILTER (\op. ~MEM op retained) physical ==>
    ?pre live ops al.
      set retained = set pre /\
      popmany_plan removed ps =
        (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ pre ++ live;
                       ps_alloc := al|>) /\
      popmany_plan removed qs =
        (ops, qs with <|ps_stack := REPLICATE n dead_stack_marker ++ pre ++ live;
                       ps_alloc := al|>) /\
      mark_dead_stack retained (REPLICATE m dead_stack_marker ++ pre ++ live) =
        REPLICATE (m + LENGTH pre) dead_stack_marker ++ live /\
      mark_dead_stack retained (REPLICATE n dead_stack_marker ++ pre ++ live) =
        REPLICATE (n + LENGTH pre) dead_stack_marker ++ live /\
      ALL_DISTINCT live /\ EVERY is_var_operand live /\
      set live = set core INTER set (MAP Var inputs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all below_all_live_core_prefix >>
  disch_then (qspecl_then [`m`, `inputs`] strip_assume_tac) >>
  `set retained = set pre` by
    (simp[EXTENSION, MEM_FILTER] >> gvs[lineage_core_def] >> ASM_SET_TAC[]) >>
  `set removed = set physical DIFF set retained` by
    (simp[EXTENSION, MEM_FILTER] >> metis_tac[]) >>
  `!k. DISJOINT (set (REPLICATE k dead_stack_marker ++ pre)) (set removed)` by
    (`~MEM dead_stack_marker physical` by
       (fs[EVERY_MEM] >>
        `~is_var_operand dead_stack_marker` by
          simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
        ASM_SET_TAC[]) >>
     gvs[] >> simp[DISJOINT_DEF, EXTENSION, MEM_REPLICATE] >> metis_tac[]) >>
  `ALL_DISTINCT tail` by gvs[ALL_DISTINCT_APPEND] >>
  `?ops live al.
     popmany_plan removed ps =
       (ops, ps with <|ps_stack := (REPLICATE m dead_stack_marker ++ pre) ++ live;
                      ps_alloc := al|>) /\
     popmany_plan removed qs =
       (ops, qs with <|ps_stack := (REPLICATE n dead_stack_marker ++ pre) ++ live;
                      ps_alloc := al|>) /\
     ALL_DISTINCT live /\ set live = set tail DIFF set removed` by
    (irule popmany_plan_prefix_frame >> gvs[lineage_core_def]) >>
  `DISJOINT (set pre) (set live)` by
    (gvs[ALL_DISTINCT_APPEND] >> ASM_SET_TAC[]) >>
  `set live = set core INTER set (MAP Var inputs)` by
    (gvs[ALL_DISTINCT_APPEND] >> ASM_SET_TAC[]) >>
  qexistsl_tac [`pre`, `live`, `ops`, `al`] >>
  simp[APPEND_ASSOC, mark_dead_stack_prefix] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `MEM e core` by ASM_SET_TAC[] >> metis_tac[]
QED

Theorem cleanup_retained_core:
  !m core ps inputs physical retained removed.
    lineage_core m core ps /\ ALL_DISTINCT core /\ EVERY is_var_operand core /\
    set physical = set core DIFF set (MAP Var inputs) /\
    retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical /\
    removed = FILTER (\op. ~MEM op retained) physical ==>
    ?n live.
      mark_dead_stack retained (SND (popmany_plan removed ps)).ps_stack =
        REPLICATE n dead_stack_marker ++ live /\
      ALL_DISTINCT live /\ EVERY is_var_operand live /\
      set live = set core INTER set (MAP Var inputs)
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_alloc = ps.ps_alloc` by simp[] >>
  drule_all cleanup_retained_prefix_replay >> strip_tac >>
  qexistsl_tac [`m + LENGTH pre`, `live`] >> gvs[]
QED

Theorem cleanup_payload_inventory:
  !S ps inputs layout to_pop physical retained removed ok promised result.
    lineage_inventory S ps /\ set (MAP Var inputs) SUBSET S /\
    S SUBSET set (MAP Var inputs) UNION set (MAP Var layout) UNION FDOM ps.ps_spilled /\
    to_pop = FILTER (\v. ~MEM v inputs) layout /\
    physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop) /\
    retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical /\
    removed = FILTER (\op. ~MEM op retained) physical /\
    result =
      (if NULL inputs /\ ok then
         ps with <| ps_stack := MAP (K dead_stack_marker) ps.ps_stack;
                    ps_cleanup_promised := promised |>
       else if ok then
         (SND (popmany_plan removed ps)) with
           <| ps_stack := mark_dead_stack retained (SND (popmany_plan removed ps)).ps_stack;
              ps_cleanup_promised := promised |>
       else SND (popmany_plan (MAP Var to_pop) ps)) ==>
    lineage_inventory (set (MAP Var inputs) UNION FDOM ps.ps_spilled) result
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ok`
  >- (Cases_on `NULL inputs`
      >- suspend "empty"
      >> suspend "marked") >>
  suspend "popped"
QED

Resume cleanup_payload_inventory[empty]:
  gvs[NULL_EQ] >>
  fs[lineage_inventory_def] >>
  simp[lineage_inventory_def, lineage_core_def] >>
  qexistsl_tac [`LENGTH ps.ps_stack`, `[]`] >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE, combinTheory.K_DEF]
QED

Resume cleanup_payload_inventory[marked]:
  qpat_x_assum `lineage_inventory _ ps` mp_tac >>
  qmatch_goalsub_rename_tac `lineage_inventory inventory_set ps` >> disch_tac >>
  `?m core. lineage_core m core ps /\ ALL_DISTINCT core /\
     EVERY is_var_operand core /\ DISJOINT (set core) (FDOM ps.ps_spilled) /\
     set core UNION FDOM ps.ps_spilled = inventory_set` by
    (fs[lineage_inventory_def] >> metis_tac[]) >>
  `set physical = set core DIFF set (MAP Var inputs)` by
    (qpat_x_assum `to_pop = _` SUBST_ALL_TAC >>
     drule_all cleanup_physical_core >> simp[]) >>
  drule_all cleanup_retained_core >> strip_tac >>
  gvs[] >> simp[lineage_inventory_def, lineage_core_def, popmany_plan_spilled_unchanged] >>
  qexistsl_tac [`n`, `live`] >> simp[] >>
  conj_tac >- ASM_SET_TAC[] >>
  conj_tac >- ASM_SET_TAC[] >>
  fs[lineage_inventory_def] >> metis_tac[]
QED

Resume cleanup_payload_inventory[popped]:
  qpat_x_assum `lineage_inventory _ ps` mp_tac >>
  qmatch_goalsub_rename_tac `lineage_inventory inventory_set ps` >> disch_tac >>
  gvs[] >>
  `~MEM dead_stack_marker (MAP Var (FILTER (\v. ~MEM v inputs) layout))` by
    simp[MEM_MAP, dead_stack_marker_def] >>
  drule_all popmany_plan_lineage_inventory >>
  `inventory_set DIFF (set (MAP Var (FILTER (\v. ~MEM v inputs) layout)) INTER set ps.ps_stack) =
     set (MAP Var inputs) UNION FDOM ps.ps_spilled` by
    (`set (MAP Var (FILTER (\v. ~MEM v inputs) layout)) =
        set (MAP Var layout) DIFF set (MAP Var inputs)` by
       (simp[EXTENSION, MEM_MAP, MEM_FILTER] >> Cases >> simp[] >> metis_tac[]) >>
     qpat_x_assum `lineage_inventory _ ps` mp_tac >>
     rewrite_tac[lineage_inventory_def, lineage_core_def] >> strip_tac >>
     `~MEM dead_stack_marker (MAP Var inputs)` by simp[MEM_MAP, dead_stack_marker_def] >>
     `~MEM dead_stack_marker (MAP Var layout)` by simp[MEM_MAP, dead_stack_marker_def] >>
     `DISJOINT (set (REPLICATE m dead_stack_marker)) (set (MAP Var layout))` by
       (simp[DISJOINT_DEF, EXTENSION, MEM_REPLICATE] >> metis_tac[]) >>
     gvs[] >> ASM_SET_TAC[]) >> simp[]
QED

Finalise cleanup_payload_inventory

Theorem clean_stack_plan_active_inventory:
  !S ps liveness cfg fn bb pred_lbl pred_bb inputs layout.
    lineage_inventory S ps /\
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    inputs = input_vars_from pred_lbl bb.bb_instructions
      (live_vars_at liveness bb.bb_label 0) /\
    layout = live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions) /\
    set (MAP Var inputs) SUBSET S /\
    S SUBSET set (MAP Var inputs) UNION set (MAP Var layout) UNION FDOM ps.ps_spilled ==>
    lineage_inventory (set (MAP Var inputs) UNION FDOM ps.ps_spilled)
      (SND (clean_stack_plan liveness cfg fn bb ps))
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once clean_stack_plan_def] >>
  qpat_x_assum `inputs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `layout = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qabbrev_tac `to_pop = FILTER (\v. ~MEM v inputs) layout` >>
  qmatch_goalsub_abbrev_tac `FILTER (\op. below_all_live op inputs ps.ps_stack) physical` >>
  qmatch_goalsub_abbrev_tac `FILTER (\op. ~MEM op retained) physical` >>
  qmatch_goalsub_abbrev_tac `popmany_plan removed ps` >>
  qmatch_goalsub_abbrev_tac `if NULL inputs /\ ok then _ else _` >>
  irule cleanup_payload_inventory >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`ok`, `physical`,
    `ps.ps_cleanup_promised \/ ~NULL retained`, `removed`, `retained`, `to_pop`] >>
  simp[Abbr `to_pop`, Abbr `physical`, Abbr `retained`, Abbr `removed`] >>
  Cases_on `ok` >> simp[] >>
  Cases_on `NULL inputs` >> simp[] >>
  pairarg_tac >> simp[]
QED

(* Expose the active cleanup payload without unfolding it in replay consumers. *)
Theorem clean_stack_plan_active_payload:
  !liveness cfg fn bb ps pred_lbl pred_bb inputs layout
   to_pop physical retained removed ok promised.
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    inputs = input_vars_from pred_lbl bb.bb_instructions
      (live_vars_at liveness bb.bb_label 0) /\
    layout = live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions) /\
    to_pop = FILTER (\v. ~MEM v inputs) layout /\
    physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop) /\
    retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical /\
    removed = FILTER (\op. ~MEM op retained) physical /\
    ok = (ps.ps_cleanup_promised \/
      cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb
        (LENGTH ps.ps_stack - LENGTH removed)) /\
    promised = (ps.ps_cleanup_promised \/ (ok /\ ~NULL retained)) ==>
    clean_stack_plan liveness cfg fn bb ps =
    if NULL inputs /\ ok then
      ([], ps with <|ps_stack := MAP (K dead_stack_marker) ps.ps_stack;
                     ps_cleanup_promised := promised|>)
    else if ok then
      (FST (popmany_plan removed ps),
       (SND (popmany_plan removed ps)) with
         <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed ps)).ps_stack;
           ps_cleanup_promised := promised|>)
    else popmany_plan (MAP Var to_pop) ps
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once clean_stack_plan_def] >>
  qpat_x_assum `inputs = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `layout = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `to_pop = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `physical = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `retained = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `removed = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `ok = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `promised = _` (fn th => rewrite_tac[GSYM th]) >>
  Cases_on `NULL inputs` >> Cases_on `ok` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem clean_stack_plan_active_prefix_replay:
  !liveness cfg fn bb ps qs m n core pred_lbl pred_bb inputs layout.
    lineage_core m core ps /\ lineage_core n core qs /\
    ALL_DISTINCT core /\ EVERY is_var_operand core /\ ps.ps_alloc = qs.ps_alloc /\
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    inputs = input_vars_from pred_lbl bb.bb_instructions
      (live_vars_at liveness bb.bb_label 0) /\
    layout = live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions) /\
    set core SUBSET set (MAP Var inputs) UNION set (MAP Var layout) ==>
    ?choice ops core' m' n' al pref pcand.
      clean_stack_plan liveness cfg fn bb ps =
        (ops, ps with <|ps_stack := REPLICATE m' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_promised := pref|>) /\
      clean_stack_plan liveness cfg fn bb
        (qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := choice|>) =
        (ops, qs with <|ps_stack := REPLICATE n' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_height := NONE;
                       ps_cleanup_promised := pcand|>) /\
      ALL_DISTINCT core' /\ EVERY is_var_operand core'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `to_pop = FILTER (\v. ~MEM v inputs) layout` >>
  qabbrev_tac `physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop)` >>
  qabbrev_tac `retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical` >>
  qabbrev_tac `removed = FILTER (\op. ~MEM op retained) physical` >>
  qabbrev_tac `ok = (ps.ps_cleanup_promised \/
    cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb
      (LENGTH ps.ps_stack - LENGTH removed))` >>
  `~MEM dead_stack_marker core` by
    (fs[EVERY_MEM] >> strip_tac >>
     first_x_assum drule >>
     simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def]) >>
  `bottom_dead_equiv ps.ps_stack qs.ps_stack` by
    (simp[bottom_dead_equiv_def] >> qexistsl_tac [`m`, `n`, `core`] >>
     simp[] >> gvs[lineage_core_def]) >>
  `~MEM dead_stack_marker (MAP Var to_pop)` by simp[MEM_MAP, dead_stack_marker_def] >>
  `physical = FILTER (\op. IS_SOME (stack_get_depth op qs.ps_stack)) (MAP Var to_pop)` by
    (simp[Abbr `physical`] >> irule bottom_dead_equiv_physical >> simp[]) >>
  `retained = FILTER (\op. below_all_live op inputs qs.ps_stack) physical` by
    (drule_all bottom_dead_equiv_cleanup_partitions >>
     disch_then (qspec_then `inputs` mp_tac) >>
     simp[Abbr `retained`, Abbr `physical`]) >>
  `set physical = set (MAP Var to_pop) INTER set core` by
    (simp[Abbr `physical`, EXTENSION, MEM_FILTER, stack_get_depth_is_some] >>
     qpat_x_assum `lineage_core m core ps` mp_tac >>
     qpat_x_assum `~MEM dead_stack_marker (MAP Var to_pop)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[lineage_core_def] >> rpt strip_tac >>
     simp[MEM_REPLICATE] >> metis_tac[]) >>
  `set (MAP Var to_pop) = set (MAP Var layout) DIFF set (MAP Var inputs)` by
    (simp[Abbr `to_pop`, EXTENSION, MEM_MAP, MEM_FILTER] >>
     Cases >> simp[] >> metis_tac[]) >>
  `set physical = set core DIFF set (MAP Var inputs)` by ASM_SET_TAC[] >>
  qabbrev_tac `pref0 = (ps.ps_cleanup_promised \/ (ok /\ ~NULL retained))` >>
  `clean_stack_plan liveness cfg fn bb ps =
    if NULL inputs /\ ok then
      ([], ps with <|ps_stack := MAP (K dead_stack_marker) ps.ps_stack;
                     ps_cleanup_promised := pref0|>)
    else if ok then
      (FST (popmany_plan removed ps),
       (SND (popmany_plan removed ps)) with
         <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed ps)).ps_stack;
           ps_cleanup_promised := pref0|>)
    else popmany_plan (MAP Var to_pop) ps` by
    (irule clean_stack_plan_active_payload >>
     rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `to_pop`, Abbr `physical`, Abbr `retained`, Abbr `removed`,
          Abbr `ok`, Abbr `pref0`]) >>
  qabbrev_tac `cs = qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := ok|>` >>
  `clean_stack_plan liveness cfg fn bb cs =
    if NULL inputs /\ ok then
      ([], cs with <|ps_stack := MAP (K dead_stack_marker) cs.ps_stack;
                     ps_cleanup_promised := ok|>)
    else if ok then
      (FST (popmany_plan removed cs),
       (SND (popmany_plan removed cs)) with
         <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed cs)).ps_stack;
           ps_cleanup_promised := ok|>)
    else popmany_plan (MAP Var to_pop) cs` by
    (irule clean_stack_plan_active_payload >>
     rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `cs`, Abbr `to_pop`, Abbr `removed`] >>
     Cases_on `ok` >> simp[]) >>
  qexists_tac `ok` >>
  Cases_on `ok`
  >- (Cases_on `NULL inputs`
      >- suspend "empty"
      >> suspend "marked") >>
  suspend "popped"
QED

Resume clean_stack_plan_active_prefix_replay[empty]:
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`[]`, `[]`, `LENGTH ps.ps_stack`, `LENGTH qs.ps_stack`,
    `ps.ps_alloc`, `pref0`, `T`] >>
  simp[] >>
  simp[stackPlanTypesTheory.plan_state_component_equality,
       LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE, combinTheory.K_DEF]
QED

Resume clean_stack_plan_active_prefix_replay[marked]:
  `lineage_core n core cs` by (simp[Abbr `cs`, lineage_core_def] >> fs[lineage_core_def]) >>
  `ps.ps_alloc = cs.ps_alloc` by simp[Abbr `cs`] >>
  qpat_x_assum `lineage_core n core qs` kall_tac >>
  qpat_x_assum `ps.ps_alloc = qs.ps_alloc` kall_tac >>
  `retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical` by
    simp[Abbr `retained`] >>
  `removed = FILTER (\op. ~MEM op retained) physical` by simp[Abbr `removed`] >>
  drule_all cleanup_retained_prefix_replay >> strip_tac >>
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`ops`, `live`, `m + LENGTH pre`, `n + LENGTH pre`,
    `al`, `pref0`, `T`] >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `mark_dead_stack _ _ = _` mp_tac) >>
  qpat_x_assum `ALL_DISTINCT live` mp_tac >>
  qpat_x_assum `EVERY is_var_operand live` mp_tac >>
  qpat_x_assum `~NULL inputs` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[]
QED

Resume clean_stack_plan_active_prefix_replay[popped]:
  `?ops live al.
    popmany_plan (MAP Var to_pop) ps =
      (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ live; ps_alloc := al|>) /\
    popmany_plan (MAP Var to_pop) cs =
      (ops, cs with <|ps_stack := REPLICATE n dead_stack_marker ++ live; ps_alloc := al|>) /\
    ALL_DISTINCT live /\ set live = set core DIFF set (MAP Var to_pop)` by
    (irule popmany_plan_prefix_frame >>
     simp[Abbr `cs`, DISJOINT_ALT, MEM_REPLICATE, MEM_MAP, dead_stack_marker_def] >>
     fs[lineage_core_def, dead_stack_marker_def]) >>
  `EVERY is_var_operand live` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `MEM e core` by ASM_SET_TAC[] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`ops`, `live`, `m`, `n`, `al`, `ps.ps_cleanup_promised`, `F`] >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  qpat_x_assum `ALL_DISTINCT live` mp_tac >>
  qpat_x_assum `EVERY is_var_operand live` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[]
QED

Finalise clean_stack_plan_active_prefix_replay


Theorem clean_stack_plan_prefix_replay:
  !liveness cfg fn bb ps qs m n core.
    lineage_core m core ps /\ lineage_core n core qs /\
    ALL_DISTINCT core /\ EVERY is_var_operand core /\ ps.ps_alloc = qs.ps_alloc /\
    (!pred_lbl pred_bb.
      cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
      1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
      lookup_block pred_lbl fn.fn_blocks = SOME pred_bb ==>
      set core SUBSET
        set (MAP Var (input_vars_from pred_lbl bb.bb_instructions
          (live_vars_at liveness bb.bb_label 0))) UNION
        set (MAP Var (live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions)))) ==>
    ?choice ops core' m' n' al pref pcand.
      clean_stack_plan liveness cfg fn bb ps =
        (ops, ps with <|ps_stack := REPLICATE m' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_promised := pref|>) /\
      clean_stack_plan liveness cfg fn bb
        (qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := choice|>) =
        (ops, qs with <|ps_stack := REPLICATE n' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_height := NONE;
                       ps_cleanup_promised := pcand|>) /\
      ALL_DISTINCT core' /\ EVERY is_var_operand core'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?pred_lbl pred_bb.
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb`
  >- (pop_assum strip_assume_tac >>
      irule clean_stack_plan_active_prefix_replay >>
      rpt (goal_assum (drule_at Any)) >>
      simp[] >> metis_tac[]) >>
  `!s. clean_stack_plan liveness cfg fn bb s = ([], s)` by
    (gen_tac >>
     Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[clean_stack_plan_def] >>
     Cases_on `t` >> simp[clean_stack_plan_def] >>
     Cases_on `LENGTH (cfg_succs_of cfg h) <= 1` >> simp[] >>
     Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
     metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  qexistsl_tac [`F`, `[]`, `core`, `m`, `n`, `ps.ps_alloc`,
                `ps.ps_cleanup_promised`, `F`] >>
  simp[] >>
  gvs[lineage_core_def, stackPlanTypesTheory.plan_state_component_equality]
QED

(* Physical cleanup replay does not require a normalized live inventory.
   In particular the shared output core below may contain internal markers. *)
Theorem clean_stack_plan_arbitrary_core_replay:
  !liveness cfg fn bb ps qs m n core.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    qs.ps_stack = REPLICATE n dead_stack_marker ++ core /\
    ps.ps_alloc = qs.ps_alloc ==>
    ?choice ops core' m' n' al pref pcand.
      clean_stack_plan liveness cfg fn bb ps =
        (ops, ps with <|ps_stack := REPLICATE m' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_promised := pref|>) /\
      clean_stack_plan liveness cfg fn bb
        (qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := choice|>) =
        (ops, qs with <|ps_stack := REPLICATE n' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_height := NONE;
                       ps_cleanup_promised := pcand|>)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?pred_lbl pred_bb.
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb`
  >- (pop_assum strip_assume_tac >> suspend "active") >>
  `!s. clean_stack_plan liveness cfg fn bb s = ([], s)` by
    (gen_tac >>
     Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[clean_stack_plan_def] >>
     Cases_on `t` >> simp[clean_stack_plan_def] >>
     Cases_on `LENGTH (cfg_succs_of cfg h) <= 1` >> simp[] >>
     Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
     metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  qexistsl_tac [`F`, `[]`, `core`, `m`, `n`, `ps.ps_alloc`,
                `ps.ps_cleanup_promised`, `F`] >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Resume clean_stack_plan_arbitrary_core_replay[active]:
  qabbrev_tac `inputs = input_vars_from pred_lbl bb.bb_instructions
    (live_vars_at liveness bb.bb_label 0)` >>
  qabbrev_tac `layout = live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions)` >>
  qabbrev_tac `to_pop = FILTER (\v. ~MEM v inputs) layout` >>
  qabbrev_tac `physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop)` >>
  qabbrev_tac `retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical` >>
  qabbrev_tac `removed = FILTER (\op. ~MEM op retained) physical` >>
  qabbrev_tac `ok = (ps.ps_cleanup_promised \/
    cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb
      (LENGTH ps.ps_stack - LENGTH removed))` >>
  `!op. op <> dead_stack_marker ==>
    stack_get_depth op ps.ps_stack = stack_get_depth op qs.ps_stack` by
    simp[stack_get_depth_bottom_dead] >>
  `physical = FILTER (\op. IS_SOME (stack_get_depth op qs.ps_stack)) (MAP Var to_pop)` by
    (simp[Abbr `physical`, FILTER_MAP, combinTheory.o_DEF, stack_get_depth_bottom_dead, dead_stack_marker_def]) >>
  `~MEM dead_stack_marker physical` by
    simp[Abbr `physical`, MEM_FILTER, MEM_MAP, dead_stack_marker_def] >>
  `retained = FILTER (\op. below_all_live op inputs qs.ps_stack) physical` by
    (simp[Abbr `retained`, Abbr `physical`, FILTER_FILTER, FILTER_MAP,
          below_all_live_def, combinTheory.o_DEF,
          stack_get_depth_bottom_dead, dead_stack_marker_def]) >>
  qabbrev_tac `pref0 = (ps.ps_cleanup_promised \/ (ok /\ ~NULL retained))` >>
  `clean_stack_plan liveness cfg fn bb ps =
    if NULL inputs /\ ok then
      ([], ps with <|ps_stack := MAP (K dead_stack_marker) ps.ps_stack;
                     ps_cleanup_promised := pref0|>)
    else if ok then
      (FST (popmany_plan removed ps),
       (SND (popmany_plan removed ps)) with
         <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed ps)).ps_stack;
           ps_cleanup_promised := pref0|>)
    else popmany_plan (MAP Var to_pop) ps` by
    (irule clean_stack_plan_active_payload >>
     rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `inputs`, Abbr `layout`, Abbr `to_pop`, Abbr `physical`,
          Abbr `retained`, Abbr `removed`, Abbr `ok`, Abbr `pref0`]) >>
  qabbrev_tac `cs = qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := ok|>` >>
  `clean_stack_plan liveness cfg fn bb cs =
    if NULL inputs /\ ok then
      ([], cs with <|ps_stack := MAP (K dead_stack_marker) cs.ps_stack;
                     ps_cleanup_promised := ok|>)
    else if ok then
      (FST (popmany_plan removed cs),
       (SND (popmany_plan removed cs)) with
         <|ps_stack := mark_dead_stack retained (SND (popmany_plan removed cs)).ps_stack;
           ps_cleanup_promised := ok|>)
    else popmany_plan (MAP Var to_pop) cs` by
    (irule clean_stack_plan_active_payload >>
     rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `cs`, Abbr `inputs`, Abbr `layout`, Abbr `to_pop`, Abbr `removed`] >>
     Cases_on `ok` >> simp[]) >>
  qexists_tac `ok` >>
  Cases_on `ok`
  >- (Cases_on `NULL inputs`
      >- suspend "empty"
      >> suspend "marked") >>
  suspend "popped"
QED

Resume clean_stack_plan_arbitrary_core_replay[empty]:
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`[]`, `[]`, `LENGTH ps.ps_stack`, `LENGTH qs.ps_stack`,
    `ps.ps_alloc`, `pref0`, `T`] >>
  simp[] >>
  simp[stackPlanTypesTheory.plan_state_component_equality,
       LIST_EQ_REWRITE, EL_APPEND_EQN, EL_MAP, EL_REPLICATE, combinTheory.K_DEF]
QED

Resume clean_stack_plan_arbitrary_core_replay[marked]:
  `~MEM dead_stack_marker removed` by
    (simp[Abbr `removed`, MEM_FILTER] >> metis_tac[]) >>
  `?ops live al.
    popmany_plan removed ps =
      (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ live; ps_alloc := al|>) /\
    popmany_plan removed cs =
      (ops, cs with <|ps_stack := REPLICATE n dead_stack_marker ++ live; ps_alloc := al|>)` by
    (irule popmany_plan_shared_core_replay >>
     simp[Abbr `cs`, DISJOINT_ALT, MEM_REPLICATE] >> metis_tac[]) >>
  `!k. mark_dead_stack retained (REPLICATE k dead_stack_marker ++ live) =
    REPLICATE k dead_stack_marker ++ mark_dead_stack retained live` by
    (Induct >> simp[mark_dead_stack_def]) >>
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`ops`, `mark_dead_stack retained live`, `m`, `n`, `al`, `pref0`, `T`] >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  qpat_x_assum `~NULL inputs` mp_tac >>
  qpat_x_assum `!k. mark_dead_stack _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[]
QED

Resume clean_stack_plan_arbitrary_core_replay[popped]:
  `?ops live al.
    popmany_plan (MAP Var to_pop) ps =
      (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ live; ps_alloc := al|>) /\
    popmany_plan (MAP Var to_pop) cs =
      (ops, cs with <|ps_stack := REPLICATE n dead_stack_marker ++ live; ps_alloc := al|>)` by
    (irule popmany_plan_shared_core_replay >>
     simp[Abbr `cs`, DISJOINT_ALT, MEM_REPLICATE, MEM_MAP, dead_stack_marker_def]) >>
  qpat_x_assum `Abbrev (cs = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`ops`, `live`, `m`, `n`, `al`, `ps.ps_cleanup_promised`, `F`] >>
  rpt (qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `popmany_plan _ _ = _` mp_tac) >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[]
QED

Finalise clean_stack_plan_arbitrary_core_replay

(* Compatibility corollary; the physical argument above needs no counts. *)
Theorem clean_stack_plan_shared_core_replay:
  !liveness cfg fn bb ps qs m n core.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    qs.ps_stack = REPLICATE n dead_stack_marker ++ core /\
    ALL_DISTINCT core /\ ps.ps_alloc = qs.ps_alloc ==>
    ?choice ops core' m' n' al pref pcand.
      clean_stack_plan liveness cfg fn bb ps =
        (ops, ps with <|ps_stack := REPLICATE m' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_promised := pref|>) /\
      clean_stack_plan liveness cfg fn bb
        (qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := choice|>) =
        (ops, qs with <|ps_stack := REPLICATE n' dead_stack_marker ++ core';
                       ps_alloc := al; ps_cleanup_height := NONE;
                       ps_cleanup_promised := pcand|>)
Proof
  rpt strip_tac >> irule clean_stack_plan_arbitrary_core_replay >>
  rpt (goal_assum (drule_at Any))
QED


Theorem stack_dup_bottom_extension:
  !d prefix core. d < LENGTH core ==>
    stack_dup d (prefix ++ core) = prefix ++ stack_dup d core
Proof
  rpt strip_tac >>
  `LENGTH (prefix ++ core) - 1 - d = LENGTH prefix + (LENGTH core - 1 - d)` by
    (simp[] >> decide_tac) >>
  simp[stack_dup_def, stack_peek_def, EL_APPEND2, SNOC_APPEND]
QED

Theorem do_dup_prefix_replay:
  !d prefix prefix' core ps qs.
    ps.ps_stack = prefix ++ core /\ qs.ps_stack = prefix' ++ core /\
    ps.ps_alloc = qs.ps_alloc /\ d < LENGTH core ==>
    ?ops al.
      do_dup d ps =
        (ops, ps with <|ps_stack := prefix ++ stack_dup d core; ps_alloc := al|>) /\
      do_dup d qs =
        (ops, qs with <|ps_stack := prefix' ++ stack_dup d core; ps_alloc := al|>)
Proof
  rpt strip_tac >> Cases_on `d <= 15`
  >- (qexistsl_tac [`[SODup (d+1)]`, `ps.ps_alloc`] >>
      simp[do_dup_def, stack_dup_bottom_extension,
           stackPlanTypesTheory.plan_state_component_equality]) >>
  `d - 15 <= LENGTH core` by decide_tac >>
  `top_n (d - 15) ps.ps_stack = top_n (d - 15) core /\
   top_n (d - 15) qs.ps_stack = top_n (d - 15) core` by
    simp[top_n_def, TAKE_APPEND] >>
  simp[do_dup_def, stack_dup_bottom_extension] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

(* A native spill removes exactly the selected top cell, not earlier copies. *)
Theorem do_spill_tos_append:
  alloc_spill_slot ps.ps_alloc = (off,alloc') ==>
  do_spill_tos (ps with ps_stack := prefix ++ [op]) =
    ([SOSpill off], ps with <| ps_stack := prefix;
      ps_spilled := ps.ps_spilled |+ (op,off); ps_alloc := alloc' |>)
Proof
  strip_tac >>
  simp[do_spill_tos_def, stack_peek_def, stack_pop_def,
       EL_APPEND2, TAKE_APPEND]
QED

Theorem do_restore_exact:
  FLOOKUP ps.ps_spilled op = SOME off ==>
  do_restore op ps =
    ([SORestore off], ps with <|
      ps_stack := ps.ps_stack ++ [op];
      ps_spilled := ps.ps_spilled \\ op;
      ps_alloc := free_spill_slot off ps.ps_alloc |> )
Proof
  simp[do_restore_def, stack_push_def, SNOC_APPEND]
QED

Theorem do_spill_at_suffix_stack:
  d < LENGTH suffix /\ d <= 16 ==>
  (SND (do_spill_at d (ps with ps_stack := prefix ++ suffix))).ps_stack =
    prefix ++ stack_pop 1 (stack_swap d suffix)
Proof
  strip_tac >> Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `d = 0`
  >- gvs[do_spill_at_def, do_spill_tos_def,
         stack_pop_def, stack_swap_def, LUPDATE_SAME,
         TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  simp[do_spill_at_def, do_spill_tos_def, stack_swap_bottom_extension,
       stack_pop_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

(* The pending-use set in the native cons equation is already exposed by
   stackPlanGen.emit_input_plan_cons. Repeated operands therefore force
   the first occurrence to be retained, even when absent from next. *)
Theorem emit_one_repeated_var_restored:
  FLOOKUP ps.ps_spilled (Var v) = SOME off ==>
  emit_one_input opc (v :: uses) (Var v) ps =
    ([SORestore off; SODup 1], ps with <|
      ps_stack := ps.ps_stack ++ [Var v; Var v];
      ps_spilled := ps.ps_spilled \\ (Var v);
      ps_alloc := free_spill_slot off ps.ps_alloc |> )
Proof
  strip_tac >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       do_restore_def, stack_push_def, SNOC_APPEND,
       stack_get_depth_def, REVERSE_APPEND, stack_find_def,
       do_dup_def, stack_dup_def, stack_peek_def, EL_APPEND2] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* Moved from LowerPrefix: one shared native input boundary. *)
Theorem emit_one_input_suffix_shallow:
  stack_get_depth (Var v) suffix = SOME d /\ d <= 15 /\
  MEM v next /\ FLOOKUP ps.ps_spilled (Var v) = NONE ==>
  emit_one_input opc next (Var v) (ps with ps_stack := prefix ++ suffix) =
    ([SODup (d+1)], ps with ps_stack := prefix ++ (suffix ++ [Var v]))
Proof
  strip_tac >>
  `stack_get_depth (Var v) (prefix ++ suffix) = SOME d` by
    metis_tac[stack_get_depth_suffix_hit] >>
  drule stack_get_depth_props >> strip_tac >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def, do_dup_def,
       stack_dup_def, listTheory.SNOC_APPEND]
QED

Theorem emit_input_repeated_var_shallow:
  stack_get_depth (Var v) suffix = SOME d /\ d <= 15 /\
  ~MEM v next /\ FLOOKUP ps.ps_spilled (Var v) = NONE ==>
  emit_input_plan opc [Var v; Var v] next
    (ps with ps_stack := prefix ++ suffix) =
    ([SODup (d+1)], ps with ps_stack := prefix ++ (suffix ++ [Var v]))
Proof
  strip_tac >>
  `emit_one_input opc (v :: next) (Var v)
    (ps with ps_stack := prefix ++ suffix) =
    ([SODup (d+1)], ps with ps_stack := prefix ++ (suffix ++ [Var v]))` by
    (irule emit_one_input_suffix_shallow >> simp[]) >>
  simp[emit_input_plan_def, dfgDefsTheory.operand_vars_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       dfgDefsTheory.operand_var_def] >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def]
QED

Theorem emit_input_repeated_var_restored:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\ ~MEM v next ==>
  emit_input_plan opc [Var v; Var v] next ps =
    ([SORestore off; SODup 1], ps with <|
      ps_stack := ps.ps_stack ++ [Var v; Var v];
      ps_spilled := ps.ps_spilled \\ (Var v);
      ps_alloc := free_spill_slot off ps.ps_alloc |> )
Proof
  strip_tac >> drule emit_one_repeated_var_restored >>
  disch_then (qspecl_then [`next`, `opc`] assume_tac) >>
  simp[emit_input_plan_def, dfgDefsTheory.operand_vars_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       dfgDefsTheory.operand_var_def] >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       DOMSUB_FLOOKUP_THM]
QED

(* Operation checkpoint: do_spill_tos_append retains every earlier copy;
   do_spill_at_suffix_stack frames the prefix but does not erase its keys.
   Hence a no-stale premise must be produced before spilling, not inferred
   from membership in the new spill map. The exported, strengthened
   reorderSim.select_spill_candidate_not_pending protects exact pending
   keys (including duplicates), and its stack-count theorems account for
   exactly one removed occurrence. emit_input_plan_cons is the existing
   general pending-use transition, with operand_vars rest ++ next_liveness.
   The repeated-input equations above show the transient extra copy both
   from a shallow suffix hit and from persistent storage, even for a key
   dead in next_liveness. They do not assert uniqueness at an instruction
   boundary: later operand consumption must discharge this reserve.
   Thus multiplicity with a pending reserve is locally compatible with
   these equations; unconditional spilled-key absence is rejected.
   Native initialization, live-set transport, and preservation for all
   opcode branches remain unproved, as does suffix-local recursive fuel.
*)

Theorem init_cleanup_residual_budget:
  !ch growth spill_base lbl_ctr.
    residual_budget_wf spill_base []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
Proof
  rpt gen_tac >>
  simp[residual_budget_wf_def, planSpillBoundsTheory.plan_slots_bounded_def,
       planSpillBoundsTheory.alloc_slots_bounded_def,
       spill_alloc_layout_wf_def, init_cleanup_plan_state_def,
       stackPlanTypesTheory.init_plan_state_def,
       stackPlanTypesTheory.init_spill_alloc_def, LIST_ELEM_COUNT_THM]
QED

(* Native initialization audit (C3.3.native_initialization).
   init_cleanup_residual_budget proves only an upper budget on the EMPTY
   initial state, uniformly in all cleanup/label parameters.

   stackPlanGen generate_fn_plan_with_cleanup_analyzed (1291-1301) calls
   generate_fn_plan_aux at fn_entry_label with this state. The first
   generate_block_plan call (796-817) does NOT immediately emit an ordinary
   instruction: for HD fn.fn_blocks it first calls prepare_params_plan.
   PARAM/RETPC_PARAM are filtered out by non_param_insts (762-765); their
   native setup (530-558) pushes Var(HD inst_outputs) for get_params and
   uses live_vars_at lr entry.bb_label (LENGTH params) for dead pops and
   optimistic swap. Thus ordinary coverage must be proved AFTER setup;
   it cannot be inferred from the empty input stack alone.

   A sufficient analysis-side entry obligation, not yet proved here, is:
     codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
       live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label 0 = []
   A separate post-PARAM demand obligation is:
     EVERY (\v. MEM v (MAP (\inst. HD inst.inst_outputs)
                           (get_params (HD fn.fn_blocks).bb_instructions)))
       (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
          (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
   (under the same readiness assumptions). It must then be transported
   through setup's dead pops and optimistic swap, not merely asserted as
   a fact about the initial state. For first non-param inst::rest, the
   actual input demand is operand_vars(compute_operands inst), while
   generate_block_insts_plan (773-794) supplies next_live at n_params+1,
   or at block_len when rest=[]; those are distinct from entry live-in.
   Entry has no predecessors under block_entries_ready, so its clean_stack
   branch is disabled; successor entries use a different edge boundary.

   Available analysis interfaces searched:
   livenessProofs.liveness_sound_proof: wf_function /\ live membership
     yields a cfg_exec_path with used_before_defined (18-28).
   livenessProofs.live_vars_at_transfer: reachable block/lookup/index plus
     wf_function gives the backward instruction transfer equation (49-61).
   live_at_entry_in_boundary identifies boundary storage, NOT emptiness.
   These signatures alone do not rule out a use-before-definition witness
   from entry: that requires the SSA/dominance/path argument. Likewise the
   post-param membership obligation requires transport across the canonical
   param prefix. No existing empty-entry theorem was found in the liveness
   API. This checkpoint deliberately does not create new liveness machinery
   or claim that residual_budget_wf supplies lower coverage.
*)

Theorem do_spill_at_lineage_inventory:
  !inventory_set ps v d.
    lineage_inventory inventory_set ps /\
    stack_get_depth (Var v) ps.ps_stack = SOME d /\ d <= 16 ==>
    lineage_inventory inventory_set (SND (do_spill_at d ps))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lineage_inventory _ _` mp_tac >>
  simp[lineage_inventory_def, lineage_core_def] >> strip_tac >>
  `Var v <> dead_stack_marker` by simp[dead_stack_marker_def] >>
  `stack_get_depth (Var v) core = SOME d` by
    gvs[stack_get_depth_bottom_dead] >>
  drule stack_get_depth_props >> strip_tac >>
  drule_all stack_pop_swap_core >>
  disch_then (qspec_then `REPLICATE m dead_stack_marker` strip_assume_tac) >>
  `d < LENGTH ps.ps_stack` by simp[] >>
  Cases_on `do_spill_at d ps` >>
  drule_all do_spill_at_spilled_update >> strip_tac >>
  `r.ps_stack = REPLICATE m dead_stack_marker ++ core'` by
    (drule_all do_spill_at_suffix_stack >>
     disch_then (qspecl_then [`ps`, `[]`] mp_tac) >> gvs[]) >>
  simp[lineage_inventory_def, lineage_core_def] >>
  qexistsl_tac [`m`, `core'`] >>
  `stack_peek d ps.ps_stack = Var v` by metis_tac[stack_get_depth_props] >>
  `MEM (Var v) core` by
    (qpat_x_assum `stack_peek d core = Var v` (SUBST1_TAC o SYM) >>
     simp[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  gvs[EVERY_MEM, DISJOINT_ALT, EXTENSION] >>
  metis_tac[stackPlanTypesTheory.is_var_operand_def]
QED

Theorem emit_one_input_live_reserve[local]:
  !done rest opc nl keep h ps.
    set keep SUBSET set nl /\
    (!v. LIST_ELEM_COUNT (Var v) done +
       (if MEM (Var v) (h::rest) \/ MEM v keep then 1 else 0) <=
       LIST_ELEM_COUNT (Var v) ps.ps_stack +
       (if Var v IN FDOM ps.ps_spilled then 1 else 0)) ==>
    !v. LIST_ELEM_COUNT (Var v) (done ++ [h]) +
       (if MEM (Var v) rest \/ MEM v keep then 1 else 0) <=
       LIST_ELEM_COUNT (Var v)
         (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_stack +
       (if Var v IN FDOM
         (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_spilled
        then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_x_assum `!v. _ <= _` (qspec_then `v` assume_tac) >>
  qspecl_then [`opc`, `operand_vars rest ++ nl`, `h`, `ps`, `Var v`]
    assume_tac emit_one_input_inventory_mono_aux >>
  Cases_on `Var v = h`
  >- (gvs[elem_count_append, LIST_ELEM_COUNT_THM] >>
      Cases_on `MEM (Var v) rest \/ MEM v keep`
      >- (`MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
            (Cases_on `Var v IN FDOM ps.ps_spilled` >>
             gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
          `MEM v (operand_vars rest ++ nl)` by
            (gvs[SUBSET_DEF, MEM_APPEND, input_mem_operand_vars] >> metis_tac[]) >>
          `MEM (Var v) rest \/ MEM v nl` by
            (gvs[SUBSET_DEF, MEM_APPEND, input_mem_operand_vars] >> metis_tac[]) >>
          qspecl_then [`opc`, `operand_vars rest ++ nl`, `Var v`, `ps`]
            mp_tac emit_one_input_inventory_inc >>
          simp[stackPlanTypesTheory.is_var_operand_def, input_mem_operand_vars] >>
          rpt IF_CASES_TAC >> gvs[] >> decide_tac) >>
      gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[elem_count_append, LIST_ELEM_COUNT_THM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem emit_input_plan_live_reserve_acc[local]:
  !rest done opc nl keep ps iops ps1.
    set keep SUBSET set nl /\
    (!v. LIST_ELEM_COUNT (Var v) done +
       (if MEM (Var v) rest \/ MEM v keep then 1 else 0) <=
       LIST_ELEM_COUNT (Var v) ps.ps_stack +
       (if Var v IN FDOM ps.ps_spilled then 1 else 0)) /\
    emit_input_plan opc rest nl ps = (iops,ps1) ==>
    !v. LIST_ELEM_COUNT (Var v) (done ++ rest) +
       (if MEM v keep then 1 else 0) <=
       LIST_ELEM_COUNT (Var v) ps1.ps_stack +
       (if Var v IN FDOM ps1.ps_spilled then 1 else 0)
Proof
  Induct_on `rest` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all emit_one_input_live_reserve >>
  disch_then (qspec_then `opc` assume_tac) >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops, mid)` >>
  Cases_on `emit_input_plan opc rest nl mid` >>
  gvs[emit_input_plan_cons] >>
  first_x_assum drule >> disch_then drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then drule >> simp[]
QED

Theorem emit_input_plan_protected_live_reserve:
  !operands opc nl keep ps iops ps1.
    set keep SUBSET set nl /\
    (!v. MEM (Var v) operands \/ MEM v keep ==>
       MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    !v. LIST_ELEM_COUNT (Var v) operands + (if MEM v keep then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) ps1.ps_stack +
        (if Var v IN FDOM ps1.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. LIST_ELEM_COUNT (Var v) [] +
       (if MEM (Var v) operands \/ MEM v keep then 1 else 0) <=
       LIST_ELEM_COUNT (Var v) ps.ps_stack +
       (if Var v IN FDOM ps.ps_spilled then 1 else 0)` by
    (gen_tac >> simp[LIST_ELEM_COUNT_THM] >>
     IF_CASES_TAC >> simp[] >>
     `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
     Cases_on `Var v IN FDOM ps.ps_spilled` >>
     gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  drule_all emit_input_plan_live_reserve_acc >> simp[]
QED

Theorem emit_input_plan_live_reserve:
  !operands opc nl ps iops ps1.
    (!v. MEM (Var v) operands \/ MEM v nl ==>
       MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    !v. LIST_ELEM_COUNT (Var v) operands + (if MEM v nl then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) ps1.ps_stack +
        (if Var v IN FDOM ps1.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >> irule emit_input_plan_protected_live_reserve >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem emit_input_plan_lineage_live_reserve:
  !inventory_set operands opc nl ps iops ps1.
    lineage_inventory inventory_set ps /\
    (!v. MEM (Var v) operands \/ MEM v nl ==> Var v IN inventory_set) /\
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    !v. LIST_ELEM_COUNT (Var v) operands + (if MEM v nl then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) ps1.ps_stack +
        (if Var v IN FDOM ps1.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  irule emit_input_plan_live_reserve >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `lineage_inventory _ _` mp_tac >>
  simp[lineage_inventory_def, lineage_core_def] >>
  rpt strip_tac >> gvs[EXTENSION] >> metis_tac[MEM_APPEND]
QED

Theorem do_dup_bottom_frame:
  !d ps prefix ops qs.
    d < LENGTH ps.ps_stack /\ do_dup d ps = (ops,qs) ==>
    do_dup d (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `d < LENGTH core`) do_dup_prefix_replay >>
  disch_then (qspecl_then [`[]`, `prefix`, `ps`,
    `ps with ps_stack := prefix ++ ps.ps_stack`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem emit_one_input_available_preserved:
  !op opc nl ps ops qs v.
    emit_one_input opc nl op ps = (ops,qs) /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`opc`, `nl`, `op`, `ps`, `Var v`]
    mp_tac emit_one_input_inventory_mono_aux >>
  simp[] >> gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var v IN FDOM ps.ps_spilled` >>
  Cases_on `Var v IN FDOM qs.ps_spilled` >> gvs[] >> decide_tac
QED

Theorem emit_one_input_shielded_bottom_frame:
  !op prefix opc nl ps.
    (!v. op = Var v ==> ~MEM (Var v) prefix \/
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    emit_one_input opc nl op (ps with ps_stack := prefix ++ ps.ps_stack) =
      (FST (emit_one_input opc nl op ps),
       (SND (emit_one_input opc nl op ps)) with ps_stack :=
         prefix ++ (SND (emit_one_input opc nl op ps)).ps_stack)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       stack_push_def, SNOC_APPEND, APPEND_ASSOC] >>
  TRY (IF_CASES_TAC >> simp[] >> NO_TAC) >>
  rename1 `MEM v nl` >>
  `FLOOKUP ps.ps_spilled (Var v) = NONE ==>
    stack_get_depth (Var v) (prefix ++ ps.ps_stack) =
    stack_get_depth (Var v) ps.ps_stack` by
    (strip_tac >> Cases_on `MEM (Var v) prefix`
     >- (`MEM (Var v) ps.ps_stack` by
           metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
         `IS_SOME (stack_get_depth (Var v) ps.ps_stack)` by
           simp[stack_get_depth_is_some] >>
         Cases_on `stack_get_depth (Var v) ps.ps_stack` >> gvs[] >>
         metis_tac[stack_get_depth_suffix_hit]) >>
     simp[stack_get_depth_bottom_excluded]) >>
  Cases_on `FLOOKUP ps.ps_spilled (Var v)` >>
  simp[do_restore_def, stack_push_def, SNOC_APPEND, APPEND_ASSOC,
       stack_get_depth_bottom_excluded] >>
  Cases_on `MEM v nl` >> simp[] >>
  TRY (rename1 `SOME off` >>
       simp[stack_get_depth_def, REVERSE_APPEND, stack_find_def, do_dup_def,
            stack_dup_def, stack_peek_def, EL_APPEND2, SNOC_APPEND, APPEND_ASSOC] >>
       NO_TAC) >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by metis_tac[planWfTheory.stack_get_depth_bound] >>
  Cases_on `do_dup d ps` >> drule_all do_dup_bottom_frame >> simp[]
QED

Theorem emit_one_input_bottom_frame:
  !op prefix opc nl ps.
    EVERY (\x. ~is_var_operand x) prefix ==>
    emit_one_input opc nl op (ps with ps_stack := prefix ++ ps.ps_stack) =
      (FST (emit_one_input opc nl op ps),
       (SND (emit_one_input opc nl op ps)) with ps_stack :=
         prefix ++ (SND (emit_one_input opc nl op ps)).ps_stack)
Proof
  rpt strip_tac >> irule emit_one_input_shielded_bottom_frame >>
  gvs[EVERY_MEM] >> metis_tac[stackPlanTypesTheory.is_var_operand_def]
QED

Theorem emit_input_plan_shielded_bottom_frame:
  !operands prefix opc nl ps ops qs.
    (!v. MEM (Var v) operands ==> ~MEM (Var v) prefix \/
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (ops,qs) ==>
    emit_input_plan opc operands nl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct_on `operands` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `!v. h = Var v ==> ~MEM (Var v) prefix \/
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[MEM] >>
  drule emit_one_input_shielded_bottom_frame >>
  disch_then (qspecl_then [`opc`, `operand_vars operands ++ nl`]
    assume_tac) >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops, mid)` >>
  `!v. MEM (Var v) operands ==> ~MEM (Var v) prefix \/
    MEM (Var v) mid.ps_stack \/ Var v IN FDOM mid.ps_spilled` by
    (rpt strip_tac >> metis_tac[MEM, emit_one_input_available_preserved]) >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  gvs[emit_input_plan_cons] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem emit_input_plan_bottom_frame:
  !operands prefix opc nl ps ops qs.
    EVERY (\x. ~is_var_operand x) prefix /\
    emit_input_plan opc operands nl ps = (ops,qs) ==>
    emit_input_plan opc operands nl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule emit_input_plan_shielded_bottom_frame >>
  goal_assum (drule_at Any) >> gvs[EVERY_MEM] >>
  metis_tac[stackPlanTypesTheory.is_var_operand_def]
QED

Theorem emit_input_plan_marker_core_budget:
  !ps m core base pending opc operands nl ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base pending (ps with ps_stack := core) /\
    emit_input_plan opc operands nl ps = (ops,qs) ==>
    ?core'. qs.ps_stack = REPLICATE m dead_stack_marker ++ core' /\
      residual_budget_wf base (pending ++ operands)
        (qs with ps_stack := core')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_input_plan opc operands nl (ps with ps_stack := core)` >>
  rename1 `emit_input_plan _ _ _ _ = (core_ops, core_state)` >>
  `EVERY (\x. ~is_var_operand x) (REPLICATE m dead_stack_marker)` by
    simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
  drule_all emit_input_plan_bottom_frame >> simp[] >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> strip_tac >>
  `ps with ps_stack := REPLICATE m dead_stack_marker ++ core = ps` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  gvs[] >> qexists_tac `core_state.ps_stack` >> simp[]
QED


Theorem FIND_member_cong[local]:
  !xs P Q. (!x. MEM x xs ==> (P x <=> Q x)) ==>
    FIND P xs = FIND Q xs
Proof
  Induct >> simp[listTheory.FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[]
QED

Theorem stack_get_unfixed_depth_suffix_hit:
  !op f n core d prefix.
    stack_get_unfixed_depth op f n core = SOME d ==>
    stack_get_unfixed_depth op f n (prefix ++ core) = SOME d
Proof
  rpt gen_tac >> Cases_on `n <= f + 1`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_suffix_hit] >>
  asm_rewrite_tac[stack_get_unfixed_depth_def, LENGTH_APPEND] >>
  strip_tac >>
  `GENLIST I (LENGTH prefix + LENGTH core) =
    GENLIST I (LENGTH core) ++
    GENLIST (\t. t + LENGTH core) (LENGTH prefix)` by
      simp[Once arithmeticTheory.ADD_COMM, GENLIST_APPEND] >>
  asm_rewrite_tac[callLayoutDefsTheory.FIND_APPEND_CASE] >>
  `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d (prefix ++ core) = op)
      (GENLIST I (LENGTH core)) =
    FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
      (GENLIST I (LENGTH core))` by
    (irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
     simp[stack_peek_def, EL_APPEND2]) >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem stack_get_unfixed_depth_bottom_excluded:
  !op prefix core f n. ~MEM op prefix ==>
    stack_get_unfixed_depth op f n (prefix ++ core) =
    stack_get_unfixed_depth op f n core
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `n <= f + 1`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_bottom_excluded] >>
  asm_rewrite_tac[stack_get_unfixed_depth_def, LENGTH_APPEND] >>
  `GENLIST I (LENGTH prefix + LENGTH core) =
    GENLIST I (LENGTH core) ++
    GENLIST (\t. t + LENGTH core) (LENGTH prefix)` by
      simp[Once arithmeticTheory.ADD_COMM, GENLIST_APPEND] >>
  asm_rewrite_tac[callLayoutDefsTheory.FIND_APPEND_CASE] >>
  `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d (prefix ++ core) = op)
      (GENLIST I (LENGTH core)) =
    FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
      (GENLIST I (LENGTH core))` by
    (irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
     simp[stack_peek_def, EL_APPEND2]) >>
  asm_rewrite_tac[] >>
  Cases_on `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
    (GENLIST I (LENGTH core))` >> simp[] >>
  Cases_on `FIND (\d. ~(f < d /\ d < n) /\
    stack_peek d (prefix ++ core) = op)
    (GENLIST (\t. t + LENGTH core) (LENGTH prefix))` >> gvs[] >>
  drule stackPlanGenTheory.FIND_SOME_MEM >> disch_then strip_assume_tac >>
  qpat_x_assum `MEM _ (GENLIST _ _)` mp_tac >>
  rewrite_tac[MEM_GENLIST] >> strip_tac >>
  `x < LENGTH core + LENGTH prefix /\ LENGTH core <= x` by (fs[] >> decide_tac) >>
  `LENGTH (prefix ++ core) - (x + 1) < LENGTH prefix` by simp[] >>
  `MEM (stack_peek x (prefix ++ core)) prefix` by
    (simp[stack_peek_def, EL_APPEND1] >> irule EL_MEM >> decide_tac) >>
  metis_tac[]
QED

Theorem stack_get_unfixed_depth_shielded[local]:
  !op f n core prefix.
    (~MEM op prefix \/ IS_SOME (stack_get_unfixed_depth op f n core)) ==>
    stack_get_unfixed_depth op f n (prefix ++ core) =
      stack_get_unfixed_depth op f n core
Proof
  rpt strip_tac >- simp[stack_get_unfixed_depth_bottom_excluded] >>
  Cases_on `stack_get_unfixed_depth op f n core` >> gvs[] >>
  metis_tac[stack_get_unfixed_depth_suffix_hit]
QED

Theorem select_spill_candidate_bottom_frame:
  !prefix core targets dist n. dist < LENGTH core ==>
    select_spill_candidate (prefix ++ core) targets dist n =
    select_spill_candidate core targets dist n
Proof
  rpt gen_tac >> strip_tac >>
  `MIN (dist - 1) (LENGTH (prefix ++ core) - 1) = dist - 1 /\
   MIN (dist - 1) (LENGTH core - 1) = dist - 1` by simp[arithmeticTheory.MIN_DEF] >>
  asm_rewrite_tac[select_spill_candidate_def, LET_THM] >> BETA_TAC >>
  irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
  `x < LENGTH core` by (fs[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  simp[stack_peek_def, EL_APPEND2]
QED

Theorem do_restore_bottom_frame:
  !op ps prefix ops qs. do_restore op ps = (ops,qs) ==>
    do_restore op (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stack_push_def, SNOC_APPEND, APPEND_ASSOC] >> strip_tac >> gvs[]
QED

Theorem do_spill_at_bottom_frame:
  !d ps prefix ops qs.
    d < LENGTH ps.ps_stack /\ d <= 16 /\ do_spill_at d ps = (ops,qs) ==>
    do_spill_at d (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `d = 0` >> gvs[do_spill_at_def, do_spill_tos_def] >>
  simp[stack_swap_bottom_extension, stack_peek_def, EL_APPEND2,
       stack_pop_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
       stackPlanTypesTheory.plan_state_component_equality] >>
  pairarg_tac >> gvs[stack_pop_def, stack_peek_def]
QED

Theorem do_swap_bottom_frame:
  !d ps prefix ops qs.
    d < LENGTH ps.ps_stack /\ do_swap d ps = (ops,qs) ==>
    do_swap d (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `d < LENGTH core`) do_swap_prefix_replay >>
  disch_then (qspecl_then [`ps`, `ps with ps_stack := prefix ++ ps.ps_stack`,
    `[]`, `prefix`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem reduce_depth_plan_unfixed_hit:
  !fuel targets op f n ps ops qs.
    MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack) /\
    reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    IS_SOME (stack_get_unfixed_depth op f n qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME d` >>
  Cases_on `d <= 16`
  >- (`reduce_depth_plan fuel targets op f n ps = ([],ps)` by
        (irule planWfTheory.reduce_depth_plan_le_16 >> simp[]) >> gvs[]) >>
  `d > 16` by decide_tac >>
  drule_all planWfTheory.reduce_depth_plan_dist_ge >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED

Theorem reduce_depth_plan_shielded_bottom_frame:
  !fuel targets op f n ps prefix ops qs.
    (~MEM op prefix \/
      (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack))) /\
    reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    reduce_depth_plan fuel targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct_on `fuel` >- simp[reduce_depth_plan_def] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `f + 1 < n` >- gvs[reduce_depth_plan_def] >>
  `stack_get_unfixed_depth op f n (prefix ++ ps.ps_stack) =
    stack_get_unfixed_depth op f n ps.ps_stack` by
      (irule stack_get_unfixed_depth_shielded >> metis_tac[]) >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack`
  >- gvs[reduce_depth_plan_def] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >- gvs[reduce_depth_plan_def] >>
  `dist < LENGTH ps.ps_stack` by
    metis_tac[stack_get_unfixed_depth_bound] >>
  `select_spill_candidate (prefix ++ ps.ps_stack) targets dist n =
    select_spill_candidate ps.ps_stack targets dist n` by
      simp[select_spill_candidate_bottom_frame] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n`
  >- gvs[reduce_depth_plan_def] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (drule_at (Pat `select_spill_candidate _ _ _ _ = SOME _`)
       planWfTheory.select_spill_candidate_bound >>
     simp[]) >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops, mid)` >>
  drule_all do_spill_at_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >>
  `~MEM op prefix \/
    (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n mid.ps_stack))` by
    (Cases_on `MEM op prefix` >> gvs[] >>
     `reduce_depth_plan (SUC 0) targets op f n ps = (spill_ops,mid)` by
       simp[reduce_depth_plan_def] >>
     irule reduce_depth_plan_unfixed_hit >>
     qexistsl [`SUC 0`, `spill_ops`, `ps`, `targets`] >> simp[]) >>
  Cases_on `reduce_depth_plan fuel targets op f n mid` >>
  `reduce_depth_plan fuel targets op f n
     (mid with ps_stack := prefix ++ mid.ps_stack) =
   (q,r with ps_stack := prefix ++ r.ps_stack)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!targets op f n ps prefix ops qs. _` kall_tac >>
  qpat_x_assum `reduce_depth_plan (SUC fuel) _ _ _ _ _ = _` mp_tac >>
  simp[Once reduce_depth_plan_def] >> strip_tac >>
  simp[Once reduce_depth_plan_def] >> gvs[]
QED

Theorem reduce_depth_plan_bottom_frame:
  !fuel targets op f n ps prefix ops qs.
    ~MEM op prefix /\ reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    reduce_depth_plan fuel targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule reduce_depth_plan_shielded_bottom_frame >> simp[]
QED

Theorem reduce_depth_plan_height_shielded_bottom_frame:
  !targets op f n ps prefix ops qs.
    (~MEM op prefix \/
      (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack))) /\
    reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps = (ops,qs) ==>
    reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n ps =
   reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps` by
    (irule reduce_depth_plan_adequate_fuel >> simp[]) >>
  irule reduce_depth_plan_shielded_bottom_frame >> simp[]
QED

Theorem reduce_depth_plan_height_bottom_frame:
  !targets op f n ps prefix ops qs.
    ~MEM op prefix /\
    reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps = (ops,qs) ==>
    reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule reduce_depth_plan_height_shielded_bottom_frame >> simp[]
QED

Theorem stack_poke_bottom_extension:
  !d x prefix core. d < LENGTH core ==>
    stack_poke d x (prefix ++ core) = prefix ++ stack_poke d x core
Proof
  rpt strip_tac >>
  `LENGTH (prefix ++ core) - 1 - d = LENGTH prefix + (LENGTH core - 1 - d)` by
    (simp[] >> decide_tac) >>
  simp[stack_poke_def, LUPDATE_APPEND2]
QED

Theorem reorder_one_shielded_bottom_frame:
  !dfg targets idx op ps prefix ops qs.
    (~MEM op prefix \/
      (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op
        (LENGTH targets - (idx + 1)) (LENGTH targets) ps.ps_stack))) /\
    idx < LENGTH targets /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    reorder_one dfg targets idx op
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac STRIP_ASSUME_TAC) >>
  `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     (prefix ++ ps.ps_stack) =
   stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     ps.ps_stack` by
    (irule stack_get_unfixed_depth_shielded >> metis_tac[]) >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rename1 `_ = (restore_ops, ps1)` >>
  `LENGTH targets <= LENGTH ps1.ps_stack` by
    (gvs[AllCaseEqs()] >>
     qspecl_then [`op`, `ps`] mp_tac planWfTheory.do_restore_length >> simp[] >> decide_tac) >>
  `((case stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
       (LENGTH targets) ps.ps_stack of
       SOME _ => ([], ps with ps_stack := prefix ++ ps.ps_stack)
     | NONE => case FLOOKUP ps.ps_spilled op of
         SOME _ => do_restore op (ps with ps_stack := prefix ++ ps.ps_stack)
       | NONE => ([], ps with ps_stack := prefix ++ ps.ps_stack)) =
     (restore_ops, ps1 with ps_stack := prefix ++ ps1.ps_stack))` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_bottom_frame]) >>
  (Q.SUBGOAL_THEN `~MEM op prefix \/
    (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op
      (LENGTH targets - (idx + 1)) (LENGTH targets) ps1.ps_stack))` assume_tac
    >- (gvs[AllCaseEqs()] >> metis_tac[])) >>
  `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     (prefix ++ ps1.ps_stack) =
   stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     ps1.ps_stack` by
    (irule stack_get_unfixed_depth_shielded >> metis_tac[]) >>
  simp[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps1.ps_stack` >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (reduce_ops, ps2)` >>
  `LENGTH targets <= LENGTH ps2.ps_stack` by
    (gvs[AllCaseEqs()] >> drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `(if x > 16 then
      reduce_depth_plan (LENGTH prefix + LENGTH ps1.ps_stack) targets op
        (LENGTH targets - (idx + 1)) (LENGTH targets)
        (ps1 with ps_stack := prefix ++ ps1.ps_stack)
    else ([],ps1 with ps_stack := prefix ++ ps1.ps_stack)) =
    (reduce_ops,ps2 with ps_stack := prefix ++ ps2.ps_stack)` by
    (Cases_on `x > 16` >> gvs[] >>
     irule (SRULE [LENGTH_APPEND] reduce_depth_plan_height_shielded_bottom_frame) >>
     simp[]) >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  (Q.SUBGOAL_THEN `~MEM op prefix \/
    (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op
      (LENGTH targets - (idx + 1)) (LENGTH targets) ps2.ps_stack))` assume_tac
    >- (Cases_on `MEM op prefix` >> gvs[] >>
        Cases_on `x > 16` >> gvs[] >>
        irule reduce_depth_plan_unfixed_hit >>
        qexistsl [`LENGTH ps1.ps_stack`, `reduce_ops`, `ps1`, `targets`] >> simp[])) >>
  `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     (prefix ++ ps2.ps_stack) =
   stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets)
     ps2.ps_stack` by
    (irule stack_get_unfixed_depth_shielded >> metis_tac[]) >>
  rpt (qpat_x_assum `~MEM op prefix \/ _` kall_tac) >>
  simp[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack` >- (simp[] >> strip_tac >> gvs[]) >>
  fs[] >>
  rename1 `stack_get_unfixed_depth _ _ _ ps2.ps_stack = SOME x'` >>
  `x' < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >>
  Cases_on `x' = LENGTH targets - (idx + 1)`
  >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >>
  qpat_x_assum `(case _ of NONE => _ | SOME _ => _) = (restore_ops,ps1)` kall_tac >>
  qpat_x_assum `(case _ of NONE => _ | SOME _ => _) = (restore_ops,_)` kall_tac >>
  qpat_x_assum `(if _ then _ else _) = (reduce_ops,ps2)` kall_tac >>
  qpat_x_assum `(if _ then _ else _) = (reduce_ops,_)` kall_tac >>
  `stack_peek (LENGTH targets - (idx + 1)) (prefix ++ ps2.ps_stack) =
   stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack` by
    simp[stack_peek_def, EL_APPEND2] >>
  simp[] >> IF_CASES_TAC
  >- (`LENGTH (stack_poke x' (stack_peek (LENGTH targets - (idx + 1))
           ps2.ps_stack) ps2.ps_stack) = LENGTH ps2.ps_stack` by
        simp[stack_poke_def] >>
      simp[stack_poke_bottom_extension] >> strip_tac >>
      gvs[stackPlanTypesTheory.plan_state_component_equality]) >>
  pairarg_tac >> simp[] >> rename1 `do_swap x' ps2 = (swap1,ps3)` >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`x'`, `ps2`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  drule_all do_swap_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >> simp[] >>
  pairarg_tac >> simp[] >> rename1 `do_swap _ ps3 = (swap2,ps4)` >>
  `LENGTH targets - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  qpat_x_assum `do_swap x' ps2 = _` kall_tac >>
  drule_all do_swap_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem reorder_one_bottom_frame:
  !dfg targets idx op ps prefix ops qs.
    ~MEM op prefix /\ idx < LENGTH targets /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    reorder_one dfg targets idx op
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule reorder_one_shielded_bottom_frame >> simp[]
QED

Theorem reduce_depth_plan_spilled_present:
  !fuel targets op f n ps y.
    y IN FDOM ps.ps_spilled ==>
    y IN FDOM (SND (reduce_depth_plan fuel targets op f n ps)).ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n` >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `x <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `y IN FDOM ps'.ps_spilled` by
    (Cases_on `alloc_spill_slot ps.ps_alloc` >>
     qpat_x_assum `do_spill_at _ _ = _` mp_tac >>
     simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
     Cases_on `x' = 0` >> simp[] >> strip_tac >> gvs[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`targets`, `op`, `f`, `n`] mp_tac) >> simp[]
QED

Theorem do_spill_at_available_preserved:
  !d ps ops qs x.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops,qs) /\
    (MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) ==>
    MEM x qs.ps_stack \/ x IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_spill_at_spilled_update >> strip_tac >>
  Cases_on `x = stack_peek d ps.ps_stack` >> simp[] >>
  drule_all do_spill_at_other_stack_count >> strip_tac >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> metis_tac[]
QED

Theorem reduce_depth_plan_available_preserved:
  !fuel targets op f n ps x.
    MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled ==>
    MEM x (SND (reduce_depth_plan fuel targets op f n ps)).ps_stack \/
    x IN FDOM (SND (reduce_depth_plan fuel targets op f n ps)).ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `f + 1 < n` >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n` >> simp[] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `cand < LENGTH ps.ps_stack /\ cand <= 16` by
    (drule stack_get_unfixed_depth_bound >> strip_tac >>
     `1 <= LENGTH ps.ps_stack` by decide_tac >>
     drule_all planWfTheory.select_spill_candidate_bound >> simp[]) >>
  `MEM x ps'.ps_stack \/ x IN FDOM ps'.ps_spilled` by
    metis_tac[do_spill_at_available_preserved] >>
  qpat_x_assum `!targets op f n ps x. _`
    (qspecl_then [`targets`, `op`, `f`, `n`] mp_tac) >>
  disch_then (qspecl_then [`ps'`, `x`] mp_tac) >> simp[]
QED

Theorem reduce_depth_plan_live_reserve:
  !fuel targets op f ps ops qs x.
    reduce_depth_plan fuel targets op f (LENGTH targets) ps = (ops,qs) /\
    LIST_ELEM_COUNT x targets + 1 <= LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) ==>
    LIST_ELEM_COUNT x targets + 1 <= LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `MEM x targets`
  >- (drule reduce_depth_plan_pending_stack_count_unconditional >>
      disch_then drule >> strip_tac >>
      `x IN FDOM ps.ps_spilled ==> x IN FDOM qs.ps_spilled` by
        metis_tac[reduce_depth_plan_spilled_present, pairTheory.SND] >>
      Cases_on `x IN FDOM ps.ps_spilled` >>
      Cases_on `x IN FDOM qs.ps_spilled` >> gvs[] >> decide_tac) >>
  (Q.SUBGOAL_THEN `MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled` assume_tac
    >- (Cases_on `x IN FDOM ps.ps_spilled` >>
        gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac)) >>
  `MEM x qs.ps_stack \/ x IN FDOM qs.ps_spilled` by
    metis_tac[reduce_depth_plan_available_preserved, pairTheory.SND] >>
  Cases_on `x IN FDOM qs.ps_spilled` >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem reorder_one_materialised_live_reserve:
  !dfg targets idx op ps ops qs d v.
    idx < LENGTH targets /\ LENGTH targets <= 16 /\
    LENGTH targets <= LENGTH ps.ps_stack /\ MEM op targets /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) /\
    LIST_ELEM_COUNT (Var v) targets + 1 <=
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) ==>
    LIST_ELEM_COUNT (Var v) targets + 1 <=
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,ps2)` >>
  `LENGTH targets <= LENGTH ps2.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `LIST_ELEM_COUNT (Var v) targets + 1 <=
    LIST_ELEM_COUNT (Var v) ps2.ps_stack +
      (if Var v IN FDOM ps2.ps_spilled then 1 else 0)` by
    (Cases_on `d > 16` >> gvs[] >>
     drule_all reduce_depth_plan_live_reserve >> simp[]) >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack`
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  `dist < LENGTH ps2.ps_stack /\ stack_peek dist ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  simp[] >> Cases_on `dist = LENGTH targets - (idx + 1)`
  >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >>
  qspecl_then [`dfg`, `op`] mp_tac reorder_place_phase_multiplicity >>
  disch_then (qspecl_then [`dist`, `LENGTH targets - (idx + 1)`, `ps2`, `Var v`]
    mp_tac) >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `do_swap (LENGTH targets - (idx + 1)) ps3` >> gvs[] >>
  `ps3.ps_spilled = ps2.ps_spilled` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >>
  `ps'.ps_spilled = ps3.ps_spilled` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >> gvs[]
QED

Theorem reorder_materialised_fold_resources[local]:
  !m k dfg targets ps acc ops qs.
    k + m <= LENGTH targets /\ LENGTH targets <= 16 /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < k ==> stack_peek (LENGTH targets - 1 - i) ps.ps_stack = EL i targets) /\
    FOLDL (\(code,st) (idx,op).
      (\(step,out). (code ++ step,out)) (reorder_one dfg targets idx op st))
      (acc,ps) (GENLIST (\j. (k+j,EL (k+j) targets)) m) = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack /\
    (!i. i < k + m ==>
      stack_peek (LENGTH targets - 1 - i) qs.ps_stack = EL i targets) /\
    (!v. LIST_ELEM_COUNT (Var v) targets + 1 <=
       LIST_ELEM_COUNT (Var v) ps.ps_stack +
         (if Var v IN FDOM ps.ps_spilled then 1 else 0) ==>
       LIST_ELEM_COUNT (Var v) targets + 1 <=
       LIST_ELEM_COUNT (Var v) qs.ps_stack +
         (if Var v IN FDOM qs.ps_spilled then 1 else 0))
Proof
  Induct_on `m` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < LENGTH targets` by decide_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets` >> simp[] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  drule_all materialised_pending_next_on_stack_window >> strip_tac >>
  Cases_on `reorder_one dfg targets k (EL k targets) ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  `MEM (EL k targets) targets` by simp[EL_MEM] >>
  `LENGTH targets - 1 - k = LENGTH targets - (k + 1)` by decide_tac >>
  `LENGTH targets <= LENGTH mid.ps_stack` by metis_tac[reorder_one_target_length] >>
  `!x. MEM x targets ==>
    LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x mid.ps_stack` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`)
       reorder_one_materialised_counts_unconditional >>
     disch_then (qspec_then `d` mp_tac) >> fs[] >> metis_tac[]) >>
  `!i. i < SUC k ==>
    stack_peek (LENGTH targets - 1 - i) mid.ps_stack = EL i targets` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`) reorder_one_advances_fixed_window >>
     simp[]) >>
  `GENLIST (\j. (k+j,EL (k+j) targets)) (SUC m) =
     (k,EL k targets) :: GENLIST (\j. (SUC k+j,EL (SUC k+j) targets)) m` by
    (simp[GENLIST_CONS, arithmeticTheory.ADD_CLAUSES, combinTheory.o_DEF] >>
     AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `FOLDL _ _ _ = (ops,qs)` mp_tac >>
  qpat_x_assum `GENLIST _ (SUC m) = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[listTheory.FOLDL] >>
  CONV_TAC (LAND_CONV (LHS_CONV
    (RATOR_CONV (RAND_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV))))) >>
  qpat_assum `reorder_one _ _ _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `SUC k + m <= LENGTH targets` by decide_tac >>
  qpat_x_assum `!k dfg targets ps acc ops qs. _`
    (qspec_then `SUC k` mp_tac) >>
  disch_then (drule_at (Pat `FOLDL _ _ _ = _`)) >> simp[] >>
  strip_tac >> rpt conj_tac >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  drule_all reorder_one_materialised_live_reserve >> simp[]
QED

Theorem reorder_plan_materialised_bounds[local]:
  !dfg targets ps ops qs.
    LENGTH targets <= 16 /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack /\
    (!i. i < LENGTH targets ==>
      stack_peek (LENGTH targets - 1 - i) qs.ps_stack = EL i targets) /\
    (!v. LIST_ELEM_COUNT (Var v) targets + 1 <=
       LIST_ELEM_COUNT (Var v) ps.ps_stack +
         (if Var v IN FDOM ps.ps_spilled then 1 else 0) ==>
       LIST_ELEM_COUNT (Var v) targets + 1 <=
       LIST_ELEM_COUNT (Var v) qs.ps_stack +
         (if Var v IN FDOM qs.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  `MAPi (\i op. (i,op)) targets =
   GENLIST (\j. (0+j,EL (0+j) targets)) (LENGTH targets)` by
    simp[LIST_EQ_REWRITE, indexedListsTheory.EL_MAPi, EL_GENLIST] >>
  gvs[reorder_plan_def] >>
  qspecl_then [`LENGTH targets`, `0`] mp_tac reorder_materialised_fold_resources >>
  simp[] >> disch_then (drule_at (Pat `FOLDL _ _ _ = _`)) >> simp[]
QED

Theorem reorder_plan_bounded_materialised_suffix:
  !dfg targets ps ops qs.
    LENGTH targets <= 16 /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    qs.ps_stack = stack_pop (LENGTH targets) qs.ps_stack ++ targets
Proof
  rpt strip_tac >> drule_all reorder_plan_materialised_bounds >> strip_tac >>
  irule fixed_suffix_decompose >> simp[]
QED

Theorem reorder_plan_materialised_live_reserve:
  !dfg targets ps ops qs v.
    LENGTH targets <= 16 /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg targets ps = (ops,qs) /\
    LIST_ELEM_COUNT (Var v) targets + 1 <=
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) ==>
    LIST_ELEM_COUNT (Var v) targets + 1 <=
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >> drule_all reorder_plan_materialised_bounds >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem reorder_materialised_fold_bottom_frame[local]:
  !m k dfg targets ps prefix acc ops qs.
    k + m <= LENGTH targets /\ LENGTH targets <= 16 /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < k ==> stack_peek (LENGTH targets - 1 - i) ps.ps_stack = EL i targets) /\
    FOLDL (\(code,st) (idx,op).
      (\(step,out). (code ++ step,out)) (reorder_one dfg targets idx op st))
      (acc,ps) (GENLIST (\j. (k+j,EL (k+j) targets)) m) = (ops,qs) ==>
    FOLDL (\(code,st) (idx,op).
      (\(step,out). (code ++ step,out)) (reorder_one dfg targets idx op st))
      (acc,ps with ps_stack := prefix ++ ps.ps_stack)
      (GENLIST (\j. (k+j,EL (k+j) targets)) m) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct_on `m` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < LENGTH targets` by decide_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets` >> simp[] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  drule_all materialised_pending_next_on_stack_window >> strip_tac >>
  Cases_on `reorder_one dfg targets k (EL k targets) ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  `MEM (EL k targets) targets` by simp[EL_MEM] >>
  `LENGTH targets - 1 - k = LENGTH targets - (k + 1)` by decide_tac >>
  `reorder_one dfg targets k (EL k targets)
     (ps with ps_stack := prefix ++ ps.ps_stack) =
     (step_ops,mid with ps_stack := prefix ++ mid.ps_stack)` by
    (irule reorder_one_shielded_bottom_frame >> fs[]) >>
  `LENGTH targets <= LENGTH mid.ps_stack` by metis_tac[reorder_one_target_length] >>
  `!x. MEM x targets ==>
    LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x mid.ps_stack` by
    (qpat_x_assum `reorder_one _ _ _ _ (ps with ps_stack := _) = _` kall_tac >>
     drule_at (Pat `reorder_one _ _ _ _ _ = _`)
       reorder_one_materialised_counts_unconditional >>
     disch_then (qspec_then `d` mp_tac) >> fs[] >> metis_tac[]) >>
  `!i. i < SUC k ==>
    stack_peek (LENGTH targets - 1 - i) mid.ps_stack = EL i targets` by
    (qpat_x_assum `reorder_one _ _ _ _ (ps with ps_stack := _) = _` kall_tac >>
     drule_at (Pat `reorder_one _ _ _ _ _ = _`) reorder_one_advances_fixed_window >>
     simp[]) >>
  `GENLIST (\j. (k+j,EL (k+j) targets)) (SUC m) =
     (k,EL k targets) :: GENLIST (\j. (SUC k+j,EL (SUC k+j) targets)) m` by
    (simp[GENLIST_CONS, arithmeticTheory.ADD_CLAUSES, combinTheory.o_DEF] >>
     AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `FOLDL _ _ _ = (ops,qs)` mp_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `!k dfg targets ps prefix acc ops qs. _`
    (qspec_then `SUC k` mp_tac) >>
  simp[] >> disch_then irule >> fs[]
QED

Theorem reorder_plan_materialised_bottom_frame:
  !dfg targets ps prefix ops qs.
    LENGTH targets <= 16 /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    reorder_plan dfg targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `MAPi (\i op. (i,op)) targets =
   GENLIST (\j. (0+j,EL (0+j) targets)) (LENGTH targets)` by
    simp[LIST_EQ_REWRITE, indexedListsTheory.EL_MAPi, EL_GENLIST] >>
  gvs[reorder_plan_def] >>
  qspecl_then [`LENGTH targets`, `0`] mp_tac reorder_materialised_fold_bottom_frame >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem emit_reorder_plan_shielded_bottom_frame:
  !opc operands selected nl ps prefix dfg iops ps1 rops ps2.
    LENGTH operands <= 16 /\
    (!x. MEM x operands /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    emit_input_plan opc operands nl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (iops,ps1 with ps_stack := prefix ++ ps1.ps_stack) /\
    reorder_plan dfg selected
      (ps1 with ps_stack := prefix ++ ps1.ps_stack) =
      (rops,ps2 with ps_stack := prefix ++ ps2.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  conj_tac
  >- (irule emit_input_plan_shielded_bottom_frame >> simp[] >>
      rpt strip_tac >> first_x_assum (qspec_then `Var v` mp_tac) >>
      simp[stackPlanTypesTheory.is_var_operand_def]) >>
  irule reorder_plan_materialised_bottom_frame >> simp[] >> metis_tac[]
QED

(* The two speculative reorders below start from the emitted state, as in
   the non-JMP preparation branch of generate_regular_inst_plan. *)
Theorem emitted_commutative_preparation_bottom_frame:
  !opc operands nl ps prefix dfg iops ps1 rops ps2.
    LENGTH operands <= 16 /\
    (!x. MEM x operands /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    (if is_commutative opc /\ 2 <= LENGTH operands then
       case reorder_plan dfg operands ps1 of (ops_a,ps_a) =>
       case reorder_plan dfg
         (TAKE (LENGTH operands - 2) operands ++
          [EL (LENGTH operands - 1) operands;
           EL (LENGTH operands - 2) operands]) ps1 of (ops_b,ps_b) =>
       if reorder_cost ops_a < reorder_cost ops_b then (ops_a,ps_a)
       else (ops_b,ps_b)
     else reorder_plan dfg operands ps1) = (rops,ps2) ==>
    (if is_commutative opc /\ 2 <= LENGTH operands then
       case reorder_plan dfg operands
         (ps1 with ps_stack := prefix ++ ps1.ps_stack) of (ops_a,ps_a) =>
       case reorder_plan dfg
         (TAKE (LENGTH operands - 2) operands ++
          [EL (LENGTH operands - 1) operands;
           EL (LENGTH operands - 2) operands])
         (ps1 with ps_stack := prefix ++ ps1.ps_stack) of (ops_b,ps_b) =>
       if reorder_cost ops_a < reorder_cost ops_b then (ops_a,ps_a)
       else (ops_b,ps_b)
     else reorder_plan dfg operands
       (ps1 with ps_stack := prefix ++ ps1.ps_stack)) =
      (rops,ps2 with ps_stack := prefix ++ ps2.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `reorder_plan dfg operands ps1` >>
  rename1 `reorder_plan dfg operands ps1 = (ops_a,ps_a)` >>
  `PERM operands operands` by simp[] >>
  drule_all emit_reorder_plan_shielded_bottom_frame >> strip_tac >>
  Cases_on `is_commutative opc /\ 2 <= LENGTH operands`
  >- (gvs[] >>
      drule last_two_reorder_perm >> strip_tac >>
      Cases_on `reorder_plan dfg
        (TAKE (LENGTH operands - 2) operands ++
         [EL (LENGTH operands - 1) operands;
          EL (LENGTH operands - 2) operands]) ps1` >>
      rename1 `reorder_plan _ _ _ = (ops_b,ps_b)` >>
      qpat_x_assum `reorder_plan dfg operands ps1 = _` kall_tac >>
      drule_all emit_reorder_plan_shielded_bottom_frame >>
      disch_then (qspec_then `prefix` strip_assume_tac) >>
      Cases_on `reorder_cost ops_a < reorder_cost ops_b` >> gvs[]) >>
  gvs[]
QED

Theorem reorder_fold_bottom_frame[local]:
  !steps dfg targets ps prefix acc ops qs.
    EVERY (\(idx,op). idx < LENGTH targets /\ ~MEM op prefix) steps /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    FOLDL (\(ops,ps) (idx,op).
      let (step,ps') = reorder_one dfg targets idx op ps in
      (ops ++ step,ps')) (acc,ps) steps = (ops,qs) ==>
    FOLDL (\(ops,ps) (idx,op).
      let (step,ps') = reorder_one dfg targets idx op ps in
      (ops ++ step,ps')) (acc,ps with ps_stack := prefix ++ ps.ps_stack) steps =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct >- (simp[] >> rpt strip_tac >> gvs[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[] >> strip_tac >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,ps_mid)` >>
  `LENGTH targets <= LENGTH ps_mid.ps_stack` by
    metis_tac[reorder_one_target_length] >>
  drule_all reorder_one_bottom_frame >> simp[] >> strip_tac >>
  first_x_assum (irule o SRULE [LET_THM]) >> gvs[]
QED

Theorem reorder_plan_bottom_frame:
  !dfg targets ps prefix ops qs.
    EVERY (\op. ~MEM op prefix) targets /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    reorder_plan dfg targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> simp[reorder_plan_def] >> strip_tac >>
  irule (SRULE [LET_THM] reorder_fold_bottom_frame) >> simp[] >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
  rpt strip_tac >> gvs[] >> metis_tac[EL_MEM]
QED

(* Count-free preparation frame. Input emission needs a non-variable
   prefix, not merely exclusion of the current inputs. Coverage produces
   the core-height floor; repeated inputs/core values are permitted. *)
Theorem emit_reorder_plan_bottom_frame:
  !opc inputs nl ps iops ps1 dfg targets rops ps2 prefix.
    emit_input_plan opc inputs nl ps = (iops,ps1) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    EVERY (\op. ~is_var_operand op) prefix /\
    EVERY (\op. ~MEM op prefix) targets /\
    LENGTH targets <= LENGTH inputs /\
    reorder_plan dfg targets ps1 = (rops,ps2) ==>
    LENGTH targets <= LENGTH ps1.ps_stack /\
    emit_input_plan opc inputs nl (ps with ps_stack := prefix ++ ps.ps_stack) =
      (iops,ps1 with ps_stack := prefix ++ ps1.ps_stack) /\
    reorder_plan dfg targets (ps1 with ps_stack := prefix ++ ps1.ps_stack) =
      (rops,ps2 with ps_stack := prefix ++ ps2.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  `LENGTH targets <= LENGTH ps1.ps_stack` by decide_tac >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule emit_input_plan_bottom_frame >> simp[]) >>
  irule reorder_plan_bottom_frame >> simp[]
QED

(* General list boundary moved from fnPlanLineagePhiTemporal. *)
Theorem stack_pop_bottom_extension:
  !n prefix core. n <= LENGTH core ==>
    stack_pop n (prefix ++ core) = prefix ++ stack_pop n core
Proof
  rpt strip_tac >> simp[stack_pop_def, TAKE_APPEND]
QED

Theorem emit_reorder_consume_bottom_frame:
  !opc inputs nl ps iops ps1 dfg targets rops ps2 prefix n.
    emit_input_plan opc inputs nl ps = (iops,ps1) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    EVERY (\op. ~is_var_operand op) prefix /\
    EVERY (\op. ~MEM op prefix) targets /\
    LENGTH targets <= LENGTH inputs /\
    reorder_plan dfg targets ps1 = (rops,ps2) /\
    n <= LENGTH targets ==>
    LENGTH targets <= LENGTH ps2.ps_stack /\
    emit_input_plan opc inputs nl (ps with ps_stack := prefix ++ ps.ps_stack) =
      (iops,ps1 with ps_stack := prefix ++ ps1.ps_stack) /\
    reorder_plan dfg targets (ps1 with ps_stack := prefix ++ ps1.ps_stack) =
      (rops,ps2 with ps_stack := prefix ++ ps2.ps_stack) /\
    stack_pop n (prefix ++ ps2.ps_stack) = prefix ++ stack_pop n ps2.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_reorder_plan_bottom_frame >> strip_tac >>
  drule_all reorder_plan_target_length >> strip_tac >>
  simp[] >> irule stack_pop_bottom_extension >> decide_tac
QED

Theorem reorder_plan_marker_core_inventory:
  !ps m core base pending dfg ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base pending (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) pending /\
    LENGTH pending <= LENGTH core /\ LENGTH pending <= 16 /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    ?core'. qs.ps_stack = REPLICATE m dead_stack_marker ++ core' /\
      residual_budget_wf base pending (qs with ps_stack := core') /\
      LENGTH pending <= LENGTH core' /\
      (!v. LIST_ELEM_COUNT (Var v) core +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) core' +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `reorder_plan dfg pending (ps with ps_stack := core)` >>
  rename1 `reorder_plan _ _ _ = (core_ops, core_state)` >>
  `LENGTH pending <= LENGTH (ps with ps_stack := core).ps_stack` by simp[] >>
  drule_all reorder_plan_inventory_mono >> strip_tac >>
  `EVERY (\op. ~MEM op (REPLICATE m dead_stack_marker)) pending` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_REPLICATE]) >>
  `ps with ps_stack := REPLICATE m dead_stack_marker ++ core = ps` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  drule_all reorder_plan_bottom_frame >> simp[] >> strip_tac >>
  gvs[] >> qexists_tac `core_state.ps_stack` >> simp[]
QED

Theorem reorder_plan_marker_core_reserve:
  !ps m core base pending nl dfg ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base pending (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) pending /\
    LENGTH pending <= LENGTH core /\ LENGTH pending <= 16 /\
    (!v. LIST_ELEM_COUNT (Var v) pending + (if MEM v nl then 1 else 0) <=
      LIST_ELEM_COUNT (Var v) core +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0)) /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    ?core'. qs.ps_stack = REPLICATE m dead_stack_marker ++ core' /\
      residual_budget_wf base pending (qs with ps_stack := core') /\
      LENGTH pending <= LENGTH core' /\
      (!v. LIST_ELEM_COUNT (Var v) pending + (if MEM v nl then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) core' +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reorder_plan_marker_core_inventory >> strip_tac >>
  qexists_tac `core'` >> simp[] >> gen_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  qpat_x_assum `!v. LIST_ELEM_COUNT (Var v) pending + _ <= _`
    (qspec_then `v` mp_tac) >> decide_tac
QED

Theorem emit_reorder_plan_marker_core_reserve:
  !ps m core base operands opc nl dfg iops ps1 rops ps2.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands \/ MEM v nl ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg operands ps1 = (rops,ps2) ==>
    ?core'. ps2.ps_stack = REPLICATE m dead_stack_marker ++ core' /\
      residual_budget_wf base operands (ps2 with ps_stack := core') /\
      LENGTH operands <= LENGTH core' /\
      (!v. LIST_ELEM_COUNT (Var v) operands + (if MEM v nl then 1 else 0) <=
        LIST_ELEM_COUNT (Var v) core' +
        (if Var v IN FDOM ps2.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_input_plan opc operands nl (ps with ps_stack := core)` >>
  rename1 `emit_input_plan _ _ _ _ = (core_ops,core_state)` >>
  qpat_x_assum `emit_input_plan _ _ _ ps = _` mp_tac >>
  `!v. MEM (Var v) operands \/ MEM v nl ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  drule_all emit_input_plan_live_reserve >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op (ps with ps_stack := core).ps_stack \/
      op IN FDOM (ps with ps_stack := core).ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  `EVERY (\x. ~is_var_operand x) (REPLICATE m dead_stack_marker)` by
    simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
  `ps with ps_stack := REPLICATE m dead_stack_marker ++ core = ps` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  `emit_input_plan opc operands nl ps =
    (core_ops,core_state with ps_stack :=
      REPLICATE m dead_stack_marker ++ core_state.ps_stack)` by
    (qpat_assum `emit_input_plan _ _ _ (ps with ps_stack := core) = _`
       (mp_then Any mp_tac emit_input_plan_bottom_frame) >>
     disch_then (qspec_then `REPLICATE m dead_stack_marker` mp_tac) >> simp[]) >>
  strip_tac >>
  qpat_x_assum `emit_input_plan _ _ _ (ps with ps_stack := core) = _` kall_tac >>
  qpat_x_assum `(ps with ps_stack := _) = ps` kall_tac >>
  `ps1 = core_state with ps_stack :=
    REPLICATE m dead_stack_marker ++ core_state.ps_stack` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `emit_input_plan _ _ _ ps = (iops,ps1)` kall_tac >>
  qpat_x_assum `emit_input_plan _ _ _ ps = _` kall_tac >>
  pop_assum SUBST_ALL_TAC >>
  irule reorder_plan_marker_core_reserve >> simp[] >>
  qexistsl_tac [`core_state.ps_stack`, `dfg`, `rops`,
    `core_state with ps_stack := REPLICATE m dead_stack_marker ++ core_state.ps_stack`] >>
  simp[]
QED

Theorem residual_budget_wf_suffix_cancel:
  !base pending ps rest.
    ps.ps_stack = rest ++ pending /\ residual_budget_wf base pending ps ==>
    residual_budget_wf base [] (ps with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[residual_budget_wf_def, elem_count_append, LIST_ELEM_COUNT_THM] >>
  conj_tac
  >- (gen_tac >> qpat_x_assum `!op. _ <= SUC _`
        (qspec_then `op` mp_tac) >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem live_reserve_suffix_cancel:
  !pending rest spilled nl.
    (!v. LIST_ELEM_COUNT (Var v) pending + (if MEM v nl then 1 else 0) <=
      LIST_ELEM_COUNT (Var v) (rest ++ pending) +
      (if Var v IN FDOM spilled then 1 else 0)) ==>
    !v. MEM v nl ==> MEM (Var v) rest \/ Var v IN FDOM spilled
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `Var v IN FDOM spilled` >> simp[elem_count_append] >>
  Cases_on `MEM (Var v) rest` >> simp[] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem emit_reorder_plan_bounded_core_suffix:
  !ps operands selected opc nl dfg iops ps1 rops ps2.
    LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    ps2.ps_stack = stack_pop (LENGTH selected) ps2.ps_stack ++ selected
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  irule reorder_plan_bounded_materialised_suffix >> simp[] >>
  qexistsl_tac [`dfg`, `rops`, `ps1`] >> simp[] >> metis_tac[]
QED

Theorem emit_reorder_plan_bounded_protected_consumption:
  !ps operands selected opc nl keep dfg iops ps1 rops ps2.
    LENGTH operands <= 16 /\ set keep SUBSET set nl /\
    (!v. MEM (Var v) operands \/ MEM v keep ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    !v. MEM v keep ==> MEM (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) \/
      Var v IN FDOM ps2.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all emit_reorder_plan_bounded_core_suffix >> strip_tac >>
  drule_all emit_input_plan_protected_live_reserve >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  match_mp_tac live_reserve_suffix_cancel >> qexists_tac `selected` >>
  gen_tac >> Cases_on `MEM v keep`
  >- (`LIST_ELEM_COUNT (Var v) selected + 1 <=
         LIST_ELEM_COUNT (Var v) ps1.ps_stack +
           (if Var v IN FDOM ps1.ps_spilled then 1 else 0)` by
        (qpat_x_assum `!v. LIST_ELEM_COUNT (Var v) operands + _ <= _`
           (qspec_then `v` mp_tac) >> simp[]) >>
      `LIST_ELEM_COUNT (Var v) selected + 1 <=
         LIST_ELEM_COUNT (Var v) ps2.ps_stack +
           (if Var v IN FDOM ps2.ps_spilled then 1 else 0)` by
        (irule reorder_plan_materialised_live_reserve >> simp[] >>
         qexistsl_tac [`dfg`, `rops`, `ps1`] >> simp[] >> metis_tac[]) >>
      simp[] >> qpat_x_assum `ps2.ps_stack = _`
        (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  simp[elem_count_append]
QED

Theorem emit_reorder_plan_core_suffix:
  !ps base operands selected opc nl dfg iops ps1 rops ps2.
    residual_budget_wf base [] ps /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    ps2.ps_stack = stack_pop (LENGTH selected) ps2.ps_stack ++ selected
Proof
  metis_tac[emit_reorder_plan_bounded_core_suffix]
QED

Theorem emit_reorder_plan_core_protected_consumption:
  !ps base operands selected opc nl keep dfg iops ps1 rops ps2.
    residual_budget_wf base [] ps /\ LENGTH operands <= 16 /\
    set keep SUBSET set nl /\
    (!v. MEM (Var v) operands \/ MEM v keep ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    residual_budget_wf base []
      (ps2 with ps_stack := stack_pop (LENGTH selected) ps2.ps_stack) /\
    (!v. MEM v keep ==> MEM (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) \/
      Var v IN FDOM ps2.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> rename1 `residual_budget_wf spillbase [] ps` >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all emit_reorder_plan_core_suffix >> strip_tac >>
  drule_all emit_input_plan_protected_live_reserve >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `residual_budget_wf spillbase selected ps1` by
    metis_tac[residual_budget_wf_perm] >>
  `LENGTH selected <= LENGTH ps1.ps_stack /\ LENGTH selected <= 16` by simp[] >>
  drule_all reorder_plan_inventory_mono >> strip_tac >>
  reverse conj_tac
  >- metis_tac[emit_reorder_plan_bounded_protected_consumption] >>
  irule residual_budget_wf_suffix_cancel >>
  qexists_tac `selected` >> simp[]
QED

Theorem emit_reorder_plan_core_consumption:
  !ps base operands selected opc nl dfg iops ps1 rops ps2.
    residual_budget_wf base [] ps /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands \/ MEM v nl ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    residual_budget_wf base []
      (ps2 with ps_stack := stack_pop (LENGTH selected) ps2.ps_stack) /\
    (!v. MEM v nl ==> MEM (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) \/
      Var v IN FDOM ps2.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  irule emit_reorder_plan_core_protected_consumption >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`iops`, `nl`, `opc`, `operands`, `ps`] >> simp[] >> metis_tac[]
QED

Theorem emit_reorder_pop_marker_execution:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    ?ci cs1 cr cs2.
      emit_input_plan opc operands nl (ps with ps_stack := core) = (ci,cs1) /\
      reorder_plan dfg selected cs1 = (cr,cs2) /\
      LENGTH selected <= LENGTH cs2.ps_stack /\
      qs = cs2 with ps_stack := REPLICATE m dead_stack_marker ++
        stack_pop (LENGTH selected) cs2.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_input_plan opc operands nl (ps with ps_stack := core)` >>
  rename1 `emit_input_plan _ _ _ _ = (ci,cs1)` >>
  Cases_on `reorder_plan dfg selected cs1` >>
  rename1 `reorder_plan _ _ cs1 = (cr,cs2)` >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op (ps with ps_stack := core).ps_stack \/
      op IN FDOM (ps with ps_stack := core).ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LENGTH selected <= LENGTH cs1.ps_stack` by simp[] >>
  `EVERY (\x. ~is_var_operand x) (REPLICATE m dead_stack_marker)` by
    simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
  `EVERY (\x. ~MEM x (REPLICATE m dead_stack_marker)) selected` by
    (gvs[EVERY_MEM] >> metis_tac[sortingTheory.PERM_MEM_EQ, MEM_REPLICATE]) >>
  `ps with ps_stack := REPLICATE m dead_stack_marker ++ core = ps` by
    simp[stackPlanTypesTheory.plan_state_component_equality] >>
  `ps1 = cs1 with ps_stack := REPLICATE m dead_stack_marker ++ cs1.ps_stack` by
    (qpat_assum `emit_input_plan _ _ _ (ps with ps_stack := core) = _`
       (mp_then Any mp_tac emit_input_plan_bottom_frame) >>
     disch_then (qspec_then `REPLICATE m dead_stack_marker` mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  `ps2 = cs2 with ps_stack := REPLICATE m dead_stack_marker ++ cs2.ps_stack` by
    (qpat_assum `reorder_plan _ _ cs1 = _`
       (mp_then Any mp_tac reorder_plan_bottom_frame) >>
     disch_then (qspec_then `REPLICATE m dead_stack_marker` mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  drule_all emit_reorder_plan_core_suffix >> strip_tac >>
  `LENGTH selected <= LENGTH cs2.ps_stack` by
    (qpat_assum `cs2.ps_stack = _`
       (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
     pure_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  qpat_x_assum `(ps with ps_stack := _) = ps` kall_tac >>
  qexistsl_tac [`ci`, `cs1`, `cr`, `cs2`] >>
  `m <= m + LENGTH cs2.ps_stack - LENGTH selected` by decide_tac >>
  gvs[stack_pop_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem emit_reorder_pop_marker_core_protected_reserve:
  !ps m core base operands selected opc nl keep dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    set keep SUBSET set nl /\
    (!v. MEM (Var v) operands \/ MEM v keep ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf base [] (qs with ps_stack := rest) /\
      (!v. MEM v keep ==> MEM (Var v) rest \/ Var v IN FDOM qs.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all emit_reorder_pop_marker_execution >> strip_tac >>
  `!v. MEM (Var v) operands \/ MEM v keep ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  drule_all emit_reorder_plan_core_protected_consumption >> strip_tac >>
  qpat_x_assum `qs = ps2 with ps_stack := _` kall_tac >>
  qexists_tac `stack_pop (LENGTH selected) cs2.ps_stack` >> gvs[]
QED


Theorem emit_reorder_pop_marker_core_reserve:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands \/ MEM v nl ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf base [] (qs with ps_stack := rest) /\
      (!v. MEM v nl ==> MEM (Var v) rest \/ Var v IN FDOM qs.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  irule emit_reorder_pop_marker_core_protected_reserve >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[SUBSET_REFL]
QED

Theorem stack_pop_swap_retains_other:
  !(s : operand list) d x. d < LENGTH s /\ MEM x s /\ x <> stack_peek d s ==>
    MEM x (stack_pop 1 (stack_swap d s))
Proof
  rpt gen_tac >> strip_tac >>
  `PERM (stack_swap d s) s` by
    (qspec_then `ARB with ps_stack := s` mp_tac
       (Q.SPEC `d` do_swap_stack_perm) >> simp[do_swap_stack_result]) >>
  `set (stack_swap d s) = set s` by metis_tac[sortingTheory.PERM_LIST_TO_SET] >>
  `stack_swap d s <> []` by
    (strip_tac >> gvs[stack_swap_def]) >>
  `LAST (stack_swap d s) = stack_peek d s` by
    (`PRE (LENGTH s) = LENGTH s - 1` by decide_tac >>
     simp[LAST_EL, stack_swap_def, stack_peek_def, EL_LUPDATE] >>
     rpt IF_CASES_TAC >> gvs[]) >>
  `MEM x (stack_swap d s)` by ASM_SET_TAC[] >>
  `MEM x (FRONT (stack_swap d s))` by
    metis_tac[MEM_SNOC, SNOC_LAST_FRONT] >>
  gvs[stack_pop_def, FRONT_BY_TAKE]
QED

Theorem popmany_fold_retains_other[local]:
  !to_pop ops ps x.
    MEM x ps.ps_stack /\ ~MEM x to_pop ==>
    MEM x (SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          (ops ++ FST (if dist = 0 then ([], ps) else do_swap dist ps) ++ [SOPop 1],
           (SND (if dist = 0 then ([], ps) else do_swap dist ps)) with
             ps_stack := stack_pop 1
               (SND (if dist = 0 then ([], ps) else do_swap dist ps)).ps_stack))
      (ops, ps) to_pop)).ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[] >>
  `(if x' = 0 then ([], ps) else do_swap x' ps) = do_swap x' ps` by
    (Cases_on `x' = 0` >> simp[do_swap_def]) >>
  simp[] >> first_x_assum irule >> simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  simp[do_swap_stack_result] >> irule stack_pop_swap_retains_other >> simp[]
QED

Theorem popmany_individual_retains_other:
  !to_pop ps x. MEM x ps.ps_stack /\ ~MEM x to_pop ==>
    MEM x (SND (popmany_individual to_pop ps)).ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  simp[popmany_individual_def, LET_THM, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  irule (SRULE [pairTheory.pair_CASE_def, pairTheory.UNCURRY] popmany_fold_retains_other) >>
  simp[sortingTheory.QSORT_MEM]
QED

Theorem popmany_contiguous_retains_other[local]:
  !to_pop ps x.
    to_pop <> [] /\ set to_pop SUBSET set ps.ps_stack /\
    is_contiguous_top (MAP THE (MAP (\op. stack_get_depth op ps.ps_stack) to_pop)) /\
    MEM x ps.ps_stack /\ ~MEM x to_pop ==>
    MEM x (stack_pop (LENGTH to_pop) (SND (do_swap (LENGTH to_pop) ps)).ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH to_pop < LENGTH ps.ps_stack /\
   set to_pop = set (MAP (\d. stack_peek d ps.ps_stack)
     (GENLIST SUC (LENGTH to_pop)))` by
    (mp_tac (Q.SPECL [`to_pop`, `[]`, `ps.ps_stack`, `ps`] contiguous_depths_core) >> simp[]) >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  `?rest top. ps.ps_stack = SNOC top rest` by metis_tac[SNOC_CASES] >>
  `LENGTH to_pop <= LENGTH rest` by gvs[] >>
  `?lower removed. ps.ps_stack = lower ++ removed ++ [top] /\
    LENGTH removed = LENGTH to_pop` by
    (qexistsl_tac [`TAKE (LENGTH rest - LENGTH to_pop) rest`,
                  `DROP (LENGTH rest - LENGTH to_pop) rest`] >>
     conj_tac
     >- (pure_rewrite_tac[GSYM APPEND_ASSOC, TAKE_DROP] >> simp[SNOC_APPEND]) >>
     simp[LENGTH_DROP]) >>
  `set to_pop = set removed` by
    (qpat_x_assum `LENGTH removed = _` (assume_tac o SYM) >>
     gvs[stack_peek_contiguous]) >>
  `MEM x (lower ++ [top])` by (gvs[] >> ASM_SET_TAC[]) >>
  simp[do_swap_stack_result] >>
  qpat_x_assum `LENGTH removed = _` (assume_tac o SYM) >>
  simp[stack_pop_contiguous] >> gvs[]
QED

Theorem popmany_plan_retains_other:
  !to_pop ps x. MEM x ps.ps_stack /\ ~MEM x to_pop ==>
    MEM x (SND (popmany_plan to_pop ps)).ps_stack
Proof
  Cases >- simp[popmany_plan_def] >> rpt gen_tac >> strip_tac >>
  simp[popmany_plan_def, LET_THM] >> IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (pairarg_tac >> gvs[] >>
          mp_tac (Q.SPECL [`h::t`, `ps`, `x`] popmany_contiguous_retains_other) >>
          simp[] >> disch_then irule >>
          simp[SUBSET_DEF] >> rpt strip_tac >>
          rename1 `MEM y ps.ps_stack` >>
          `IS_SOME (stack_get_depth y ps.ps_stack)` by
            (gvs[EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
          Cases_on `stack_get_depth y ps.ps_stack` >> gvs[] >>
          drule stack_get_depth_props >> strip_tac >>
          gvs[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
      irule popmany_individual_retains_other >> simp[]) >>
  irule popmany_individual_retains_other >> simp[]
QED

(* Pointwise upper transport; unlike the reserve bound this needs no
   availability premise and charges a variable copy only when it is live. *)
Theorem emit_one_input_inventory_upper[local]:
  !opc nl op ps x.
    LIST_ELEM_COUNT x (SND (emit_one_input opc nl op ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) +
      (if x = op /\ (~is_var_operand op \/ MEM x (MAP Var nl)) then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op`
  >- (simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
           stack_push_def, rich_listTheory.SNOC_APPEND, elem_count_append,
           LIST_ELEM_COUNT_THM] >>
      rename1 `Lit c` >> Cases_on `x = Lit c` >> simp[LIST_ELEM_COUNT_DEF])
  >- (rename1 `Var v` >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
          Cases_on `MEM v nl` >> simp[] >>
          Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
          rename1 `stack_get_depth _ _ = SOME d` >>
          drule stack_get_depth_props >> strip_tac >>
          drule do_dup_stack_exact >> strip_tac >>
          CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
          Cases_on `do_dup d ps` >>
          drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
          gvs[elem_count_append, LIST_ELEM_COUNT_THM, MEM_MAP] >>
          Cases_on `x = Var v` >> simp[LIST_ELEM_COUNT_DEF]) >>
      rename1 `FLOOKUP ps.ps_spilled (Var v) = SOME off` >>
      `Var v IN FDOM ps.ps_spilled` by metis_tac[flookup_thm] >>
      simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
           do_restore_def] >>
      Cases_on `MEM v nl` >> simp[]
      >- (simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def] >>
          qmatch_goalsub_abbrev_tac `do_dup d restored` >>
          `d < LENGTH restored.ps_stack /\
           stack_peek d restored.ps_stack = Var v` by
            (gvs[Abbr `restored`, Abbr `d`, stack_get_depth_def,
                 stack_push_def, stack_peek_def, REVERSE_SNOC,
                 stack_find_def, rich_listTheory.SNOC_APPEND, EL_APPEND_EQN]) >>
          drule do_dup_stack_exact >> strip_tac >>
          CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
          Cases_on `do_dup d restored` >>
          drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
          gvs[Abbr `d`, Abbr `restored`, stack_push_def, rich_listTheory.SNOC_APPEND,
              elem_count_append, MEM_MAP] >>
          Cases_on `x = Var v` >> gvs[LIST_ELEM_COUNT_DEF]) >>
      simp[stack_push_def, rich_listTheory.SNOC_APPEND, elem_count_append] >>
      Cases_on `x = Var v` >> gvs[LIST_ELEM_COUNT_DEF]) >>
  Cases_on `opc = INVOKE` >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       stack_push_def, rich_listTheory.SNOC_APPEND, elem_count_append, LIST_ELEM_COUNT_THM] >>
  Cases_on `x = Label s` >> simp[LIST_ELEM_COUNT_DEF]
QED

Theorem emit_input_plan_variable_origins:
  !opc operands nl ps ops qs v.
    emit_input_plan opc operands nl ps = (ops,qs) /\
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
    MEM (Var v) operands
Proof
  gen_tac >> Induct >> rpt gen_tac
  >- simp[emit_input_plan_def] >>
  namedCases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` ["step_ops ps1"] >>
  namedCases_on `emit_input_plan opc operands nl ps1` ["rest_ops ps2"] >>
  simp[emit_input_plan_def] >> strip_tac >> gvs[] >>
  `MEM (Var v) ps1.ps_stack \/ Var v IN FDOM ps1.ps_spilled \/ MEM (Var v) operands` by
    metis_tac[] >>
  Cases_on `MEM (Var v) operands` >- simp[] >>
  qspecl_then [`opc`, `operand_vars operands ++ nl`, `h`, `ps`, `Var v`]
    mp_tac emit_one_input_inventory_upper >>
  gvs[] >>
  Cases_on `MEM (Var v) ps.ps_stack` >- simp[] >>
  Cases_on `Var v IN FDOM ps.ps_spilled` >- simp[] >>
  Cases_on `Var v = h` >- simp[] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var v IN FDOM ps1.ps_spilled` >> gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem emit_one_input_live_upper_acc[local]:
  !done rest opc nl h ps x.
    (LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars (h::rest) ++ nl)) then 1 else 0)) ==>
    LIST_ELEM_COUNT x (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_spilled
       then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ [h]) +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`opc`, `operand_vars rest ++ nl`, `h`, `ps`, `x`]
    assume_tac emit_one_input_inventory_upper >>
  Cases_on `x IN FDOM ps.ps_spilled` >>
  Cases_on `h` >> Cases_on `x` >>
  gvs[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def,
      venomInstTheory.operand_var_def, dfgDefsTheory.operand_var_def,
      stackPlanTypesTheory.is_var_operand_def,
      elem_count_append, MAP_APPEND, LIST_ELEM_COUNT_DEF, MEM_MAP] >>
  rpt IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem emit_input_plan_live_upper_acc[local]:
  !rest done opc nl ps iops qs x.
    (LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)) /\
    emit_input_plan opc rest nl ps = (iops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ rest) +
      (if MEM x (MAP Var nl) then 1 else 0)
Proof
  Induct_on `rest` >- simp[venomInstTheory.operand_vars_def,
                          dfgDefsTheory.operand_vars_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_one_input_live_upper_acc >>
  disch_then (qspec_then `opc` assume_tac) >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops, mid)` >>
  Cases_on `emit_input_plan opc rest nl mid` >>
  gvs[emit_input_plan_cons] >>
  first_x_assum drule >> disch_then drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem emit_input_plan_relevant_variable_upper:
  !opc operands nl ps iops qs v.
    MEM v (operand_vars operands ++ nl) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    emit_input_plan opc operands nl ps = (iops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) operands + (if MEM v nl then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack +
     (if Var v IN FDOM ps.ps_spilled then 1 else 0) <=
   LIST_ELEM_COUNT (Var v) [] +
     (if MEM (Var v) (MAP Var (operand_vars operands ++ nl)) then 1 else 0)` by
    gvs[MEM_MAP, LIST_ELEM_COUNT_THM] >>
  drule_all emit_input_plan_live_upper_acc >> simp[MEM_MAP]
QED

Theorem emit_input_plan_live_upper:
  !opc operands nl ps iops qs.
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    set ps.ps_stack UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (operand_vars operands ++ nl)) /\
    emit_input_plan opc operands nl ps = (iops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x operands + (if MEM x (MAP Var nl) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x [] +
    (if MEM x (MAP Var (operand_vars operands ++ nl)) then 1 else 0)` by
    (gen_tac >>
     `LIST_ELEM_COUNT x ps.ps_stack <= 1` by
       (`ALL_DISTINCT (FILTER (\y. y = x) ps.ps_stack)` by
          simp[FILTER_ALL_DISTINCT] >>
        `!y. MEM y (FILTER (\y. y = x) ps.ps_stack) ==> y = x` by
          simp[MEM_FILTER] >>
        simp[LIST_ELEM_COUNT_DEF] >>
        qmatch_goalsub_abbrev_tac `LENGTH filtered` >>
        qpat_x_assum `Abbrev _` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        Cases_on `filtered` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
     Cases_on `MEM x (MAP Var (operand_vars operands ++ nl))`
     >- (Cases_on `x IN FDOM ps.ps_spilled` >>
         gvs[DISJOINT_ALT, LIST_ELEM_COUNT_THM] >>
         `~MEM x ps.ps_stack` by metis_tac[] >>
         gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
     `~MEM x ps.ps_stack /\ x NOTIN FDOM ps.ps_spilled` by
       (gvs[SUBSET_DEF] >> metis_tac[]) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
  gen_tac >>
  qpat_x_assum `!x. _` (qspec_then `x` assume_tac) >>
  drule_all emit_input_plan_live_upper_acc >> simp[]
QED

Theorem reorder_plan_inventory_subset:
  !dfg pending ps ops qs base.
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    !x. MEM x qs.ps_stack \/ x IN FDOM qs.ps_spilled ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> irule plan_steps_reorder_inventory_subset >>
  qexistsl_tac [`base'`, `dfg`, `MAPi (\i op. (i,op)) pending`, `ops`, `qs`, `pending`] >>
  simp[GSYM reorder_plan_eq_plan_steps, EVERY_EL,
       indexedListsTheory.EL_MAPi, indexedListsTheory.LENGTH_MAPi]
QED

Theorem reorder_plan_materialised_live_upper:
  !dfg pending ps ops qs base live.
    (!x. MEM x pending ==> x NOTIN FDOM ps.ps_spilled) /\
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    (!x. MEM x pending ==> LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x pending + (if MEM x live then 1 else 0)) /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x pending + (if MEM x live then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reorder_plan_inventory_mono >> strip_tac >>
  `!x. MEM x pending ==> LIST_ELEM_COUNT x qs.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[reorder_plan_materialised_counts] >>
  `!x. MEM x qs.ps_stack \/ x IN FDOM qs.ps_spilled ==>
       MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled` by
    metis_tac[reorder_plan_inventory_subset] >>
  gen_tac >> Cases_on `MEM x pending`
  >- (`x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
      `x NOTIN FDOM qs.ps_spilled` by
        (drule_all reorder_plan_pending_not_spilled >>
         disch_then (qspec_then `dfg` mp_tac) >> simp[]) >>
      qpat_x_assum `!x. _ + _ <= LIST_ELEM_COUNT x pending + _` (qspec_then `x` mp_tac) >>
      simp[]) >>
  Cases_on `MEM x live`
  >- (qpat_x_assum `residual_budget_wf _ _ qs` mp_tac >>
      simp[residual_budget_wf_def] >> strip_tac >>
      Cases_on `x IN FDOM qs.ps_spilled` >>
      qpat_x_assum `!op. LIST_ELEM_COUNT op qs.ps_stack <= SUC _`
        (qspec_then `x` assume_tac) >>
      qpat_x_assum `!op. op IN FDOM _ ==> _` (qspec_then `x` assume_tac) >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  `LIST_ELEM_COUNT x ps.ps_stack = 0 /\ x NOTIN FDOM ps.ps_spilled` by
    (qpat_x_assum `!x. _ + _ <= LIST_ELEM_COUNT x pending + _` (qspec_then `x` mp_tac) >>
     Cases_on `x IN FDOM ps.ps_spilled` >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  `~MEM x qs.ps_stack /\ x NOTIN FDOM qs.ps_spilled` by
    (qpat_x_assum `!x. MEM x qs.ps_stack \/ _ ==> _`
       (qspec_then `x` mp_tac) >>
     simp[GSYM LIST_ELEM_COUNT_MEM]) >>
  gvs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem residual_budget_wf_empty_inventory:
  !spillbase ps. residual_budget_wf spillbase [] ps ==>
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `plan_state_residual_wf spillbase [] 0 ps` by
    (irule residual_budget_wf_to_residual >> simp[]) >>
  qspecl_then [`spillbase`, `[]`, `ps`] mp_tac plan_state_residual_wf_pop >>
  simp[stack_pop_def] >> metis_tac[]
QED

Theorem emit_reorder_plan_core_live_upper:
  !ps base operands selected opc nl dfg iops ps1 rops ps2.
    residual_budget_wf base [] ps /\ LENGTH operands <= 16 /\
    set ps.ps_stack UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (operand_vars operands ++ nl)) /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    !x. LIST_ELEM_COUNT x (stack_pop (LENGTH selected) ps2.ps_stack) +
      (if x IN FDOM ps2.ps_spilled then 1 else 0) <=
      (if MEM x (MAP Var nl) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> rename1 `residual_budget_wf spillbase [] ps` >>
  drule residual_budget_wf_empty_inventory >> strip_tac >>
  drule_all emit_input_plan_live_upper >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  `!x. MEM x operands ==> x NOTIN FDOM ps1.ps_spilled` by
    (gen_tac >> strip_tac >> Cases_on `is_var_operand x`
     >- metis_tac[emit_input_plan_vars_not_spilled] >>
     `~MEM x (MAP Var nl)` by
       (Cases_on `x` >> gvs[stackPlanTypesTheory.is_var_operand_def, MEM_MAP]) >>
     qpat_x_assum `!x. _ + _ <= LIST_ELEM_COUNT x operands + _`
       (qspec_then `x` mp_tac) >>
     first_x_assum (qspec_then `x` assume_tac) >>
     Cases_on `x IN FDOM ps1.ps_spilled` >> simp[] >> decide_tac) >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `residual_budget_wf spillbase selected ps1` by
    metis_tac[residual_budget_wf_perm] >>
  `!x. MEM x selected ==> x NOTIN FDOM ps1.ps_spilled` by
    metis_tac[sortingTheory.PERM_MEM_EQ] >>
  `!x. MEM x selected ==> LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x ps1.ps_stack` by
    metis_tac[] >>
  `!x. LIST_ELEM_COUNT x ps1.ps_stack +
    (if x IN FDOM ps1.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x selected + (if MEM x (MAP Var nl) then 1 else 0)` by
    metis_tac[] >>
  `LENGTH selected <= LENGTH ps1.ps_stack /\ LENGTH selected <= 16` by simp[] >>
  drule_all reorder_plan_materialised_live_upper >> strip_tac >>
  drule_all emit_reorder_plan_core_suffix >> strip_tac >>
  gen_tac >>
  qpat_x_assum `!x. _ + _ <= LIST_ELEM_COUNT x selected + _`
    (qspec_then `x` mp_tac) >>
  qpat_x_assum `ps2.ps_stack = _` (fn th => once_rewrite_tac[th]) >>
  simp[elem_count_append, stack_pop_def, TAKE_APPEND, TAKE_TAKE]
QED

Theorem emit_reorder_pop_marker_core_live_upper:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    set core UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (operand_vars operands ++ nl)) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf base [] (qs with ps_stack := rest) /\
      (!x. LIST_ELEM_COUNT x rest +
        (if x IN FDOM qs.ps_spilled then 1 else 0) <=
        (if MEM x (MAP Var nl) then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_reorder_pop_marker_execution >> strip_tac >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  `set (ps with ps_stack := core).ps_stack UNION
     FDOM (ps with ps_stack := core).ps_spilled SUBSET
       set (MAP Var (operand_vars operands ++ nl))` by gvs[] >>
  drule_all emit_reorder_plan_core_live_upper >> strip_tac >>
  `set [] SUBSET set nl` by simp[] >>
  `!v. MEM (Var v) operands \/ MEM v [] ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by simp[] >>
  drule_all emit_reorder_plan_core_protected_consumption >> strip_tac >>
  qpat_x_assum `qs = ps2 with ps_stack := _` kall_tac >>
  qexists_tac `stack_pop (LENGTH selected) cs2.ps_stack` >> gvs[]
QED

Theorem emit_input_plan_absent:
  !opc operands nl ps ops qs x.
    ~MEM x operands /\ ~MEM x ps.ps_stack /\ x NOTIN FDOM ps.ps_spilled /\
    emit_input_plan opc operands nl ps = (ops,qs) ==>
    ~MEM x qs.ps_stack /\ x NOTIN FDOM qs.ps_spilled
Proof
  Induct_on `operands` >- simp[emit_input_plan_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  `~MEM x mid.ps_stack /\ x NOTIN FDOM mid.ps_spilled` by
    (qspecl_then [`opc`, `operand_vars operands ++ nl`, `h`, `ps`, `x`]
       mp_tac emit_one_input_inventory_upper >>
     gvs[GSYM LIST_ELEM_COUNT_MEM] >>
     Cases_on `x IN FDOM mid.ps_spilled` >> simp[] >> decide_tac) >>
  gvs[emit_input_plan_cons] >> first_x_assum drule >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem emit_reorder_pop_marker_core_fresh:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs outputs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack /\
    EVERY (\v. ~MEM (Var v) operands /\ ~MEM (Var v) core /\
      Var v NOTIN FDOM ps.ps_spilled) outputs ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf base [] (qs with ps_stack := rest) /\
      EVERY (\v. ~MEM (Var v) rest /\ Var v NOTIN FDOM qs.ps_spilled) outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_reorder_pop_marker_execution >> strip_tac >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  `set [] SUBSET set nl` by simp[] >>
  `!v. MEM (Var v) operands \/ MEM v [] ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by simp[] >>
  drule_all emit_reorder_plan_core_protected_consumption >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op (ps with ps_stack := core).ps_stack \/
      op IN FDOM (ps with ps_stack := core).ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  `residual_budget_wf base' selected cs1` by
    metis_tac[residual_budget_wf_perm] >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LENGTH selected <= LENGTH cs1.ps_stack /\ LENGTH selected <= 16` by simp[] >>
  `!x. MEM x cs2.ps_stack \/ x IN FDOM cs2.ps_spilled ==>
    MEM x cs1.ps_stack \/ x IN FDOM cs1.ps_spilled` by
    metis_tac[reorder_plan_inventory_subset] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  `~MEM (Var v) cs1.ps_stack /\ Var v NOTIN FDOM cs1.ps_spilled` by
    (irule emit_input_plan_absent >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `~MEM (Var v) cs2.ps_stack /\ Var v NOTIN FDOM cs2.ps_spilled` by metis_tac[] >>
  gvs[stack_pop_def] >> metis_tac[MEM_TAKE]
QED

(* Diagnostic only: malformed short storage reaches native bulk swap.
   This equation does not assign a value to out-of-range EL reads. *)
Theorem reorder_one_short_bulk_branch[local]:
  !dfg ps x. ps.ps_stack = [Var x] ==>
    reorder_one dfg (REPLICATE 18 (Var x)) 0 (Var x) ps = do_swap 17 ps
Proof
  rpt strip_tac >>
  simp[reorder_one_def, stack_get_unfixed_depth_def, stack_get_depth_def,
       stack_find_def, do_swap_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >> simp[]
QED

Theorem emit_reorder_pop_marker_variable_origins:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/ MEM (Var v) operands
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_reorder_pop_marker_execution >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op (ps with ps_stack := core).ps_stack \/
      op IN FDOM (ps with ps_stack := core).ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def,
                 MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  `residual_budget_wf base' selected cs1` by
    metis_tac[residual_budget_wf_perm] >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LENGTH selected <= LENGTH cs1.ps_stack /\ LENGTH selected <= 16` by simp[] >>
  `!x. MEM x cs2.ps_stack \/ x IN FDOM cs2.ps_spilled ==>
    MEM x cs1.ps_stack \/ x IN FDOM cs1.ps_spilled` by
    metis_tac[reorder_plan_inventory_subset] >>
  rpt strip_tac >>
  `MEM (Var v) cs2.ps_stack \/ Var v IN FDOM cs2.ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def, stack_pop_def] >>
     metis_tac[MEM_TAKE]) >>
  `MEM (Var v) cs1.ps_stack \/ Var v IN FDOM cs1.ps_spilled` by metis_tac[] >>
  drule emit_input_plan_variable_origins >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  gvs[] >> metis_tac[]
QED

(* Exact copy from fnAliasStep.foldl_plan_inventory_subset; owner-approved
   independent copy avoids fnAliasStep -> fnAliasInv -> fnPlanLineage. *)
Theorem foldl_plan_inventory_subset[local]:
  !(f : 'a # plan_state -> 'b -> 'a # plan_state) items acc.
    (!acc x at.
       MEM at (SND (f acc x)).ps_stack \/ at IN FDOM (SND (f acc x)).ps_spilled ==>
       MEM at (SND acc).ps_stack \/ at IN FDOM (SND acc).ps_spilled) ==>
    !at. MEM at (SND (FOLDL f acc items)).ps_stack \/
         at IN FDOM (SND (FOLDL f acc items)).ps_spilled ==>
         MEM at (SND acc).ps_stack \/ at IN FDOM (SND acc).ps_spilled
Proof
  ntac 2 gen_tac >> Induct_on `items` >> simp[] >> metis_tac[]
QED

(* Exact copy from fnAliasStep.popmany_individual_inventory_subset. *)
Theorem popmany_individual_inventory_subset:
  !to_pop ps ops ps'.
    popmany_individual to_pop ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f acc0 sorted` >>
  `ps' = SND (FOLDL f acc0 sorted) /\ ps = SND acc0` by
    gvs[Abbr `acc0`] >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  match_mp_tac foldl_plan_inventory_subset >>
  simp[Abbr `f`, pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  Cases_on `stack_get_depth x p_2.ps_stack` >> simp[] >>
  rename1 `stack_get_depth x p_2.ps_stack = SOME dist` >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `dist = 0` >> simp[]
  >- (simp[stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  pairarg_tac >> simp[stack_pop_def] >> strip_tac >>
  `MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled` by
    metis_tac[MEM_TAKE] >>
  metis_tac[do_swap_inventory_subset]
QED

(* Exact copy from fnAliasStep.popmany_plan_inventory_subset. *)
Theorem popmany_plan_inventory_subset:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Cases
  >- (simp[popmany_plan_def] >> rpt strip_tac >> gvs[]) >>
  simp[popmany_plan_def] >> rpt gen_tac >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_inventory_subset] >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_inventory_subset] >>
  qmatch_asmsub_abbrev_tac `is_contiguous_top depths` >>
  `!v. IS_SOME (stack_get_depth v ps.ps_stack) ==>
       THE (stack_get_depth v ps.ps_stack) < LENGTH ps.ps_stack` by
    (rpt strip_tac >> Cases_on `stack_get_depth v ps.ps_stack` >> gvs[] >>
     drule stack_get_depth_props >> simp[]) >>
  `!d. MEM d depths ==> d < LENGTH ps.ps_stack` by
    (simp[Abbr `depths`, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (SUC (LENGTH t)) depths` by
    (`LENGTH depths = SUC (LENGTH t)` by simp[Abbr `depths`] >>
     `MEM (SUC (LENGTH t)) (QSORT (\a b. a <= b) depths)` by
       gvs[is_contiguous_top_def, LET_THM, MEM_GENLIST] >>
     metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]) >>
  `SUC (LENGTH t) < LENGTH ps.ps_stack` by metis_tac[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[stack_pop_def] >>
  rpt strip_tac >>
  `MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled` by
    metis_tac[MEM_TAKE] >>
  metis_tac[do_swap_inventory_subset]
QED

(* Exact copy from fnAliasStep.optimistic_swap_plan_inventory_subset. *)
Theorem optimistic_swap_plan_inventory_subset:
  !dfg inst nl nt ps ops ps'.
    optimistic_swap_plan dfg inst nl nt ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  strip_tac >> gen_tac >> disch_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule stack_get_depth_props >> strip_tac >>
  metis_tac[do_swap_inventory_subset]
QED

(* Exact copy from fnAliasStep.release_dead_spills_inventory_subset. *)
Theorem release_dead_spills_inventory_subset:
  !nl ps at.
    MEM at (release_dead_spills nl ps).ps_stack \/
    at IN FDOM (release_dead_spills nl ps).ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  `!(f : plan_state -> operand # num -> plan_state) l ps.
     (!ps x. (f ps x).ps_stack = ps.ps_stack /\
             FDOM (f ps x).ps_spilled SUBSET FDOM ps.ps_spilled) ==>
     (FOLDL f ps l).ps_stack = ps.ps_stack /\
     FDOM (FOLDL f ps l).ps_spilled SUBSET FDOM ps.ps_spilled` by
    (ntac 2 gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
     metis_tac[SUBSET_TRANS]) >>
  rpt gen_tac >> simp[release_dead_spills_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL f ps dead` >>
  `(FOLDL f ps dead).ps_stack = ps.ps_stack /\
   FDOM (FOLDL f ps dead).ps_spilled SUBSET FDOM ps.ps_spilled` by
    (first_x_assum irule >>
     simp[Abbr `f`, pairTheory.FORALL_PROD, SUBSET_DEF]) >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

(* Exact copies from fnAliasStep; its lineage dependency prevents import. *)
Theorem restore_spilled_plan_inventory_subset:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_restore_inventory_subset]
QED

Theorem do_restore_inventory_count[local]:
  !op ps ops ps'.
    do_restore op ps = (ops,ps') ==>
    (!x. LIST_ELEM_COUNT x ps'.ps_stack +
           (if x IN FDOM ps'.ps_spilled then 1 else 0) =
         LIST_ELEM_COUNT x ps.ps_stack +
           (if x IN FDOM ps.ps_spilled then 1 else 0)) /\
    op NOTIN FDOM ps'.ps_spilled /\
    FDOM ps'.ps_spilled SUBSET FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
  >- (strip_tac >> gvs[FLOOKUP_DEF]) >>
  strip_tac >> gvs[stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_DEF,
                   FILTER_APPEND, FLOOKUP_DEF, SUBSET_DEF] >>
  rw[] >> gvs[]
QED

Theorem restore_spilled_plan_inventory_count:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') ==>
    (!x. LIST_ELEM_COUNT x ps'.ps_stack +
           (if x IN FDOM ps'.ps_spilled then 1 else 0) =
         LIST_ELEM_COUNT x ps.ps_stack +
           (if x IN FDOM ps.ps_spilled then 1 else 0)) /\
    (!x. MEM x targets ==> x NOTIN FDOM ps'.ps_spilled) /\
    FDOM ps'.ps_spilled SUBSET FDOM ps.ps_spilled
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule do_restore_inventory_count >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> gvs[SUBSET_DEF] >> metis_tac[])
  >> metis_tac[SUBSET_TRANS]
QED

Theorem restore_spilled_plan_length_floor:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') /\
    pending_inventory_wf targets ps ==>
    LENGTH targets <= LENGTH ps'.ps_stack
Proof
  rpt strip_tac >> drule restore_spilled_plan_inventory_count >> strip_tac >>
  irule list_elem_count_dom_length >> gen_tac >>
  Cases_on `MEM x targets`
  >- (`LIST_ELEM_COUNT x targets <=
       LIST_ELEM_COUNT x ps.ps_stack +
         (if x IN FDOM ps.ps_spilled then 1 else 0)` by
        fs[pending_inventory_wf_def] >>
      `x NOTIN FDOM ps'.ps_spilled` by metis_tac[] >>
      qpat_x_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  `LIST_ELEM_COUNT x targets = 0` by
    (CCONTR_TAC >>
     `LIST_ELEM_COUNT x targets > 0` by decide_tac >>
     metis_tac[LIST_ELEM_COUNT_MEM]) >>
  simp[]
QED

(* Exact copies from deepResidualBudget: unbounded target windows still
   require a native length floor. Do not import its frame simulation chain. *)
Theorem select_spill_candidate_props:
  !stk forbidden dist target_len cand.
    select_spill_candidate stk forbidden dist target_len = SOME cand ==>
    target_len <= cand /\ ~MEM (stack_peek cand stk) forbidden /\
    is_var_operand (stack_peek cand stk)
Proof
  rpt gen_tac >> simp[select_spill_candidate_def, LET_THM] >>
  strip_tac >> imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem do_spill_at_length[local]:
  !d ps.
    d < LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at d ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[stack_pop_def] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[stack_pop_def]
QED

Theorem reduce_depth_plan_target_len_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') /\
    target_len <= LENGTH ps.ps_stack ==>
    target_len <= LENGTH ps'.ps_stack
Proof
  Induct >- simp[reduce_depth_plan_def] >>
  rpt gen_tac >> simp[Once reduce_depth_plan_def, LET_THM] >>
  Cases_on `f + 1 < target_len` >> simp[] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `x <= 16` >> simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  pairarg_tac >> simp[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand < LENGTH ps.ps_stack` by metis_tac[planWfTheory.select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by
    (qspecl_then [`cand`, `ps`] mp_tac do_spill_at_length >> simp[]) >>
  `target_len <= LENGTH ps1.ps_stack` by decide_tac >>
  metis_tac[]
QED

Theorem reorder_restore_inventory_subset_nb[local]:
  !op f n ps ops ps'.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,ps') ==>
    LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `do_restore _ _ = _` mp_tac >>
      simp[do_restore_def] >> strip_tac >> gvs[stack_push_def]) >>
  metis_tac[do_restore_inventory_subset]
QED

Theorem stack_poke_mem_subset_nb:
  !d op stk at. MEM at (stack_poke d op stk) ==> at = op \/ MEM at stk
Proof
  simp[stack_poke_def, MEM_LUPDATE] >> metis_tac[EL_MEM]
QED

Theorem reorder_reduce_inventory_subset_nb[local]:
  !(dist:num) tops op f ps ops ps'.
    (if dist > 16 then
       reduce_depth_plan (LENGTH ps.ps_stack) tops op f (LENGTH tops) ps
     else ([],ps)) = (ops,ps') ==>
    LENGTH tops <= LENGTH ps.ps_stack ==>
    LENGTH tops <= LENGTH ps'.ps_stack /\
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `dist > 16` >> simp[] >> ntac 2 strip_tac >> gvs[] >>
  conj_tac
  >- (drule reduce_depth_plan_target_len_floor >> fs[]) >>
  metis_tac[reduce_depth_plan_inventory_subset]
QED

(* Exact copy from reorderSim.stack_swap_mem_subset (local there).
   Shared by the shallow and length-floor planner interfaces. *)
Theorem stack_swap_mem_subset:
  !d stk at. MEM at (stack_swap d stk) ==> MEM at stk
Proof
  rpt gen_tac >> Cases_on `stk = []` >- simp[stack_swap_def, LUPDATE_def] >>
  `LENGTH stk - 1 < LENGTH stk /\
   LENGTH stk - (d + 1) < LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  `MEM (EL (LENGTH stk - 1) stk) stk /\
   MEM (EL (LENGTH stk - (d + 1)) stk) stk` by
    (conj_tac >> irule EL_MEM >> decide_tac) >>
  simp[stack_swap_def, LET_THM] >> strip_tac >>
  fs[MEM_LUPDATE, EL_LUPDATE] >> gvs[] >> metis_tac[EL_MEM]
QED

Theorem do_swap_safe_inventory_subset:
  !d ps ops qs.
    (d <= 16 \/ d < LENGTH ps.ps_stack) /\
    do_swap d ps = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `d <= 16`
  >- (qpat_x_assum `do_swap _ _ = _` mp_tac >>
      simp[do_swap_def] >> Cases_on `d = 0` >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[stack_swap_mem_subset]) >>
  metis_tac[reorderSimTheory.do_swap_inventory_subset]
QED

Theorem reorder_one_safe_inventory_subset:
  !dfg tops idx op ps ops qs.
    ((idx < LENGTH tops /\ LENGTH tops <= LENGTH ps.ps_stack) \/
     LENGTH tops - 1 - idx <= 16) /\
    reorder_one dfg tops idx op ps = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gnvs[] >>
  `LENGTH ps.ps_stack <= LENGTH ps1.ps_stack /\
   !at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule reorder_restore_inventory_subset_nb >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
        MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (Cases_on `dist > 16` >> gvs[] >>
     metis_tac[reduce_depth_plan_inventory_subset]) >>
  `~(LENGTH tops - (idx + 1) <= 16) ==>
   LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` by
    (Cases_on `LENGTH tops - (idx + 1) <= 16` >> simp[] >>
     `idx < LENGTH tops /\ LENGTH tops <= LENGTH ps1.ps_stack` by decide_tac >>
     `LENGTH tops <= LENGTH ps2.ps_stack` by
       (drule reorder_reduce_inventory_subset_nb >> simp[]) >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `MEM op ps2.ps_stack` by metis_tac[stack_peek_mem] >>
  Cases_on `dist' = LENGTH tops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack)` >> simp[] >>
  all_tac >>~- ([`_ /\ (ps2 with ps_stack := _) = qs ==> _`],
    `MEM (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack) ps2.ps_stack` by
      (irule stack_peek_mem >> decide_tac) >>
    strip_tac >> gvs[] >> rpt strip_tac >> metis_tac[stack_poke_mem_subset_nb]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gnvs[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  `!at. MEM at ps3.ps_stack \/ at IN FDOM ps3.ps_spilled ==>
        MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (rpt strip_tac >> irule reorderSimTheory.do_swap_inventory_subset >>
     qexistsl [`dist'`, `swap1_ops`] >> simp[]) >>
  `!at. MEM at ps4.ps_stack \/ at IN FDOM ps4.ps_spilled ==>
        MEM at ps3.ps_stack \/ at IN FDOM ps3.ps_spilled` by
    (rpt strip_tac >> irule do_swap_safe_inventory_subset >>
     qexistsl [`LENGTH tops - (idx + 1)`, `swap2_ops`] >> simp[]) >>
  metis_tac[]
QED

Theorem reorder_one_inventory_subset_nb:
  !dfg tops idx op ps ops ps'.
    idx < LENGTH tops /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_one dfg tops idx op ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  metis_tac[reorder_one_safe_inventory_subset]
QED

(* Exact copies from fnAliasStep, completing the unbounded reorder interface. *)
Theorem reorder_restore_length_mono[local]:
  !op f n ps ops ps'.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,ps') ==>
    LENGTH ps.ps_stack <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `do_restore _ _ = _` mp_tac >>
  simp[do_restore_def] >> strip_tac >> gvs[stack_push_def]
QED

Theorem reorder_one_length_floor:
  !dfg tops idx op ps ops ps'.
    idx < LENGTH tops /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_one dfg tops idx op ps = (ops,ps') ==>
    LENGTH tops <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gvs[] >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    (drule reorder_restore_length_mono >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `LENGTH tops <= LENGTH ps2.ps_stack` by
    (Cases_on `dist > 16` >> gvs[] >>
     drule reduce_depth_plan_target_len_floor >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH tops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[stack_poke_def]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac planWfTheory.do_swap_length >>
     asm_simp_tac (srw_ss()) []) >>
  strip_tac >> gvs[] >>
  `LENGTH tops - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  qspecl_then [`LENGTH tops - (idx + 1)`, `ps3`] mp_tac planWfTheory.do_swap_length >>
  asm_simp_tac (srw_ss()) []
QED

Theorem plan_steps_reorder_inventory_subset_nb[local]:
  !items dfg tops ps ops ps'.
    EVERY (\(idx,op). idx < LENGTH tops) items /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg tops idx op ps) items ps =
      (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg tops idx op ps = (step_ops,ps1)` >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_length_floor] >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    metis_tac[reorder_one_inventory_subset_nb] >>
  rpt strip_tac >>
  `MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (first_x_assum (qspecl_then [`dfg`, `tops`, `ps1`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reorder_plan_inventory_subset_nb:
  !dfg tops ps ops ps'.
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_plan dfg tops ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH tops) (MAPi (\i op. (i,op)) tops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  metis_tac[plan_steps_reorder_inventory_subset_nb]
QED

(* A resource-safe join boundary; pending inventory is a caller obligation. *)
Theorem restore_reorder_inventory_subset:
  !targets ps restore_ops mid dfg reorder_ops qs.
    pending_inventory_wf targets ps /\
    restore_spilled_plan targets ps = (restore_ops,mid) /\
    reorder_plan dfg targets mid = (reorder_ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    metis_tac[restore_spilled_plan_length_floor] >>
  metis_tac[reorder_plan_inventory_subset_nb,
            restore_spilled_plan_inventory_subset]
QED

(* Native JMP call site: when join_target_ops liveness fn lbl inst = SOME
   targets, the input to restore_spilled_plan is ps1 from
   emit_input_plan JMP (compute_operands inst) next ps = (input_ops,ps1).
   For inst_operands = [Label target], compute_operands is [] and ps1 = ps;
   targets = MAP Var (input_vars_from lbl target_bb.bb_instructions
                        (live_vars_at liveness target 0)), where
   lookup_block target fn.fn_blocks = SOME target_bb.
   The reachable JMP producer must establish pending_inventory_wf targets ps1.
   Neither successful generation nor join_reached supplies that premise.
   This boundary proves inventory inclusion only, not dominance support. *)

Theorem restore_spilled_plan_length_exact:
  !targets ps ops mid.
    restore_spilled_plan targets ps = (ops,mid) ==>
    LENGTH mid.ps_stack = LENGTH ps.ps_stack +
      CARD (set targets INTER FDOM ps.ps_spilled)
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled h` >> simp[]
  >- (pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      `h NOTIN FDOM ps.ps_spilled` by gvs[FLOOKUP_DEF] >>
      simp[INSERT_INTER]) >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[stack_push_def, INSERT_INTER] >>
  `h IN FDOM ps.ps_spilled` by gvs[FLOOKUP_DEF] >>
  `h INSERT (set targets INTER FDOM ps.ps_spilled) =
   h INSERT (set targets INTER (FDOM ps.ps_spilled DELETE h))` by SET_TAC[] >>
  simp[CARD_INSERT]
QED

Theorem restore_reorder_scalar_inventory_subset:
  !targets ps rops mid dfg ops qs.
    LENGTH targets <= LENGTH ps.ps_stack +
      CARD (set targets INTER FDOM ps.ps_spilled) /\
    restore_spilled_plan targets ps = (rops,mid) /\
    reorder_plan dfg targets mid = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    metis_tac[restore_spilled_plan_length_exact] >>
  metis_tac[reorder_plan_inventory_subset_nb,
            restore_spilled_plan_inventory_subset]
QED
Theorem reorder_one_shallow_inventory_subset:
  !dfg tops idx op ps ops qs.
    LENGTH tops - 1 - idx <= 16 /\
    reorder_one dfg tops idx op ps = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  metis_tac[reorder_one_safe_inventory_subset]
QED

Theorem plan_steps_reorder_shallow_inventory_subset[local]:
  !items dfg tops ps ops qs.
    LENGTH tops <= 17 /\
    plan_steps (\(idx,op) ps. reorder_one dfg tops idx op ps) items ps =
      (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg tops idx op ps = (step_ops,ps1)` >>
  `LENGTH tops - 1 - idx <= 16` by decide_tac >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    metis_tac[reorder_one_shallow_inventory_subset] >>
  rpt strip_tac >>
  `MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (first_x_assum (qspecl_then [`dfg`, `tops`, `ps1`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reorder_plan_shallow_inventory_subset:
  !dfg tops ps ops qs.
    LENGTH tops <= 17 /\ reorder_plan dfg tops ps = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  metis_tac[plan_steps_reorder_shallow_inventory_subset]
QED

Theorem restore_reorder_shallow_inventory_subset:
  !targets ps restore_ops mid dfg reorder_ops qs.
    LENGTH targets <= 17 /\
    restore_spilled_plan targets ps = (restore_ops,mid) /\
    reorder_plan dfg targets mid = (reorder_ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  metis_tac[reorder_plan_shallow_inventory_subset,
            restore_spilled_plan_inventory_subset]
QED

Theorem select_spill_candidate_target_ceiling[local]:
  !stk forbidden dist n.
    0 < n /\ LENGTH stk <= n ==>
    select_spill_candidate stk forbidden dist n = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `select_spill_candidate stk forbidden dist n` >> simp[] >>
  drule select_spill_candidate_props >> strip_tac >>
  qpat_x_assum `select_spill_candidate _ _ _ _ = _` mp_tac >>
  simp[select_spill_candidate_def, LET_THM] >> strip_tac >>
  imp_res_tac FIND_SOME_MEM >> gvs[MEM_GENLIST] >>
  gvs[arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem reduce_depth_plan_target_ceiling[local]:
  !fuel forbidden op f n ps.
    0 < n /\ LENGTH ps.ps_stack <= n ==>
    reduce_depth_plan fuel forbidden op f n ps = ([],ps)
Proof
  rpt gen_tac >> Cases_on `fuel` >> simp[reduce_depth_plan_def] >> strip_tac >>
  simp[select_spill_candidate_target_ceiling] >>
  Cases_on `f + 1 < n` >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[]
QED

Theorem do_swap_target_ceiling:
  !d ps ops qs n.
    LENGTH ps.ps_stack <= n /\ d < n /\ do_swap d ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= n /\ qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do_swap _ _ = _` mp_tac >> simp[do_swap_def, LET_THM] >>
  Cases_on `d = 0` >> simp[] >- (strip_tac >> gvs[]) >>
  Cases_on `d <= 16` >> simp[] >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem reorder_one_target_ceiling:
  !dfg targets idx op ps ops qs.
    idx < LENGTH targets /\ MEM op targets /\
    LENGTH ps.ps_stack <= LENGTH targets /\
    DISJOINT (set targets) (FDOM ps.ps_spilled) /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= LENGTH targets /\ qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ps.ps_spilled op = NONE` by
    (simp[FLOOKUP_DEF] >> fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH targets - (idx + 1)) (LENGTH targets) ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  `0 < LENGTH targets` by decide_tac >>
  simp[reduce_depth_plan_target_ceiling] >>
  Cases_on `x = LENGTH targets - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH targets - (idx + 1) < LENGTH ps.ps_stack` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >> simp[] >>
  all_tac >>~- ([`_ /\ (ps with ps_stack := _) = qs ==> _`],
    strip_tac >> gvs[stack_poke_def]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >> gvs[] >>
  `x < LENGTH targets /\ LENGTH targets - (idx + 1) < LENGTH targets` by decide_tac >>
  `LENGTH ps3.ps_stack <= LENGTH targets /\ ps3.ps_spilled = ps.ps_spilled` by
    (irule do_swap_target_ceiling >> simp[] >> qexistsl [`x`, `swap1_ops`] >> simp[]) >>
  `LENGTH ps4.ps_stack <= LENGTH targets /\ ps4.ps_spilled = ps3.ps_spilled` by
    (irule do_swap_target_ceiling >> simp[] >>
     qexistsl [`LENGTH targets - (idx + 1)`, `swap2_ops`] >> simp[]) >> simp[]
QED

Theorem plan_steps_reorder_target_ceiling[local]:
  !items dfg targets ps ops qs.
    EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets) items /\
    LENGTH ps.ps_stack <= LENGTH targets /\
    DISJOINT (set targets) (FDOM ps.ps_spilled) /\
    plan_steps (\(idx,op) ps. reorder_one dfg targets idx op ps) items ps =
      (ops,qs) ==>
    LENGTH qs.ps_stack <= LENGTH targets /\ qs.ps_spilled = ps.ps_spilled
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg targets idx op ps = (step_ops,ps1)` >>
  `LENGTH ps1.ps_stack <= LENGTH targets /\ ps1.ps_spilled = ps.ps_spilled` by
    metis_tac[reorder_one_target_ceiling] >>
  first_x_assum (qspecl_then [`dfg`, `targets`, `ps1`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem reorder_plan_target_ceiling:
  !dfg targets ps ops qs.
    LENGTH ps.ps_stack <= LENGTH targets /\
    DISJOINT (set targets) (FDOM ps.ps_spilled) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= LENGTH targets /\ qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets)
     (MAPi (\i op. (i,op)) targets)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[EL_MEM]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  metis_tac[plan_steps_reorder_target_ceiling]
QED

Theorem restore_reorder_success_inventory_subset:
  !targets ps rops mid dfg ops qs.
    (!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    restore_spilled_plan targets ps = (rops,mid) /\
    reorder_plan dfg targets mid = (ops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH targets <= LENGTH mid.ps_stack`
  >- metis_tac[reorder_plan_inventory_subset_nb,
               restore_spilled_plan_inventory_subset] >>
  `FDOM mid.ps_spilled = FDOM ps.ps_spilled DIFF set targets` by
    (qspecl_then [`targets`, `ps`] mp_tac restore_spilled_plan_domain >> simp[]) >>
  `DISJOINT (set targets) (FDOM mid.ps_spilled)` by ASM_SET_TAC[] >>
  `LENGTH mid.ps_stack <= LENGTH targets` by decide_tac >>
  `LENGTH qs.ps_stack <= LENGTH targets /\ qs.ps_spilled = mid.ps_spilled` by
    metis_tac[reorder_plan_target_ceiling] >>
  `LENGTH qs.ps_stack - LENGTH targets = 0` by decide_tac >>
  `qs.ps_stack = targets` by
    (qpat_x_assum `stack_pop _ _ ++ _ = _` mp_tac >>
     simp[stack_pop_def]) >>
  gvs[] >> metis_tac[]
QED

(* Exact copy from fnFrameBoundaryGenRet.release_dead_spills_stack;
   importing that frame-level theory would violate planner leaf layering. *)
Theorem release_dead_spills_stack:
  (release_dead_spills nl ps).ps_stack = ps.ps_stack
Proof
  simp[release_dead_spills_def] >>
  qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v nl | Label v => T)
    (fmap_to_alist ps.ps_spilled)`, `xs`) >>
  qid_spec_tac `ps` >> Induct_on `xs` >> simp[] >>
  Cases_on `h` >> simp[]
QED

Theorem generate_inst_plan_jmp_inventory_subset:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    (!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs)
    ==> !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
             MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rOps,psR)` >>
  Cases_on `reorder_plan dfg targets psR` >> simp[stack_pop_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `join_reached _ _ _ _ _` mp_tac >>
  simp[join_reached_def, generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
       release_dead_spills_stack] >>
  strip_tac >> gvs[stack_pop_def] >>
  `!at. MEM at r.ps_stack \/ at IN FDOM r.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> irule restore_reorder_success_inventory_subset >>
     goal_assum (drule_at Any) >> simp[stack_pop_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[release_dead_spills_inventory_subset]
QED

Theorem generate_inst_plan_jmp_variable_support:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs P.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    (!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==> P v)
    ==> !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==> P v
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (irule generate_inst_plan_jmp_inventory_subset >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

(* Pointwise resource accounting permits stale/dead stack--spill overlap. *)
Theorem do_spill_at_resource_nonincrease:
  !d ps ops qs x.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_spill_at_stack_count >>
  disch_then (qspec_then `x` assume_tac) >>
  drule_all do_spill_at_spilled_update >> strip_tac >>
  Cases_on `x = stack_peek d ps.ps_stack` >>
  Cases_on `x IN FDOM ps.ps_spilled` >>
  gvs[FDOM_FUPDATE, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem reduce_depth_plan_resource_nonincrease:
  !fuel pending target f n ps ops qs x.
    reduce_depth_plan fuel pending target f n ps = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target f n ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < n` >> gvs[] >>
  Cases_on `x' <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x' n` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[planWfTheory.select_spill_candidate_bound] >>
  drule_all do_spill_at_resource_nonincrease >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `reduce_depth_plan fuel pending target f n ps1` >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `x` assume_tac) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem reorder_restore_resource[local]:
  !op f n ps ops qs x.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >>
  drule do_restore_inventory_count >> simp[]
QED

Theorem reorder_one_resource_nonincrease:
  !dfg pending idx op ps ops qs x.
    idx < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_one dfg pending idx op ps = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  strip_tac >> qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gnvs[] >>
  `LIST_ELEM_COUNT x ps1.ps_stack +
    (if x IN FDOM ps1.ps_spilled then 1 else 0) =
   LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled then 1 else 0)` by
    (drule_all reorder_restore_resource >> simp[]) >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule reorder_restore_length_mono >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `LENGTH pending <= LENGTH ps2.ps_stack /\
   LIST_ELEM_COUNT x ps2.ps_stack +
    (if x IN FDOM ps2.ps_spilled then 1 else 0) <=
   LIST_ELEM_COUNT x ps1.ps_stack +
    (if x IN FDOM ps1.ps_spilled then 1 else 0)` by
    (Cases_on `dist > 16` >> gvs[] >>
     conj_tac
     >- (drule reduce_depth_plan_target_len_floor >> simp[]) >>
     drule reduce_depth_plan_resource_nonincrease >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> simp[] >>
      `LIST_ELEM_COUNT x
         (stack_poke (LENGTH pending - (idx + 1)) op
           (stack_poke dist' (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
             ps2.ps_stack)) = LIST_ELEM_COUNT x ps2.ps_stack` by
        (qpat_assum `stack_peek dist' ps2.ps_stack = op`
           (fn th => once_rewrite_tac[GSYM th]) >>
         irule stack_poke_exchange_multiplicity >> simp[]) >>
      gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (drule planWfTheory.do_swap_length >> simp[]) >>
  `LIST_ELEM_COUNT x ps3.ps_stack = LIST_ELEM_COUNT x ps2.ps_stack` by
    (drule do_swap_multiplicity >> simp[]) >>
  `LIST_ELEM_COUNT x ps4.ps_stack = LIST_ELEM_COUNT x ps3.ps_stack` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`, `x`]
       mp_tac do_swap_multiplicity >> simp[]) >>
  `ps3.ps_spilled = ps2.ps_spilled /\ ps4.ps_spilled = ps3.ps_spilled` by
    (conj_tac
     >- (qspec_then `dist'` (qspec_then `ps2` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
     qspec_then `LENGTH pending - (idx + 1)`
       (qspec_then `ps3` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
  gvs[]
QED

Theorem plan_steps_reorder_resource_nonincrease:
  !items dfg pending ps ops qs x.
    EVERY (\(idx,op). idx < LENGTH pending) items /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps =
      (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg pending idx op ps = (step_ops,ps1)` >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_length_floor] >>
  `LIST_ELEM_COUNT x ps1.ps_stack +
    (if x IN FDOM ps1.ps_spilled then 1 else 0) <=
   LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled then 1 else 0)` by
    metis_tac[reorder_one_resource_nonincrease] >>
  first_x_assum drule >> disch_then drule_all >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem reorder_plan_resource_nonincrease:
  !dfg pending ps ops qs x.
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  irule plan_steps_reorder_resource_nonincrease >>
  qexistsl [`dfg`, `MAPi (\i op. (i,op)) pending`, `ops`, `pending`] >>
  simp[GSYM reorder_plan_eq_plan_steps, EVERY_EL,
       indexedListsTheory.EL_MAPi, indexedListsTheory.LENGTH_MAPi] >>
  metis_tac[EL_MEM]
QED

Theorem emit_reorder_pop_next_live_upper:
  !opc operands selected nl dfg ps iops ps1 rops ps2.
    LENGTH operands <= 16 /\ PERM operands selected /\
    (!v. MEM v (operand_vars operands ++ nl) ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    !v. MEM v nl ==>
      LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) +
        (if Var v IN FDOM ps2.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LENGTH selected <= 16 /\ LENGTH selected <= LENGTH ps1.ps_stack` by simp[] >>
  `!x. MEM x selected ==>
    LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x ps1.ps_stack` by metis_tac[] >>
  drule_all reorder_plan_bounded_materialised_suffix >> strip_tac >>
  gen_tac >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) ps1.ps_stack +
    (if Var v IN FDOM ps1.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) selected + 1` by
    (drule_at (Pat `emit_input_plan _ _ _ _ = _`)
       emit_input_plan_relevant_variable_upper >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `LIST_ELEM_COUNT (Var v) ps2.ps_stack +
    (if Var v IN FDOM ps2.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) selected + 1` by
    (Cases_on `MEM (Var v) selected`
     >- (`MEM (Var v) operands` by metis_tac[sortingTheory.PERM_MEM_EQ] >>
         `Var v NOTIN FDOM ps1.ps_spilled` by
           (drule_at (Pat `emit_input_plan _ _ _ _ = _`)
              emit_input_plan_vars_not_spilled >>
            simp[stackPlanTypesTheory.is_var_operand_def]) >>
         `Var v NOTIN FDOM ps2.ps_spilled` by
           (qspecl_then [`dfg`, `selected`, `ps1`, `Var v`]
              mp_tac reorder_plan_pending_not_spilled >> simp[]) >>
         `LIST_ELEM_COUNT (Var v) ps2.ps_stack =
          LIST_ELEM_COUNT (Var v) ps1.ps_stack` by
           metis_tac[reorder_plan_materialised_counts] >> gvs[]) >>
     drule_all reorder_plan_resource_nonincrease >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `ps2.ps_stack = _` (fn th =>
    qpat_x_assum `LIST_ELEM_COUNT (Var v) ps2.ps_stack + _ <= _`
      (mp_tac o ONCE_REWRITE_RULE [th])) >>
  simp[elem_count_append]
QED

Theorem stack_pop_elem_count_le:
  !n xs x. LIST_ELEM_COUNT x (stack_pop n xs) <= LIST_ELEM_COUNT x xs
Proof
  rpt gen_tac >>
  `LIST_ELEM_COUNT x xs =
    LIST_ELEM_COUNT x (TAKE (LENGTH xs - n) xs) +
    LIST_ELEM_COUNT x (DROP (LENGTH xs - n) xs)` by
    metis_tac[TAKE_DROP, elem_count_append] >>
  simp[stack_pop_def]
QED

Theorem do_swap_resource_count:
  !n ps x. n < LENGTH ps.ps_stack ==>
    LIST_ELEM_COUNT x (SND (do_swap n ps)).ps_stack +
      (if x IN FDOM (SND (do_swap n ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >> drule do_swap_multiplicity >>
  simp[do_swap_spilled_unchanged]
QED

Theorem popmany_individual_resource_nonincrease:
  !items ps ops qs.
    popmany_individual items ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack + (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f acc sorted` >>
  `!items acc x.
    LIST_ELEM_COUNT x (SND (FOLDL f acc items)).ps_stack +
      (if x IN FDOM (SND (FOLDL f acc items)).ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x (SND acc).ps_stack +
      (if x IN FDOM (SND acc).ps_spilled then 1 else 0)` suffices_by
    (rpt strip_tac >> first_x_assum (qspecl_then [`sorted`, `acc`, `x`] mp_tac) >>
     gvs[Abbr `acc`]) >>
  Induct >> simp[] >> rpt gen_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `LIST_ELEM_COUNT x (SND (f acc' h)).ps_stack +
    (if x IN FDOM (SND (f acc' h)).ps_spilled then 1 else 0)` >>
  conj_tac >- simp[] >>
  PairCases_on `acc'` >> simp[Abbr `f`] >>
  rename1 `stack_get_depth h p.ps_stack` >>
  Cases_on `stack_get_depth h p.ps_stack` >> simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  rename1 `stack_get_depth h p.ps_stack = SOME dist` >>
  Cases_on `dist = 0` >> simp[]
  >- irule stack_pop_elem_count_le >>
  pairarg_tac >> simp[] >>
  drule do_swap_resource_count >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >>
  qspecl_then [`1`, `ps'.ps_stack`, `x`] mp_tac stack_pop_elem_count_le >>
  rpt strip_tac >>
  qpat_x_assum `LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
    (fn th => once_rewrite_tac [GSYM th]) >> simp[]
QED

Theorem popmany_plan_resource_nonincrease:
  !items ps ops qs.
    popmany_plan items ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack + (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  Cases >- (simp[popmany_plan_def] >> rpt strip_tac >> gvs[]) >>
  simp[popmany_plan_def] >> rpt gen_tac >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_resource_nonincrease] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_resource_nonincrease] >>
  qmatch_asmsub_abbrev_tac `is_contiguous_top depths` >>
  `!v. IS_SOME (stack_get_depth v ps.ps_stack) ==>
    THE (stack_get_depth v ps.ps_stack) < LENGTH ps.ps_stack` by
    (rpt strip_tac >> Cases_on `stack_get_depth v ps.ps_stack` >> gvs[] >>
     drule stack_get_depth_props >> simp[]) >>
  `!d. MEM d depths ==> d < LENGTH ps.ps_stack` by
    (simp[Abbr `depths`, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (SUC (LENGTH t)) depths` by
    (`LENGTH depths = SUC (LENGTH t)` by simp[Abbr `depths`] >>
     `MEM (SUC (LENGTH t)) (QSORT (\a b. a <= b) depths)` by
       gvs[is_contiguous_top_def, LET_THM, MEM_GENLIST] >>
     metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]) >>
  `SUC (LENGTH t) < LENGTH ps.ps_stack` by metis_tac[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> gen_tac >>
  qspecl_then [`SUC (LENGTH t)`, `ps`, `x`] mp_tac do_swap_resource_count >>
  impl_tac >- metis_tac[] >> simp[] >> strip_tac >>
  qpat_x_assum `LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
    (fn th => once_rewrite_tac [GSYM th]) >> simp[stack_pop_elem_count_le]
QED

Theorem optimistic_swap_plan_resource_count:
  !dfg inst nl term ps ops qs.
    optimistic_swap_plan dfg inst nl term ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack + (if x IN FDOM qs.ps_spilled then 1 else 0) =
      LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >> strip_tac >> gen_tac >>
  Cases_on `term` >> gvs[] >>
  Cases_on `inst.inst_outputs = []` >> gvs[] >>
  Cases_on `nl = []` >> gvs[] >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))` >> gvs[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> gvs[] >>
  drule stack_get_depth_props >> strip_tac >>
  drule do_swap_resource_count >> simp[]
QED

Theorem release_dead_spills_resource_nonincrease:
  !nl ps x.
    LIST_ELEM_COUNT x (release_dead_spills nl ps).ps_stack +
      (if x IN FDOM (release_dead_spills nl ps).ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> simp[release_dead_spills_stack, release_dead_spills_domain] >>
  Cases_on `x IN FDOM ps.ps_spilled` >> simp[] >>
  Cases_on `MEM x (MAP Var nl)` >> simp[]
QED

Theorem emit_reorder_pop_variable_absent:
  !opc operands selected nl dfg ps iops ps1 rops ps2 v.
    PERM operands selected /\
    (!w. MEM (Var w) operands ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    ~MEM (Var v) operands ==>
    ~MEM (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) /\
    Var v NOTIN FDOM ps2.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  drule_all available_input_plan_length >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LENGTH selected <= LENGTH ps1.ps_stack` by simp[] >>
  drule_at (Pat `reorder_plan _ _ _ = _`) reorder_plan_inventory_subset_nb >>
  simp[] >> strip_tac >>
  `~MEM (Var v) ps1.ps_stack /\ Var v NOTIN FDOM ps1.ps_spilled` by
    metis_tac[emit_input_plan_variable_origins] >>
  `~MEM (Var v) ps2.ps_stack /\ Var v NOTIN FDOM ps2.ps_spilled` by metis_tac[] >>
  simp[stack_pop_def] >> metis_tac[MEM_TAKE]
QED

(* Exact copy from reorderSim.all_distinct_elem_count_le_one (local there). *)
Theorem all_distinct_elem_count_le_one:
  !(xs : 'a list) x.
    ALL_DISTINCT xs ==> LIST_ELEM_COUNT x xs <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (`~(LIST_ELEM_COUNT h xs > 0)` by
        metis_tac[LIST_ELEM_COUNT_MEM] >> decide_tac)
  >> first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

(* Exact copy of reorderSim.do_dup_inventory_subset; importing that
   frame-level theory here would cross the planner-leaf boundary.
   Use the already imported deepResidualBudget spill projection. *)
Theorem do_dup_inventory_subset:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ do_dup d ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule do_dup_stack_exact >> simp[] >> strip_tac >>
  drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
  rpt strip_tac >> gvs[stack_dup_def, MEM_SNOC] >>
  metis_tac[stack_peek_mem]
QED

(* Exact copy of regularPostfixSim.popmany_plan_top_singleton;
   importing that simulation theory would cross the planner-leaf boundary. *)
Theorem popmany_plan_top_singleton:
  stack_get_depth v ps.ps_stack = SOME 0 ==>
  popmany_plan [v] ps =
    ([SOPop 1], ps with ps_stack := stack_pop 1 ps.ps_stack)
Proof
  strip_tac >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF]
QED

(* Consumption debt is discharged only when the entire selected suffix is
   removed. This pointwise fact needs neither global inventory support nor
   uniqueness of unrelated names. *)
Theorem selected_suffix_resource_extinction:
  !ps prefix selected x.
    ps.ps_stack = prefix ++ selected /\
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
        LIST_ELEM_COUNT x selected ==>
    LIST_ELEM_COUNT x (stack_pop (LENGTH selected) ps.ps_stack) = 0 /\
    x NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  gvs[elem_count_append, stack_pop_def, TAKE_APPEND, TAKE_TAKE] >>
  Cases_on `x IN FDOM ps.ps_spilled` >> gvs[]
QED

Theorem emit_reorder_pop_last_use_extinction:
  !ps operands selected opc nl dfg iops ps1 rops ps2 v.
    LENGTH operands <= 16 /\ PERM operands selected /\
    (!w. MEM (Var w) operands ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
    MEM (Var v) operands /\ ~MEM v nl /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH selected) ps2.ps_stack) = 0 /\
    Var v NOTIN FDOM ps2.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `MEM (Var v) selected` by metis_tac[sortingTheory.PERM_MEM_EQ] >>
  `MEM v (operand_vars operands ++ nl)` by
    simp[input_mem_operand_vars] >>
  drule_all emit_input_plan_relevant_variable_upper >> simp[] >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) ps1.ps_stack = LIST_ELEM_COUNT (Var v) selected /\
    Var v NOTIN FDOM ps1.ps_spilled` by
    (qpat_x_assum `!x. LIST_ELEM_COUNT x operands <= _`
       (qspec_then `Var v` assume_tac) >>
     Cases_on `Var v IN FDOM ps1.ps_spilled` >> gvs[] >> decide_tac) >>
  `LIST_ELEM_COUNT (Var v) ps2.ps_stack = LIST_ELEM_COUNT (Var v) selected` by
    (`LENGTH selected <= 16 /\ LENGTH selected <= LENGTH ps1.ps_stack /\
      (!x. MEM x selected ==>
        LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x ps1.ps_stack)` by
       (gvs[] >> metis_tac[]) >>
     drule_all reorder_plan_materialised_counts >> simp[]) >>
  `Var v NOTIN FDOM ps2.ps_spilled` by
    (drule_all reorder_plan_pending_not_spilled >>
     disch_then (qspec_then `dfg` mp_tac) >> simp[]) >>
  irule selected_suffix_resource_extinction >> simp[] >>
  qexists_tac `stack_pop (LENGTH selected) ps2.ps_stack` >>
  metis_tac[emit_reorder_plan_bounded_core_suffix]
QED

(* Exact copy of reorderSim.elem_count_snoc (local there). *)
Theorem elem_count_snoc[local]:
  !x y (xs : 'a list).
    LIST_ELEM_COUNT x (SNOC y xs) =
    LIST_ELEM_COUNT x xs + LIST_ELEM_COUNT x [y]
Proof
  gen_tac >> gen_tac >> Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
QED

(* Exact copy of reorderSim.stack_pop_one_elem_count (local there).
   Kept here to avoid importing frame-level simulation theories. *)
Theorem stack_pop_one_elem_count[local]:
  !x (xs : 'a list).
    xs <> [] ==>
    LIST_ELEM_COUNT x (stack_pop 1 xs) +
    LIST_ELEM_COUNT x [stack_peek 0 xs] = LIST_ELEM_COUNT x xs
Proof
  rpt strip_tac >>
  `?ys y. xs = SNOC y ys` by metis_tac[rich_listTheory.SNOC_CASES] >>
  gvs[stack_pop_def, stack_peek_def, elem_count_snoc,
      rich_listTheory.TAKE_SNOC, EL_LENGTH_SNOC]
QED

Theorem pop_unique_operand:
  !x ps d.
    stack_get_depth x ps.ps_stack = SOME d /\
    LIST_ELEM_COUNT x ps.ps_stack <= 1 ==>
    ~MEM x (stack_pop 1 (SND (do_swap d ps)).ps_stack)
Proof
  rpt strip_tac >> drule stack_get_depth_props >> strip_tac >>
  `LIST_ELEM_COUNT x (SND (do_swap d ps)).ps_stack =
    LIST_ELEM_COUNT x ps.ps_stack` by simp[do_swap_multiplicity] >>
  `stack_peek 0 (SND (do_swap d ps)).ps_stack = x` by
    (simp[do_swap_stack_result, stack_peek_def, stack_swap_def, EL_LUPDATE] >>
     gvs[stack_peek_def]) >>
  `(SND (do_swap d ps)).ps_stack <> []` by
    (simp[do_swap_stack_result, stack_swap_def] >> strip_tac >> gvs[]) >>
  drule stack_pop_one_elem_count >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[LIST_ELEM_COUNT_THM] >> strip_tac >>
  `LIST_ELEM_COUNT x (stack_pop 1 (SND (do_swap d ps)).ps_stack) = 0` by decide_tac >>
  gvs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem popmany_individual_unique_absent:
  !items ps ops qs x.
    MEM x items /\ LIST_ELEM_COUNT x ps.ps_stack <= 1 /\
    popmany_individual items ps = (ops,qs) ==>
    ~MEM x qs.ps_stack
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f acc sorted` >>
  `MEM x sorted` by simp[Abbr `sorted`, sortingTheory.QSORT_MEM] >>
  `!ys p a.
    LIST_ELEM_COUNT x p.ps_stack <= 1 /\
    (MEM x ys \/ ~MEM x p.ps_stack) ==>
    ~MEM x (SND (FOLDL f (a,p) ys)).ps_stack` suffices_by
    (disch_then (qspecl_then [`sorted`,`ps`,`[]`] mp_tac) >>
     gvs[Abbr `acc`]) >>
  Induct >- simp[] >> pure_rewrite_tac[FOLDL] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qmatch_goalsub_abbrev_tac `FOLDL f acc1 ys` >>
  `LIST_ELEM_COUNT x (SND acc1).ps_stack <= LIST_ELEM_COUNT x p.ps_stack` by
    (simp[Abbr `acc1`, Abbr `f`] >>
     Cases_on `stack_get_depth h p.ps_stack` >> simp[] >>
     drule stack_get_depth_props >> strip_tac >>
     Cases_on `x' = 0` >> simp[stack_pop_elem_count_le] >>
     pairarg_tac >> simp[] >>
     qspecl_then [`1`,`ps'.ps_stack`,`x`] mp_tac stack_pop_elem_count_le >>
     drule do_swap_multiplicity >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  `MEM x ys \/ ~MEM x (SND acc1).ps_stack` by
    (Cases_on `MEM x ys` >> simp[] >>
     Cases_on `MEM x p.ps_stack`
     >- (`h = x` by fs[] >>
         simp[Abbr `acc1`, Abbr `f`] >>
         Cases_on `stack_get_depth x p.ps_stack` >> simp[]
         >- metis_tac[stack_get_depth_is_some, optionTheory.IS_SOME_DEF] >>
         Cases_on `x' = 0` >> simp[]
         >- (drule_all pop_unique_operand >> simp[do_swap_def]) >>
         pairarg_tac >> simp[] >> drule_all pop_unique_operand >> simp[]) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  PairCases_on `acc1` >> first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem popmany_plan_unique_absent:
  !items ps ops qs x.
    MEM x items /\ LIST_ELEM_COUNT x ps.ps_stack <= 1 /\
    popmany_plan items ps = (ops,qs) ==>
    ~MEM x qs.ps_stack
Proof
  Cases >- simp[] >> rpt gen_tac >>
  simp[popmany_plan_def] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_unique_absent, MEM] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_unique_absent, MEM] >>
  strip_tac >>
  `set (h::t) SUBSET set ps.ps_stack` by
    (gvs[SUBSET_DEF, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     metis_tac[stack_get_depth_is_some]) >>
  `LENGTH (h::t) < LENGTH ps.ps_stack /\
   set (h::t) = set (MAP (\d. stack_peek d ps.ps_stack)
      (GENLIST SUC (LENGTH (h::t))))` by
    (qspecl_then [`h::t`,`[]`,`ps.ps_stack`,`ps`] mp_tac contiguous_depths_core >> simp[]) >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  `?rest top. ps.ps_stack = SNOC top rest` by metis_tac[SNOC_CASES] >>
  `LENGTH (h::t) <= LENGTH rest` by gvs[] >>
  `?base removed. ps.ps_stack = base ++ removed ++ [top] /\
      LENGTH removed = LENGTH (h::t)` by
    (qexistsl_tac [`TAKE (LENGTH rest - LENGTH (h::t)) rest`,
                  `DROP (LENGTH rest - LENGTH (h::t)) rest`] >>
     conj_tac
     >- (pure_rewrite_tac[GSYM APPEND_ASSOC, TAKE_DROP] >> simp[SNOC_APPEND]) >>
     gvs[LENGTH_DROP]) >>
  `set (h::t) = set removed` by
    (qpat_x_assum `LENGTH removed = _` (assume_tac o SYM) >>
     gvs[stack_peek_contiguous]) >>
  rename1 `ps.ps_stack = lower ++ removed ++ [top]` >>
  `MEM x removed` by
    (qpat_x_assum `set (h::t) = set removed` mp_tac >>
     simp[EXTENSION] >> metis_tac[]) >>
  `0 < LIST_ELEM_COUNT x removed` by gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  `~MEM x (lower ++ [top])` by
    (Cases_on `x = top` >>
     gvs[elem_count_append, LIST_ELEM_COUNT_THM, GSYM LIST_ELEM_COUNT_MEM]) >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`LENGTH removed`,`ps`] mp_tac do_swap_stack_result >>
  simp[] >> strip_tac >>
  qpat_x_assum `LENGTH removed = _` (assume_tac o SYM) >>
  gvs[stack_pop_contiguous]
QED

Theorem clean_stack_plan_spilled_unchanged:
  !lv cfg fn bb ps ops qs.
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  Cases_on `t` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[popmany_plan_spilled_unchanged, pairTheory.SND]) >>
  metis_tac[popmany_plan_spilled_unchanged, pairTheory.SND]
QED

Theorem clean_stack_plan_branch_unique_absent:
  !lv cfg fn bb pred pred_bb v ps ops qs.
    cfg_preds_of cfg bb.bb_label = [pred] /\
    1 < LENGTH (cfg_succs_of cfg pred) /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)) /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at lv bb.bb_label 0)) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def] >>
  qmatch_goalsub_abbrev_tac `NULL inputs` >>
  qmatch_goalsub_abbrev_tac `NULL inputs /\ ok` >>
  qmatch_goalsub_abbrev_tac `mark_dead_stack retained` >>
  qmatch_goalsub_abbrev_tac `popmany_plan requests ps` >>
  `MEM (Var v) (MAP Var
    (FILTER (\w. ~MEM w inputs)
      (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))))` by
    simp[MEM_MAP, MEM_FILTER, Abbr `inputs`] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[MEM_MAP, dead_stack_marker_def]) >>
  reverse IF_CASES_TAC >> simp[]
  >- metis_tac[popmany_plan_unique_absent] >>
  pairarg_tac >> simp[] >> disch_then (CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  Cases_on `MEM (Var v) retained`
  >- (simp[mark_dead_stack_def, MEM_MAP, dead_stack_marker_def] >>
      gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  `~MEM (Var v) ps'.ps_stack` by
    (Cases_on `MEM (Var v) ps.ps_stack`
     >- (`MEM (Var v) requests` by
           simp[Abbr `requests`, MEM_FILTER, stack_get_depth_is_some] >>
         metis_tac[popmany_plan_unique_absent]) >>
     `ps'.ps_spilled = ps.ps_spilled` by
       metis_tac[popmany_plan_spilled_unchanged, pairTheory.SND] >>
     drule popmany_plan_resource_nonincrease >>
     disch_then (qspec_then `Var v` mp_tac) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  simp[mark_dead_stack_def, MEM_MAP, dead_stack_marker_def] >>
  gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem clean_stack_plan_branch_resource_absent:
  !lv cfg fn bb pred pred_bb v ps ops qs.
    cfg_preds_of cfg bb.bb_label = [pred] /\
    1 < LENGTH (cfg_succs_of cfg pred) /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)) /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at lv bb.bb_label 0)) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    Var v NOTIN FDOM ps.ps_spilled /\
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule clean_stack_plan_branch_unique_absent >> metis_tac[]) >>
  drule clean_stack_plan_spilled_unchanged >> simp[]
QED

Theorem do_restore_stack_support:
  !op ps ops qs x.
    do_restore op ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    x = op \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[stack_push_def]
QED

Theorem restore_spilled_plan_stack_support:
  !targets ps ops qs x.
    restore_spilled_plan targets ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x targets \/ MEM x ps.ps_stack
Proof
  Induct >- (simp[restore_spilled_plan_def] >> rpt strip_tac >> gvs[]) >>
  simp[restore_spilled_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then drule >>
  drule do_restore_stack_support >> metis_tac[]
QED


Theorem do_spill_at_stack_support:
  !d ps ops qs x.
    do_spill_at d ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x ps.ps_stack
Proof
  rpt gen_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def, do_spill_tos_def, stack_pop_def, LET_THM] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[rich_listTheory.MEM_TAKE]) >>
  simp[do_spill_at_def, do_spill_tos_def, stack_pop_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule rich_listTheory.MEM_TAKE >> strip_tac >>
  metis_tac[stack_swap_mem_subset]
QED

Theorem reduce_depth_plan_stack_support:
  !fuel targets op f n ps ops qs x.
    reduce_depth_plan fuel targets op f n ps = (ops,qs) /\
    MEM x qs.ps_stack ==> MEM x ps.ps_stack
Proof
  Induct >- (simp[reduce_depth_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[Once reduce_depth_plan_def] >>
  Cases_on `f + 1 < n` >- simp[] >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >- simp[] >> simp[] >>
  rename1 `stack_get_unfixed_depth op f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >- simp[] >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n` >- simp[] >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then drule >>
  metis_tac[do_spill_at_stack_support]
QED

Theorem do_swap_safe_stack_support:
  !d ps ops qs x.
    (d <= 16 \/ d < LENGTH ps.ps_stack) /\
    do_swap d ps = (ops,qs) /\ MEM x qs.ps_stack ==> MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d <= 16`
  >- (qpat_x_assum `do_swap _ _ = _` mp_tac >>
      simp[do_swap_def] >> Cases_on `d = 0` >> simp[] >>
      strip_tac >> gvs[] >> metis_tac[stack_swap_mem_subset]) >>
  `d < LENGTH ps.ps_stack` by simp[] >>
  drule doSwapSimTheory.do_swap_stack_perm >> simp[] >>
  metis_tac[sortingTheory.PERM_MEM_EQ]
QED

Theorem reorder_restore_stack_support[local]:
  !op f n ps ops qs x.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,qs) /\
    MEM x qs.ps_stack ==> x = op \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[do_restore_stack_support]
QED

Theorem reorder_one_stack_support:
  !dfg tops idx op ps ops qs x.
    idx < LENGTH tops /\ LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_one dfg tops idx op ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    x = op \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gnvs[] >>
  `LENGTH ps.ps_stack <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_restore_inventory_subset_nb] >>
  `!a. MEM a ps1.ps_stack ==> a = op \/ MEM a ps.ps_stack` by
    metis_tac[reorder_restore_stack_support] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH tops - (idx + 1))
    (LENGTH tops) ps1.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `LENGTH tops <= LENGTH ps2.ps_stack /\
   !a. MEM a ps2.ps_stack ==> MEM a ps1.ps_stack` by
    (Cases_on `dist > 16` >> gvs[] >> conj_tac
     >- (drule reduce_depth_plan_target_len_floor >> simp[]) >>
     rpt strip_tac >> drule reduce_depth_plan_stack_support >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH tops - (idx + 1))
    (LENGTH tops) ps2.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH tops - (idx + 1)` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (`MEM (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack) ps2.ps_stack` by
        (irule stack_peek_mem >> decide_tac) >>
      strip_tac >> gvs[] >> metis_tac[stack_poke_mem_subset_nb]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  `MEM x ps3.ps_stack` by
    (irule do_swap_safe_stack_support >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM x ps2.ps_stack` by
    (irule do_swap_safe_stack_support >>
     qexistsl [`dist'`, `swap1_ops`, `ps3`] >> simp[]) >>
  metis_tac[]
QED

Theorem plan_steps_reorder_stack_support[local]:
  !items dfg tops ps ops qs.
    EVERY (\(idx,op). idx < LENGTH tops /\ MEM op tops) items /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg tops idx op ps) items ps = (ops,qs) ==>
    !x. MEM x qs.ps_stack ==> MEM x tops \/ MEM x ps.ps_stack
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg tops idx op ps = (step_ops,ps1)` >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_length_floor] >>
  `!x. MEM x ps1.ps_stack ==> x = op \/ MEM x ps.ps_stack` by
    metis_tac[reorder_one_stack_support] >>
  rpt strip_tac >>
  `MEM x tops \/ MEM x ps1.ps_stack` by
    (first_x_assum (qspecl_then [`dfg`, `tops`, `ps1`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reorder_plan_stack_support:
  !dfg tops ps ops qs x.
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_plan dfg tops ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x tops \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH tops /\ MEM op tops)
    (MAPi (\i op. (i,op)) tops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[EL_MEM]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  metis_tac[plan_steps_reorder_stack_support]
QED

Theorem restore_reorder_stack_support:
  !targets ps rops mid dfg ops qs x.
    LENGTH targets <= LENGTH ps.ps_stack +
      CARD (set targets INTER FDOM ps.ps_spilled) /\
    restore_spilled_plan targets ps = (rops,mid) /\
    reorder_plan dfg targets mid = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x targets \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (drule restore_spilled_plan_length_exact >> simp[]) >>
  `MEM x targets \/ MEM x mid.ps_stack` by
    (drule_all reorder_plan_stack_support >> simp[]) >>
  metis_tac[restore_spilled_plan_stack_support]
QED
