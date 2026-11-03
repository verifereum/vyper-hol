Theory createSizePrefixProbe
Ancestors
  stackPlanGen stackPlanOps dfgDefs mixedPrefixSim rich_list doSwapSim reorderSim
Libs wordsLib

(* Concrete deep output suffix: no dependency on genBlockSim admissions. *)
Definition probe_ps_def:
  probe_ps = <| ps_stack := GENLIST (\i. Lit (n2w i)) 18;
    ps_spilled := FEMPTY;
    ps_alloc := <| sa_free_slots := []; sa_next_offset := 1024;
                  sa_spill_base := 1024 |>;
    ps_label_counter := 0; ps_cleanup_height := NONE;
    ps_cleanup_growth := []; ps_cleanup_promised := F |>
End

Theorem probe_deep_swap_shape:
  LENGTH (FST (do_swap 17 probe_ps)) = 36 /\
  TAKE 18 (FST (do_swap 17 probe_ps)) =
    GENLIST (\i. SOSpill (1024 + 32 * i)) 18 /\
  LAST (FST (do_swap 17 probe_ps)) = SORestore 1568
Proof
  EVAL_TAC
QED

Definition probe_inst_def:
  probe_inst = <| inst_opcode := CREATE;
    inst_operands := [Lit 0w; Lit 1w; Lit 49153w];
    inst_outputs := ["out"] |>
End

Definition probe_base_def:
  probe_base = probe_ps with ps_stack :=
    Var "deep" :: GENLIST (\i. Lit (n2w (100 + i))) 16
End

Definition probe_plan_def:
  probe_plan liveness cfg fn = generate_regular_inst_plan liveness dfg_empty cfg fn
    probe_inst ["out"; "deep"] F F "bb" probe_base
End

Theorem probe_normalize:
  normalize_operand dfg_empty visited op = op
Proof
  Cases_on `op` >> simp[normalize_operand_def, dfg_empty_def,
    dfg_get_def_def]
QED

val _ = computeLib.add_funs [probe_normalize, pairTheory.UNCURRY_DEF];

Theorem probe_actual_plan:
  FST (probe_plan liveness cfg fn) =
    [SOPush (Lit 49153w); SOPush (Lit 1w); SOPush (Lit 0w);
     SOEmit "CREATE"] ++
    FST (do_swap 17 (probe_base with ps_stack :=
      probe_base.ps_stack ++ [Var "out"]))
Proof
  EVAL_TAC
QED

Definition probe_prefix_def:
  probe_prefix = [SOPush (Lit 49153w); SOPush (Lit 1w); SOPush (Lit 0w)]
End

Theorem probe_actual_prefix_stack:
  (apply_prefix_ops initial_fmp lo probe_prefix probe_base).ps_stack =
    probe_base.ps_stack ++ [Lit 49153w; Lit 1w; Lit 0w]
Proof
  EVAL_TAC
QED

(* The spill part of FRONT is evaluated on the pre-op stack, not on the
   planner's abstract post-CREATE stack. *)
Theorem probe_fictitious_spills:
  (apply_prefix_ops initial_fmp lo
    (probe_prefix ++ [SOEmit "CREATE"] ++
      TAKE 18 (FST (do_swap 17 (probe_base with ps_stack :=
        probe_base.ps_stack ++ [Var "out"])))) probe_base).ps_stack =
    [Var "deep"; Lit 100w] /\
  FLOOKUP (apply_prefix_ops initial_fmp lo
    (probe_prefix ++ [SOEmit "CREATE"] ++
      TAKE 18 (FST (do_swap 17 (probe_base with ps_stack :=
        probe_base.ps_stack ++ [Var "out"])))) probe_base).ps_spilled
    (Lit 0w) = SOME 1024
Proof
  EVAL_TAC
QED


Definition probe_spills_def:
  probe_spills = apply_prefix_ops 0 FEMPTY
    (probe_prefix ++ [SOEmit "CREATE"] ++
      TAKE 18 (FST (do_swap 17 (probe_base with ps_stack :=
        probe_base.ps_stack ++ [Var "out"])))) probe_base
End

Theorem probe_spills_value:
  probe_spills = probe_base with <|
    ps_stack := [Var "deep"; Lit 100w];
    ps_alloc := probe_base.ps_alloc with sa_next_offset := 1600;
    ps_spilled := FEMPTY |++
      [(Lit 0w,1024); (Lit 1w,1056); (Lit 49153w,1088);
       (Lit 115w,1120); (Lit 114w,1152); (Lit 113w,1184);
       (Lit 112w,1216); (Lit 111w,1248); (Lit 110w,1280);
       (Lit 109w,1312); (Lit 108w,1344); (Lit 107w,1376);
       (Lit 106w,1408); (Lit 105w,1440); (Lit 104w,1472);
       (Lit 103w,1504); (Lit 102w,1536); (Lit 101w,1568)] |>
Proof
  EVAL_TAC
QED

Theorem probe_restore_suffix:
  DROP 22 (FRONT (FST (probe_plan liveness cfg fn))) =
    [SORestore 1024; SORestore 1536; SORestore 1504; SORestore 1472;
     SORestore 1440; SORestore 1408; SORestore 1376; SORestore 1344;
     SORestore 1312; SORestore 1280; SORestore 1248; SORestore 1216;
     SORestore 1184; SORestore 1152; SORestore 1120; SORestore 1088;
     SORestore 1056]
Proof
  EVAL_TAC
QED

Theorem probe_first_restore:
  spill_lookup 1024 probe_spills.ps_spilled = Lit 0w
Proof
  simp[probe_spills_value, spill_lookup_def, finite_mapTheory.FUPDATE_LIST_THM,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  irule SELECT_UNIQUE >> gen_tac >>
  BETA_TAC >> rpt IF_CASES_TAC >> gvs[] >> EVAL_TAC
QED

(* In this concrete table, deleting other entries cannot change a restore. *)
Theorem probe_lookup_delete:
  (!x. FLOOKUP fm x = SOME off <=> x = v) /\ v <> removed ==>
  spill_lookup off (fm \\ removed) = v
Proof
  strip_tac >> simp[spill_lookup_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  irule SELECT_UNIQUE >> simp[] >> metis_tac[]
QED

Definition probe_restores_def:
  probe_restores = [SORestore 1024; SORestore 1536; SORestore 1504;
    SORestore 1472; SORestore 1440; SORestore 1408; SORestore 1376;
    SORestore 1344; SORestore 1312; SORestore 1280; SORestore 1248;
    SORestore 1216; SORestore 1184; SORestore 1152; SORestore 1120;
    SORestore 1088; SORestore 1056]
End

Definition probe_restored_def:
  probe_restored k = apply_prefix_ops 0 FEMPTY (TAKE k probe_restores) probe_spills
End

Theorem probe_restored_one:
  probe_restored 1 = probe_spills with <|
    ps_stack := [Var "deep"; Lit 100w; Lit 0w];
    ps_spilled := probe_spills.ps_spilled \\ Lit 0w |>
Proof
  simp[probe_restored_def, probe_restores_def, apply_prefix_ops_def,
    apply_prefix_op_def, probe_first_restore,
    stackModelTheory.stack_push_def] >> simp[probe_spills_value]
QED

Definition probe_items_def:
  probe_items = [Lit 0w] ++ GENLIST (\i. Lit (n2w (102+i))) 14 ++
    [Lit 49153w; Lit 1w]
End


Theorem probe_table_lookup_mem[local]:
  !entries key off.
    FLOOKUP (FEMPTY |++ entries) key = SOME off ==> MEM (key,off) entries
Proof
  Induct using SNOC_INDUCT
  >- simp[finite_mapTheory.FUPDATE_LIST_THM] >>
  rpt gen_tac >> PairCases_on `x` >>
  simp[rich_listTheory.SNOC_APPEND, finite_mapTheory.FUPDATE_LIST_APPEND,
       finite_mapTheory.FUPDATE_LIST_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `key = x0` >> simp[] >> metis_tac[]
QED

Theorem probe_table_separation[local]:
  EVERY (\p. EVERY (\q. FST p = FST q \/ SND p + (32:num) <= SND q \/
                             SND q + 32 <= SND p) entries) entries ==>
  !k a j b. FLOOKUP (FEMPTY |++ entries) k = SOME a /\
             FLOOKUP (FEMPTY |++ entries) j = SOME b /\ k <> j ==>
             a + 32 <= b \/ b + 32 <= a
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  `MEM (k,a) entries` by (irule probe_table_lookup_mem >> metis_tac[]) >>
  `MEM (j,b) entries` by (irule probe_table_lookup_mem >> metis_tac[]) >>
  first_x_assum (qspec_then `(k,a)` mp_tac) >> simp[] >>
  disch_then (qspec_then `(j,b)` mp_tac) >> simp[]
QED

Definition probe_table_def:
  probe_table : (operand # num) list = [(Lit 0w,1024); (Lit 1w,1056); (Lit 49153w,1088);
       (Lit 115w,1120); (Lit 114w,1152); (Lit 113w,1184);
       (Lit 112w,1216); (Lit 111w,1248); (Lit 110w,1280);
       (Lit 109w,1312); (Lit 108w,1344); (Lit 107w,1376);
       (Lit 106w,1408); (Lit 105w,1440); (Lit 104w,1472);
       (Lit 103w,1504); (Lit 102w,1536); (Lit 101w,1568)]
End

Theorem probe_spilled_table:
  probe_spills.ps_spilled = FEMPTY |++ probe_table
Proof
  simp[probe_spills_value, probe_table_def]
QED

Theorem probe_spill_separation:
  !k a j b. FLOOKUP probe_spills.ps_spilled k = SOME a /\
             FLOOKUP probe_spills.ps_spilled j = SOME b /\ k <> j ==>
             a + 32 <= b \/ b + 32 <= a
Proof
  rewrite_tac[probe_spilled_table] >>
  qspec_then `probe_table` mp_tac (GEN_ALL probe_table_separation) >>
  (impl_tac >- EVAL_TAC) >> metis_tac[]
QED

Theorem probe_restore_stack:
  (apply_prefix_ops 0 FEMPTY probe_restores probe_spills).ps_stack =
    [Var "deep"; Lit 100w] ++ probe_items
Proof
  `probe_restores = MAP SORestore
     [1024;1536;1504;1472;1440;1408;1376;1344;1312;1280;1248;
      1216;1184;1152;1120;1088;1056]` by EVAL_TAC >>
  `probe_spills.ps_stack = [Var "deep"; Lit 100w]` by
    simp[probe_spills_value] >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[] >> irule apply_restore_ops_stack >>
  conj_tac
  >- (`EVERY (\k. FLOOKUP probe_spills.ps_spilled (EL k probe_items) =
          SOME (EL k [1024;1536;1504;1472;1440;1408;1376;1344;1312;
                      1280;1248;1216;1184;1152;1120;1088;1056]))
         (GENLIST I 17)` by EVAL_TAC >>
      gvs[listTheory.EVERY_GENLIST] >>
      `LENGTH probe_items = 17` by EVAL_TAC >> simp[]) >>
  conj_tac >- metis_tac[probe_spill_separation] >> EVAL_TAC
QED

Theorem probe_front_split:
  FRONT (FST (probe_plan liveness cfg fn)) =
    probe_prefix ++ [SOEmit "CREATE"] ++
      TAKE 18 (FST (do_swap 17 (probe_base with ps_stack :=
        probe_base.ps_stack ++ [Var "out"]))) ++ probe_restores
Proof
  EVAL_TAC
QED

Theorem probe_front_stack:
  (apply_prefix_ops 0 FEMPTY
    (FRONT (FST (probe_plan liveness cfg fn))) probe_base).ps_stack =
    [Var "deep"; Lit 100w; Lit 0w] ++
    GENLIST (\i. Lit (n2w (102+i))) 14 ++ [Lit 49153w; Lit 1w]
Proof
  rewrite_tac[probe_front_split, APPEND_ASSOC] >>
  once_rewrite_tac[planAlignTheory.apply_prefix_ops_append] >>
  rewrite_tac[GSYM probe_spills_def, probe_restore_stack] >> EVAL_TAC
QED

Theorem probe_front_alignment_incompatible:
  venom_asm_rel FEMPTY
    (apply_prefix_ops 0 FEMPTY
      (FRONT (FST (probe_plan liveness cfg fn))) probe_base) vs st_mid ==>
  ~(LENGTH (compute_operands probe_inst) <= LENGTH st_mid.as_stack /\
    !i. i < LENGTH (compute_operands probe_inst) ==>
      eval_operand (EL i (REVERSE (compute_operands probe_inst))) vs =
      SOME (EL i st_mid.as_stack))
Proof
  simp[codegenRelTheory.venom_asm_rel_def] >> strip_tac >>
  qpat_x_assum `plan_stack_rel _ _ _ _` mp_tac >>
  rewrite_tac[probe_front_stack, codegenRelTheory.plan_stack_rel_def] >>
  strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >>
  CONV_TAC (LAND_CONV EVAL) >>
  strip_tac >> disj2_tac >> qexists_tac `0` >> EVAL_TAC >> gvs[]
QED

(* Lower-bound inventory, deliberately independent of allocator layout. *)
Definition probe_inventory_def:
  probe_inventory x (ps : plan_state) =
    LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled then 1 else 0)
End

Theorem probe_input_inventory_accumulation[local]:
  !operands ps opc nl iops ps1 x.
    emit_input_plan opc operands nl ps = (iops, ps1) /\
    (is_var_operand x /\ MEM x operands ==> 1 <= probe_inventory x ps) ==>
    probe_inventory x ps + LIST_ELEM_COUNT x operands <=
    probe_inventory x ps1 +
      (if is_var_operand x /\ MEM x operands then 1 else 0)
Proof
  rewrite_tac[probe_inventory_def] >>
  metis_tac[emit_input_plan_inventory_accumulation]
QED

Theorem probe_inventory_accessible[local]:
  ((?d. stack_get_depth x ps.ps_stack = SOME d) \/
   IS_SOME (FLOOKUP ps.ps_spilled x)) ==>
  1 <= probe_inventory x ps
Proof
  strip_tac
  >- (drule stackModelTheory.stack_get_depth_props >> strip_tac >>
      `MEM x ps.ps_stack` by
        (gvs[stackModelTheory.stack_peek_def] >>
         irule listTheory.EL_MEM >> decide_tac) >>
      `0 < LIST_ELEM_COUNT x ps.ps_stack` by
        (drule (iffRL LIST_ELEM_COUNT_MEM) >> decide_tac) >>
      simp[probe_inventory_def] >> decide_tac) >>
  `x IN FDOM ps.ps_spilled` by
    (Cases_on `FLOOKUP ps.ps_spilled x` >>
     gvs[finite_mapTheory.flookup_thm]) >>
  simp[probe_inventory_def]
QED

Theorem probe_emit_input_plan_pending_inventory:
  !opc operands next_live ps input_ops ps1.
    (opc = CREATE \/ opc = CREATE2) /\
    (!op. MEM op operands /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    emit_input_plan opc operands next_live ps = (input_ops, ps1) ==>
    pending_inventory_wf operands ps1
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[pending_inventory_wf_def] >> gen_tac >>
  `is_var_operand op /\ MEM op operands ==> 1 <= probe_inventory op ps` by
    (strip_tac >> irule probe_inventory_accessible >> metis_tac[]) >>
  drule probe_input_inventory_accumulation >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >>
  Cases_on `is_var_operand op /\ MEM op operands` >>
  gvs[probe_inventory_def] >> strip_tac >>
  Cases_on `op IN FDOM ps.ps_spilled` >>
  Cases_on `op IN FDOM ps1.ps_spilled` >> gvs[] >> decide_tac
QED

Theorem probe_repeated_spilled_create_inventory:
  let ps = probe_ps with <| ps_stack := [];
    ps_spilled := FEMPTY |+ (Var "x", 1024) |> in
  pending_inventory_wf [Var "x"; Var "x"; Var "x"]
    (SND (emit_input_plan CREATE [Var "x"; Var "x"; Var "x"] [] ps)) /\
  pending_inventory_wf [Var "x"; Var "x"; Var "x"; Var "x"]
    (SND (emit_input_plan CREATE2
      [Var "x"; Var "x"; Var "x"; Var "x"] [] ps))
Proof
  EVAL_TAC >> simp[]
QED

(* Lower inventory plus an exact current window does not preserve that
   window when the next operand must be restored. *)
Definition probe_window_ps_def:
  probe_window_ps = probe_ps with <|
    ps_stack := [Lit 1w; Lit 0w; Lit 3w];
    ps_spilled := FEMPTY |+ (Var "x", 1024) |>
End

Theorem probe_restore_fixed_window_obstruction:
  let pending = [Lit 1w; Var "x"; Lit 3w] in
  let ps = probe_window_ps in
  pending_inventory_wf pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ 1 < LENGTH pending /\
  (!i. i < 1 ==> stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
  stack_get_unfixed_depth (EL 1 pending) 1 3 ps.ps_stack = NONE /\
  (SND (reorder_one dfg_empty pending 1 (EL 1 pending) ps)).ps_stack =
    [Lit 1w; Lit 0w; Var "x"; Lit 3w] /\
  ~(!i. i < 2 ==> stack_peek (LENGTH pending - 1 - i)
       (SND (reorder_one dfg_empty pending 1 (EL 1 pending) ps)).ps_stack = EL i pending)
Proof
  EVAL_TAC >> conj_tac
  >- (gen_tac >> Cases_on `op = Lit 1w` >>
      Cases_on `op = Lit 0w` >> Cases_on `op = Lit 3w` >>
      Cases_on `op = Var "x"` >> gvs[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> `i = 0` by decide_tac >> gvs[]) >>
  simp[NOT_FORALL_THM] >> qexists_tac `0` >> EVAL_TAC
QED
