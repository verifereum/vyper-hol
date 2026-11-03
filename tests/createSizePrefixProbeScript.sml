Theory createSizePrefixProbe
Ancestors
  stackPlanGen stackPlanOps dfgDefs mixedPrefixSim rich_list doSwapSim
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

