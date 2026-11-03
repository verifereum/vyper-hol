Theory createSizePrefixProbe
Ancestors
  stackPlanGen stackPlanOps dfgDefs mixedPrefixSim rich_list
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

