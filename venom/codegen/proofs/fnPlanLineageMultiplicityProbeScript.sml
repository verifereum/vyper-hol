Theory fnPlanLineageMultiplicityProbe
Ancestors
  codegenReadyCompute stackPlanGen livenessDefs stackPlanOps stackPlanTypes
  stackModel venomInst cfgTransform fnPlanLineageInventory
Libs wordsLib

Definition repeated_use_fn_def:
  repeated_use_fn branch = mk_raw_function "repeated_use"
    ([<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ADD [Lit 10w; Lit 1w] ["x"]] ++
        (if branch then
          [mk_inst 1 ADD [Lit 1w; Lit 0w] ["c"];
           mk_inst 2 JNZ [Var "c"; Label "use"; Label "other"] []]
         else [mk_inst 2 JMP [Label "use"] []]) |>;
      <| bb_label := "use"; bb_instructions :=
        [mk_inst 3 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 4 JMP [Label "exit"] []] |>;
      <| bb_label := "exit"; bb_instructions := [mk_inst 5 STOP [] []] |>] ++
     (if branch then [<| bb_label := "other"; bb_instructions :=
        [mk_inst 6 STOP [] []] |>] else []))
End

Theorem repeated_use_ready:
  codegen_ready_fn (repeated_use_fn F) /\
  codegen_ready_fn (repeated_use_fn T) /\
  EVERY (\fn. EVERY (\bb. EVERY (\inst. EVERY (\op.
    op <> dead_stack_marker) inst.inst_operands) bb.bb_instructions)
    fn.fn_blocks) [repeated_use_fn F; repeated_use_fn T]
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_use_liveness:
  live_vars_at (liveness_analyze (repeated_use_fn F)) "use" 0 = ["x";"x"] /\
  live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0 = ["x";"x"] /\
  input_vars_from "entry" (EL 1 (repeated_use_fn F).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn F)) "use" 0) = ["x";"x"] /\
  input_vars_from "entry" (EL 1 (repeated_use_fn T).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0) = ["x";"x"]
Proof
  EVAL_TAC
QED

Theorem repeated_use_plan_results:
  generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (repeated_use_fn F)) (dfg_build_function (repeated_use_fn F))
    (cfg_analyze (repeated_use_fn F)) NONE [] (repeated_use_fn F) 0 0 = NONE /\
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) NONE [] (repeated_use_fn T) 0 0)
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Theorem repeated_use_branch_entry:
  IS_SOME (generate_block_plan
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) (repeated_use_fn T)
    (EL 0 (repeated_use_fn T).fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)) /\
  (SND (THE (generate_block_plan
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) (repeated_use_fn T)
    (EL 0 (repeated_use_fn T).fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)))).ps_stack = [Var "x"] /\
  ~ALL_DISTINCT (MAP Var (input_vars_from "entry"
    (EL 1 (repeated_use_fn T).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0)))
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

(* JMP rejects the repeated target suffix; single-predecessor JNZ succeeds
   with one available x although the analyzed target list requests two.
   This refutes actual-caller target distinctness, not block-plan replay. *)

(* Test the unbounded height proposal at an undersized deep swap window. *)
Theorem protected_reorder_height_probe:
  DISJOINT (set (REPLICATE 18 (Var "x")))
    (FDOM (init_cleanup_plan_state NONE [] 0 0).ps_spilled) /\
  LENGTH (SND (reorder_one (dfg_build_function (repeated_use_fn F))
    (REPLICATE 18 (Var "x")) 0 (Var "x")
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"]))).ps_stack = 18
Proof
  EVAL_TAC >> simp[]
QED

(* The bulk swap is intentionally left symbolic at out-of-range ELs.
   Subsequent fold steps branch on whether these unspecified values equal x. *)
Theorem protected_reorder_first_stack_probe:
  (SND (reorder_one (dfg_build_function (repeated_use_fn F))
    (REPLICATE 18 (Var "x")) 0 (Var "x")
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"]))).ps_stack =
  [EL 17 [Var "x"]] ++ GENLIST (\i. EL (i + 1) [Var "x"]) 16 ++ [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED

(* Whole-fold diagnostic: evaluation of reorder_plan on the preceding
   singleton example stops at comparisons of Var "x" with EL n [] / HD [].
   These are unspecified HOL values, not fresh symbolic operands that may be
   assumed different from x. Thus neither final suffix success nor failure
   has been certified for this example. The first step already raises the
   height to the target length; the existing reorder_one_length_floor and
   reorder_plan_inventory_subset_nb interfaces require an input floor, not
   merely a successful output suffix. A native producer for that route must
   establish LENGTH targets <= LENGTH mid.ps_stack after restoration (or the
   stronger pending_inventory_wf before restoration). Ordinary set coverage
   does not supply this multiplicity bound. This diagnostic establishes no
   counterexample to the frozen block theorem. *)

(* A genuine ready local producer: ADD leaves one x before a JMP requesting
   two. The global JMP plan is rejected, as proved above; this only rules
   out an unconditional scalar producer from readiness and ordinary steps. *)
Theorem repeated_use_local_scalar_obstruction:
  IS_SOME (generate_inst_plan
    (liveness_analyze (repeated_use_fn F))
    (dfg_build_function (repeated_use_fn F)) (cfg_analyze (repeated_use_fn F))
    (repeated_use_fn F) (mk_inst 0 ADD [Lit 10w; Lit 1w] ["x"])
    (live_vars_at (liveness_analyze (repeated_use_fn F)) "entry" 1)
    F T "entry" (init_cleanup_plan_state NONE [] 0 0)) /\
  (SND (THE (generate_inst_plan
    (liveness_analyze (repeated_use_fn F))
    (dfg_build_function (repeated_use_fn F)) (cfg_analyze (repeated_use_fn F))
    (repeated_use_fn F) (mk_inst 0 ADD [Lit 10w; Lit 1w] ["x"])
    (live_vars_at (liveness_analyze (repeated_use_fn F)) "entry" 1)
    F T "entry" (init_cleanup_plan_state NONE [] 0 0)))).ps_stack = [Var "x"] /\
  join_target_ops (liveness_analyze (repeated_use_fn F)) (repeated_use_fn F)
    "entry" (mk_inst 2 JMP [Label "use"] []) = SOME [Var "x"; Var "x"] /\
  ~(LENGTH [Var "x"; Var "x"] <= LENGTH [Var "x"] +
    CARD (set [Var "x"; Var "x"] INTER
      FDOM (init_cleanup_plan_state NONE [] 0 0).ps_spilled))
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

(* Scalar producer audit (not a reachable-state invariant):
   - join_target_ops is MAP Var of input_vars_from; singleton-label JMP has
     no compute_operands and therefore input emission adds no resources.
   - analyzed_live_out_jmp in fnPlanLineageLiveness equates SETS, not lists
     or counts. liveness_block combines edges with list_union, so repeated
     target occurrences need not survive into the predecessor's live-out.
   - input_vars_from's fold appends at most one result per base occurrence.
     PHI mapped indices are placed only once. Under phi_uses_disjoint the
     matching-to-operand map coherence prevents different indices from
     selecting the same variable (fnPlanLineagePhiMaps). Unmapped repeated
     base occurrences can still survive. No analyzed ALL_DISTINCT premise
     is available; repeated_use_liveness is a checked obstruction.
   - ordinary_position_invariant supplies live membership coverage, upper
     demand_available support and residual_budget_wf. These bound resources
     from above, not by target-list length from below. The preceding local
     producer proves that readiness and a successful ordinary step cannot
     by themselves imply the scalar lower bound. Spare non-target stack
     entries may satisfy the bound but are not guaranteed by those facts.
   - release_dead_spills preserves the stack and removes dead spill keys;
     it neither creates duplicate stack resources nor preserves all counts
     of arbitrary future target lists. Parameters/empty initialization also
     need an explicit lower-resource producer, not merely well-formedness.
   A possible sufficient new invariant would lower-bound stack length plus
   distinct target spills at each upcoming JMP. Its producers must handle
   initialization/parameters, each ordinary instruction's consumption and
   dead-output cleanup, PHI renaming, and every CFG edge/reset. No proof of
   these producers is supplied here. Global successful-function hypotheses
   exclude repeated_use_fn F, so the local obstruction does not refute the
   frozen theorem or the still-open success-conditioned scalar producer. *)

(* Resource-interface audit: repeated target demand is not deduplicated, but
   a shallow native JMP with unique input resources rejects that demand. *)
Theorem repeated_target_resource_probe:
  residual_budget_wf 0 []
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"; Var "z"]) /\
  generate_inst_plan
    (liveness_analyze (repeated_use_fn F))
    (dfg_build_function (repeated_use_fn F)) (cfg_analyze (repeated_use_fn F))
    (repeated_use_fn F) (mk_inst 2 JMP [Label "use"] []) ["x"] F T "entry"
    ((init_cleanup_plan_state NONE [] 0 0) with
      ps_stack := [dead_stack_marker; Var "x"; Var "z"]) = NONE
Proof
  EVAL_TAC >> simp[] >> gen_tac >> rpt IF_CASES_TAC >> simp[]
QED

Definition resource_probe_targets_def:
  resource_probe_targets = MAP Var
    ["a";"b";"c";"d";"e";"f";"g";"h";"i";
     "j";"k";"l";"m";"n";"o";"p";"q";"r"]
End

(* An unbounded target window with a nonzero marker prefix: the first
   indexed step is already aligned and leaves the whole state unchanged.
   This is a boundary probe, not a full-fold resource preservation proof. *)
Theorem deep_target_marker_resource_probe:
  LENGTH resource_probe_targets = 18 /\
  reorder_one (dfg_build_function (repeated_use_fn F)) resource_probe_targets
    0 (Var "a")
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      dead_stack_marker :: resource_probe_targets) =
    ([], (init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      dead_stack_marker :: resource_probe_targets)
Proof
  EVAL_TAC
QED

(* Empty-pending JMP resource-interface audit (not a preservation theorem).
   The existing repeated_use_liveness above certifies that input_vars_from
   retains repeated unmapped base variables; it does not deduplicate them.
   PHI classes are separately recorded by input_vars_from, but this does not
   remove repetitions of untouched base variables. Native success rejects
   the shallow repeated-target fixture even with an extra unique operand.

   residual_budget_wf base [] (reorderSim) requires count(core,op)<=1 and
   count(core,op)=0 for spilled operands, in addition to slot/layout facts.
   The new success-conditioned inventory subset proves neither count bound.
   The first-step 18-target test above checks a nonzero marker prefix only
   in the aligned case. Attempted full-fold resource evaluation (both
   reversed and aligned targets) exceeded the fixed 2.5-second tactic limit;
   no whole-fold conclusion or falsehood was obtained from those attempts.

   Existing resource interfaces: reorderSim.reorder_one_residual_budget_wf
   needs target length<=16 and a full-stack floor. For larger targets,
   deepResidualBudget.reorder_plan_residual_budget_wf_marked needs marked
   budget, pending_inventory_wf, and a full-stack floor; it preserves budget
   relative to pending targets, not an empty-pending distinct core.
   These bundle allocator layout/slot bounds with count control. None is a
   producer of a marker-free core floor or of target multiplicity from set
   coverage. Caller live-out coverage now supplies only the set premise
   (analyzed_terminal_jmp_target_coverage in fnPlanLineageCallers).

   The candidate fixed-m, empty-pending resource contract remains unvalidated.
   Before a general preservation proof, a strategy must supply a core-level
   safe-swap/count argument across the restored reorder window (including
   possible undersized deep windows), plus fixed-marker-prefix and allocator
   layout preservation. Native suffix success and full-stack inventory alone
   are not proofs of those obligations. These diagnostics establish no
   counterexample to the candidate or to the frozen TASK theorem. *)
