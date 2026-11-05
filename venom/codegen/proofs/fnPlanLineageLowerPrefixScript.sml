Theory fnPlanLineageLowerPrefix
Ancestors
  fnPlanLineageSuffix fnPlanLineageReplay fnPlanLineagePhiTemporal stackPlanGen stackPlanOps
  stackModel venomInst finite_map list rich_list

(* A suffix hit supplies both the actual search depth and the element used
   by shallow DUP.  No property of the lower prefix is needed. *)
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

(* Equal singleton suffixes do not in themselves shield optimistic_swap.
   The first state has a hidden occurrence of scheduled y; the second has
   none. Both lower prefixes are arbitrary. This is an arbitrary-state
   interface obstruction, NOT a reachable-program counterexample. *)
Theorem optimistic_swap_prefix_obstruction:
  inst.inst_outputs = [x] /\ x <> y /\
  ~operand_equiv dfg (Var x) (Var y) /\ ~MEM (Var y) prefixQ ==>
  FST (optimistic_swap_plan dfg inst [x;y] F
    (ps with ps_stack := prefixP ++ [Var y; Var x])) = [SOSwap 1] /\
  FST (optimistic_swap_plan dfg inst [x;y] F
    (ps with ps_stack := prefixQ ++ [Var x])) = []
Proof
  strip_tac >>
  `stack_get_depth (Var y) (prefixP ++ [Var y; Var x]) = SOME 1` by
    (irule stack_get_depth_suffix_hit >>
     simp[stack_get_depth_def, stack_find_def]) >>
  `stack_get_depth (Var y) (prefixQ ++ [Var x]) = NONE` by
    (simp[stack_get_depth_bottom_excluded, stack_get_depth_def, stack_find_def]) >>
  simp[optimistic_swap_plan_def, do_swap_def]
QED

Theorem regular_assign_top_suffix:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var v] /\
  inst.inst_outputs = [out] /\ v <> out /\ ps.ps_spilled = FEMPTY ==>
  generate_regular_inst_plan lv dfg cfg fn inst [out] F T lbl
    (ps with ps_stack := prefix ++ suffix ++ [Var v]) =
  ([], ps with ps_stack := prefix ++ suffix ++ [Var out])
Proof
  strip_tac >>
  `compute_operands inst = [Var v] /\ ~is_commutative inst.inst_opcode /\
   !n rs. generate_emit_ops inst n rs = ([],rs)` by
    simp[compute_operands_def, python_stack_operands_def,
         venomEffectsTheory.is_commutative_def, generate_emit_ops_def,
         asmIRTheory.venom_to_evm_name_def] >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       emit_input_plan_def, emit_one_input_def,
       stackPlanTypesTheory.is_var_operand_def,
       reorder_plan_def, reorder_one_def, stack_get_unfixed_depth_def,
       stack_get_depth_def, stack_find_def, stack_pop_def,
       stack_push_def, generate_emit_ops_def,
       popmany_plan_def, optimistic_swap_plan_def, release_dead_spills_def,
       dfgDefsTheory.operand_vars_def, venomInstTheory.operand_vars_def,
       listTheory.REVERSE_APPEND, listTheory.SNOC_APPEND,
       alistTheory.fmap_to_alist_FEMPTY, rich_listTheory.TAKE_APPEND, listTheory.TAKE_LENGTH_TOO_LONG]
QED

(* Consumer-premise ledger (C3.2.2.lower_prefix_boundary).

   This is a branch audit, not a proof of universal ordinary replay. The
   checked interfaces above deliberately distinguish suffix confinement
   from equality of live projections. P and Q need not have equal length.

   Existing reusable interfaces searched/reused:
   - fnPlanLineageSuffix: stack_get_depth_suffix_hit and PHI search hit.
   - fnPlanLineageReplay: stack_swap_bottom_extension (d < LENGTH S).
   - fnPlanLineagePhiTemporal: stack_poke_bottom_extension and
     stack_pop_bottom_extension (pop count <= LENGTH S), plus state frames.
   The actual ordinary searches are exact equality (stack_get_depth and
   stack_get_unfixed_depth), NOT operand_equiv search. operand_equiv is
   consulted at the target slot by reorder_one and in optimistic_swap's
   early exit; these tests must use the same actual target cells.

   Execution-order audit of generate_regular_inst_plan:
   1. emit_input_plan restores spills by exact key, so both spill maps and
      allocators must agree. Literals/labels append common cells. Live Var
      DUP needs a suffix hit after restoration, as proved above; deep DUP
      additionally reads a top window of d-15 cells. A hit gives d<LENGTH S,
      hence that window is within S. Dead Vars are not materialized here.
      FIRST unsupported read absent extra premises: a live Var not restored
      and absent from S can be found in only one prefix. No native ordinary
      operand coverage producer has been proved in this component.
   2. JMP join restore uses common exact spill keys. Reorder then needs
      suffix-local unfixed hits and target window LENGTH targets <= LENGTH S.
   3. Both commutative dry runs need those same premises for their respective
      target orders; equal cost is not enough without equal dry-run ops.
      reorder_one's target operand_equiv test is confined if final_dist is
      below LENGTH S. If a hit has dist>16, S has at least 18 cells, so the
      select_spill_candidate offsets 0..16 are initially confined. After
      each spill the new suffix/window invariant and a sufficient recursion
      fuel bound must be proved; LENGTH(P++S) and LENGTH(Q++S) differ. No
      symbolic preservation/fuel producer is claimed here.
   4. Consumed pop requires LENGTH operands <= LENGTH current S; output
      pushes then extend the common suffix. The ASSIGN theorem above checks
      this actual pipeline with arbitrary lower prefix and untouched suffix.
   5. generate_emit_ops does not inspect the stack. INVOKE and
      ASSERT_UNREACHABLE use the label counter; equal label bookkeeping is
      needed in addition to alloc/spilled equality. INITIAL_FMP/BUMP emit
      fixed ops; their planner outputs still participate in stack edits.
   6. Dead-output popmany needs its actual exact hits (including repeated
      sequential searches) in the suffix and enough cells for each pop.
      Its contiguous branch swaps at depth n and pops n: n<LENGTH S is
      needed, not merely n<=LENGTH S. SSA/distinct outputs may supply part
      of this producer, but no such native producer is established here.
   7. optimistic_swap uses exact lookup of LAST next_liveness after its
      operand_equiv early exit. The obstruction above has next=[x;y], so
      output x is live and the regular pipeline's live_outs guard does NOT
      disable this branch. Shared suffix [Var x] is insufficient. A hit
      for y in S would shield it; a miss needs y absent in BOTH prefixes
      (or a separately proved equal harmless observation). Coverage by
      S OR spilled is not enough: this stage does not restore y. A native
      invariant must also exclude stale prefix copies of spilled live y.
      Empty S is not automatically safe either; an enabled lookup can read
      P/Q directly. In reachable regular states a retained live output
      should make S nonempty, but this remains a producer obligation.
   8. release_dead_spills reads the entire persistent spill map and frees
      its selected offsets. Equal allocators alone are insufficient; equal
      maps make its deterministic fold agree. Successful join spill reset
      was proved elsewhere, but preservation through ordinary selective
      spills is not established by the present boundary probes.

   generate_inst_plan dispatch is separate: PHI uses accepted native
   schedule boundaries; OFFSET inspects two operands, emits SOPushOfst,
   and pushes Var output (not the regular reorder pipeline); param/NOP are noops;
   pre-codegen/malformed INVOKE reject; other opcodes use regular planning
   and JMP additionally tests join_reached on the resulting stack.

   Outcome: checked shallow input and one whole regular consumer boundary,
   plus a symbolic optimistic-swap obstruction with arbitrary prefixes.
   No claim of native reachability, a frozen-task counterexample, universal
   ordinary replay, or equality of whole stacks follows from these probes.
*)
