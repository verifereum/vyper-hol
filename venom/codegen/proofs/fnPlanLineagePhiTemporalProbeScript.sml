Theory fnPlanLineagePhiTemporalProbe
Ancestors
  fnPlanLineagePhiSlots fnPlanLineagePhiMaps fnPlanLineageLiveness
  stackPlanGen livenessDefs

(* Finite local PHI-prefix experiment, not globally ready functions.
   Entry order is produced by backward transfer, never hand-selected. *)
Definition temporal_phis_def:
  temporal_phis bs =
    [mk_inst 0 PHI [Label "entry";Var "a0";Label "back";Var (EL 0 bs)] ["x0"];
     mk_inst 1 PHI [Label "entry";Var "a1";Label "back";Var (EL 1 bs)] ["x1"];
     mk_inst 2 PHI [Label "entry";Var "a2";Label "back";Var (EL 2 bs)] ["x2"]]
End

Definition temporal_live_def:
  temporal_live phis terminal = FOLDR (liveness_transfer []) terminal phis
End

Definition temporal_entry_def:
  temporal_entry edge phis terminal =
    (init_plan_state 0) with ps_stack :=
      MAP Var (input_vars_from edge phis (temporal_live phis terminal))
End

(* Observe incoming first hit, selected-value liveness, and the output hit
   after writing but BEFORE the dead-output pop. Retain every physical cell. *)
Definition temporal_observe_def:
  temporal_observe inst live ps =
    case stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack of
      NONE => (NONE,F,NONE)
    | SOME d =>
        let dup = MEM (operand_to_string (stack_peek d ps.ps_stack)) live in
        let written = if dup then
          stack_poke 0 (Var (HD inst.inst_outputs)) (SND (do_dup d ps)).ps_stack
          else stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack in
        (SOME d,dup,stack_get_depth (Var (HD inst.inst_outputs)) written)
End

Definition temporal_trace_def:
  (temporal_trace [] terminal ps = []) /\
  (temporal_trace (inst::rest) terminal ps =
    let live = temporal_live rest terminal in
    let result = generate_phi_plan inst live F ps in
    (FST result, temporal_observe inst live ps, (SND result).ps_alloc) ::
      temporal_trace rest terminal (SND result))
End

Definition temporal_check_def:
  temporal_check bs terminal =
    let phis = temporal_phis bs in
    (phi_uses_disjoint phis /\
     EVERY (\phi. EVERY (\v. ~MEM v terminal) (inst_uses phi)) phis) ==>
    temporal_trace phis terminal (temporal_entry "entry" phis terminal) =
    temporal_trace phis terminal (temporal_entry "back" phis terminal)
End

Definition temporal_choices_def:
  temporal_choices = ["x0";"x1";"x2";"b0";"b1";"b2"]
End

Definition temporal_chunk_def:
  temporal_chunk b terminal =
    EVERY (\c. EVERY (\d. temporal_check [b;c;d] terminal)
      temporal_choices) temporal_choices
End

(* Separate computational chunks keep each EVAL invocation bounded. *)
Theorem temporal_family_x0[local]:
  temporal_chunk "x0" []
Proof
  EVAL_TAC
QED

Theorem temporal_family_x1[local]:
  temporal_chunk "x1" []
Proof
  EVAL_TAC
QED

Theorem temporal_family_x2[local]:
  temporal_chunk "x2" []
Proof
  EVAL_TAC
QED

Theorem temporal_family_b0[local]:
  temporal_chunk "b0" []
Proof
  EVAL_TAC
QED

Theorem temporal_family_b1[local]:
  temporal_chunk "b1" []
Proof
  EVAL_TAC
QED

Theorem temporal_family_b2[local]:
  temporal_chunk "b2" []
Proof
  EVAL_TAC
QED

Theorem temporal_family:
  EVERY (\b. temporal_chunk b []) temporal_choices
Proof
  simp[temporal_choices_def, temporal_family_x0, temporal_family_x1,
       temporal_family_x2, temporal_family_b0, temporal_family_b1,
       temporal_family_b2]
QED
(* A terminal output may be live only when it is not an incoming name. *)
Theorem temporal_live_output_readiness:
  phi_uses_disjoint (temporal_phis ["b0";"x0";"x1"]) /\
  EVERY (\phi. EVERY (\v. ~MEM v ["x2"]) (inst_uses phi))
    (temporal_phis ["b0";"x0";"x1"]) /\
  temporal_check ["b0";"x0";"x1"] ["x2"] /\
  ~EVERY (\phi. EVERY (\v. ~MEM v ["x0"]) (inst_uses phi))
    (temporal_phis ["x1";"x2";"x0"])
Proof
  EVAL_TAC
QED

Theorem temporal_cycle_entry:
  temporal_live (temporal_phis ["x1";"x2";"x0"]) [] =
    ["a2";"a1";"x2";"a0";"x1"] /\
  (temporal_entry "entry" (temporal_phis ["x1";"x2";"x0"]) []).ps_stack =
    [Var "a2";Var "a1";Var "a0"] /\
  (temporal_entry "back" (temporal_phis ["x1";"x2";"x0"]) []).ps_stack =
    [Var "x0";Var "x2";Var "x1"]
Proof
  EVAL_TAC
QED

Definition temporal_summary_def:
  temporal_summary bs terminal edge =
    MAP (\(ops,obs,alloc). (ops,obs))
      (temporal_trace (temporal_phis bs) terminal
        (temporal_entry edge (temporal_phis bs) terminal))
End

Theorem temporal_cycle_stages:
  temporal_summary ["x1";"x2";"x0"] [] "entry" =
    [([SOPoke 0 (Var "x0")], SOME 0,F,SOME 0);
     ([SOPoke 1 (Var "x1"); SOSwap 1; SOPop 1], SOME 1,F,SOME 1);
     ([SOPoke 0 (Var "x2"); SOPop 1], SOME 0,F,SOME 0)]
Proof
  EVAL_TAC
QED

Theorem temporal_other_stages:
  MAP (\bs. temporal_summary bs [] "entry")
    [["x0";"x1";"x2"];["x1";"x0";"x2"];["b0";"x0";"x1"]] =
    [[([SOPoke 0 (Var "x0"); SOPop 1], SOME 0,F,SOME 0);
      ([SOPoke 0 (Var "x1"); SOPop 1], SOME 0,F,SOME 0);
      ([SOPoke 0 (Var "x2"); SOPop 1], SOME 0,F,SOME 0)];
     [([SOPoke 0 (Var "x0")], SOME 0,F,SOME 0);
      ([SOPoke 0 (Var "x1"); SOPop 1], SOME 0,F,SOME 0);
      ([SOPoke 1 (Var "x2"); SOSwap 1; SOPop 1], SOME 1,F,SOME 1)];
     [([SOPoke 0 (Var "x0")], SOME 0,F,SOME 0);
      ([SOPoke 0 (Var "x1")], SOME 0,F,SOME 0);
      ([SOPoke 0 (Var "x2"); SOPop 1], SOME 0,F,SOME 0)]]
Proof
  EVAL_TAC
QED

Theorem temporal_live_stages:
  temporal_summary ["b0";"x0";"x1"] ["x2"] "entry" =
    [([SOPoke 0 (Var "x0")], SOME 0,F,SOME 0);
     ([SOPoke 0 (Var "x1")], SOME 0,F,SOME 0);
     ([SOPoke 0 (Var "x2")], SOME 0,F,SOME 0)]
Proof
  EVAL_TAC
QED

(* Premise-producer ledger and bounded output-search audit (.17).

   Checked family: all 6^3 back-edge triples; the disjoint-use guard filters
   repeated class names. Both traces compare the operations, selected-value
   next-live membership, incoming first-hit and post-write output first-hit,
   and the complete allocator at EVERY stage, not just at completion.

   Case                 incoming depths    output-hit depths   dead pops
   identity             0,0,0              0,0,0               0,1,2
   transposition        0,0,1              0,0,1               1,2
   three-cycle          0,1,0              0,1,0               1,2
   chain                0,0,0              0,0,0               2
   chain, x2 live       0,0,0              0,0,0               none

   Selected-value live flags are F in these exact stage tables. The inserted
   output is the first occurrence whenever popped; a deeper write gives the
   explicitly recorded SOSwap. In the cycle x0 survives stage 0 because a
   later PHI uses it. In the chain, the newly common x0 and then x1 shadow
   still-existing unequal original cells on BOTH edges. No cell is removed
   from the model except by the actual generate_phi_plan operation.

   Producer                           Status
   entry list/order                   actual backward transfer + input_vars_from
   incoming disjointness              evaluated for each accepted family member
   terminal incoming-name absence     evaluated, including live-output variant
   selected incoming death            .16 universal analyzed boundary available
   paired top-first/output-hit equality checked finite family only
   universal ordering/shielding        STILL MISSING
   arbitrary residual exclusion        STILL MISSING
   deep DUP/spill-window replay        NOT TESTED by these shallow prefixes
   whole-function reachable producer  NOT CLAIMED

   Proposed universal assertion requiring proof: before a dead output pop,
   there is no unmatched old output occurrence above the common newly written
   cell. Transfer ordering and future-use liveness support it in the checked
   examples, but these equations do not prove it for arbitrary PHI prefixes,
   opaque lower residuals, or persistent spills. Ancestor strategy review is
   required before promoting this experiment to a preservation invariant.
*)
