(*
 * Counterexamples for FALSE stack order theorems.
 *
 * so_needed_are_live_proof and so_get_stack_sound_proof are FALSE.
 *
 * Key insight: so_analyze_block tracks stack layout (what operands need
 * to be available), NOT liveness. A variable defined and consumed within
 * a block gets popped from the simulated stack. If a successor also needs
 * that variable (via from_to), the terminator re-adds it to needed.
 * But the variable is NOT live at block entry — its definition kills it.
 *
 * Full mechanical counterexample requires computing liveness_analyze
 * (worklist fixpoint) and cfg_analyze (DFS), which EVAL cannot reduce.
 * Key lemmas are proved mechanically below.
 *)

Theory stackOrderCex
Ancestors
  stackOrderDefs livenessDefs passSharedDefs
Libs
  finite_mapTheory listTheory

(* =====================================================================
   KEY LEMMA 1: so_analyze_block puts "x" in needed
   =====================================================================

   Block A: inst0 (MSIZE, outputs=["x"]), inst1 (ISZERO, operands=[Var "x"],
   outputs=["y"]), inst2 (JMP, operands=[Label "B"]).

   With from_to("A","B") = ["x"], so_analyze_block returns needed=["x"].
   Variable "x" is defined at inst0, consumed at inst1 (popped from stack),
   then re-requested by the JMP terminator (from from_to). *)

Definition cex_inst0_def:
  cex_inst0 = <| inst_id := 0; inst_opcode := MSIZE;
                 inst_operands := []; inst_outputs := ["x"] |>
End

Definition cex_inst1_def:
  cex_inst1 = <| inst_id := 1; inst_opcode := ISZERO;
                 inst_operands := [Var "x"]; inst_outputs := ["y"] |>
End

Definition cex_inst2_def:
  cex_inst2 = <| inst_id := 2; inst_opcode := JMP;
                 inst_operands := [Label "B"]; inst_outputs := [] |>
End

Definition cex_cfg_def:
  cex_cfg = <| cfg_succs := FEMPTY |+ ("A", ["B"]);
               cfg_preds := FEMPTY |+ ("B", ["A"]);
               cfg_reachable := FEMPTY;
               cfg_dfs_post := []; cfg_dfs_pre := [] |>
End

Definition cex_from_to_def:
  cex_from_to = (FEMPTY |+ (("A","B"), ["x"]))
                  : (string # string, string list) fmap
End

Theorem so_analyze_block_cex:
  so_analyze_block cex_cfg ARB cex_from_to "A"
    [cex_inst0; cex_inst1; cex_inst2] = (["x"], [])
Proof
  EVAL_TAC
QED

(* "x" is in the needed list *)
Theorem x_in_needed:
  MEM "x" (FST (so_analyze_block cex_cfg ARB cex_from_to "A"
    [cex_inst0; cex_inst1; cex_inst2]))
Proof
  simp[so_analyze_block_cex]
QED

(* =====================================================================
   KEY LEMMA 2: liveness_transfer kills "x" at inst0

   inst0 = MSIZE with outputs=["x"], so inst_defs inst0 = ["x"].
   liveness_transfer applied to inst0 removes "x" from any live set.
   Therefore "x" cannot be live at block entry (index 0).
   ===================================================================== *)

Theorem inst0_defs_x:
  inst_defs cex_inst0 = ["x"]
Proof
  EVAL_TAC
QED

Theorem inst0_uses_empty:
  inst_uses cex_inst0 = []
Proof
  EVAL_TAC
QED

(* For any live set, liveness_transfer at inst0 kills "x" *)
Theorem liveness_transfer_kills_x:
  ∀bbs live. ¬MEM "x" (liveness_transfer bbs cex_inst0 live)
Proof
  rw[liveness_transfer_def, live_update_def, MEM_APPEND, MEM_FILTER] >>
  simp[inst0_defs_x, inst0_uses_empty]
QED

(* =====================================================================
   KEY LEMMA 3: from_to_wf holds for any lr where "x" is live at B entry

   from_to_wf lr cex_from_to ⟺ MEM "x" (live_vars_at lr "B" 0)

   This is consistent: "x" IS live at B entry (B uses x at inst3).
   The liveness fixpoint for this fn has "x" ∈ live_vars_at lr "B" 0.
   ===================================================================== *)

Theorem from_to_wf_cex:
  !lr. from_to_wf lr cex_from_to = MEM "x" (live_vars_at lr "B" 0)
Proof
  rw[from_to_wf_def, cex_from_to_def, FLOOKUP_UPDATE, live_vars_at_def] >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`"A"`, `"B"`, `["x"]`, `"x"`] mp_tac) >>
  simp[]
QED

(* =====================================================================
   COUNTEREXAMPLE 2: so_get_stack_sound FALSE WITH single_use_form
   =====================================================================

   The ASSIGN handler adds "v" to needed when "v" is live at the NEXT
   instruction (MEM v next_live). But "v" can be defined by an earlier
   instruction in the same block, making it NOT live at block entry.
   single_use_form doesn't prevent this because ASSIGN uses aren't counted.

   Block "succ":
     inst0: MSIZE → v     (defines v)
     inst1: ASSIGN v → w  (ASSIGN, excluded from single_use_form count)
     inst2: ISZERO v → y  (non-ASSIGN, uses v, counted = 1 use)
     inst3: JMP → exit    (terminator)

   single_use_form: var_use_count_block "v" = 1 (only inst2 counted). ✓
   ASSIGN handler at inst1: MEM "v" (live_vars_at lr "succ" 2) → true
     (v used at inst2) → adds "v" to needed.
   Liveness at inst0: defs=["v"], uses=[] → "v" is killed → NOT live at 0.

   Therefore: MEM "v" needed ∧ ¬MEM "v" (live_vars_at lr "succ" 0).
   The needed list gets recorded into from_to via so_record_from_to,
   violating from_to_wf for the new entry.
   ===================================================================== *)

(* Construct explicit lr where live_vars_at lr "succ" 2 = ["v"] *)
Definition cex2_lr_def:
  cex2_lr = <| ds_inst := FEMPTY |+ (("succ", 2:num), ["v":string]);
               ds_boundary := FEMPTY |>
End

Definition cex2_cfg_def:
  cex2_cfg = <| cfg_succs := FEMPTY |+ ("succ", ["exit"]);
                cfg_preds := FEMPTY |+ ("exit", ["succ"]);
                cfg_reachable := FEMPTY;
                cfg_dfs_post := []; cfg_dfs_pre := [] |>
End

Definition cex2_insts_def:
  cex2_insts =
    [<| inst_id := 0; inst_opcode := MSIZE;
        inst_operands := []; inst_outputs := ["v"] |>;
     <| inst_id := 1; inst_opcode := ASSIGN;
        inst_operands := [Var "v"]; inst_outputs := ["w"] |>;
     <| inst_id := 2; inst_opcode := ISZERO;
        inst_operands := [Var "v"]; inst_outputs := ["y"] |>;
     <| inst_id := 3; inst_opcode := JMP;
        inst_operands := [Label "exit"]; inst_outputs := [] |>]
End

(* KEY LEMMA 2a: so_analyze_block with this lr puts "v" in needed *)
Theorem so_analyze_block_cex2:
  so_analyze_block cex2_cfg cex2_lr FEMPTY "succ" cex2_insts =
  (["v"], [Var "w"])
Proof
  EVAL_TAC
QED

Theorem v_in_needed_cex2:
  MEM "v" (FST (so_analyze_block cex2_cfg cex2_lr FEMPTY "succ" cex2_insts))
Proof
  simp[so_analyze_block_cex2]
QED

(* KEY LEMMA 2b: liveness_transfer at inst0 always kills "v" *)
Theorem liveness_transfer_kills_v:
  ∀bbs live.
    ¬MEM "v" (liveness_transfer bbs
      <| inst_id := 0; inst_opcode := MSIZE;
         inst_operands := []; inst_outputs := ["v"] |> live)
Proof
  rw[liveness_transfer_def, live_update_def, MEM_APPEND, MEM_FILTER,
     inst_defs_def, inst_uses_def, operand_vars_def]
QED

(* KEY LEMMA 2c: var_use_count_block for "v" is exactly 1 *)
Theorem single_use_cex2:
  var_use_count_block "v"
    <| bb_label := "succ"; bb_instructions := cex2_insts |> = 1
Proof
  EVAL_TAC
QED

(* KEY LEMMA 2d: from_to_wf lr FEMPTY is trivially true (empty map) *)
Theorem from_to_wf_empty:
  ∀lr. from_to_wf lr FEMPTY
Proof
  rw[from_to_wf_def, FLOOKUP_DEF]
QED

(* =====================================================================
   Summary: so_get_stack_sound is FALSE even with single_use_form.

   Given a function fn with one block "succ" containing cex2_insts,
   if lr = liveness_analyze fn satisfies the fixpoint equation
   (live_vars_at lr "succ" idx = transfer(live_vars_at lr "succ" (idx+1))),
   then:
   - live_vars_at lr "succ" 2 includes "v" (used by ISZERO at inst2)
   - live_vars_at lr "succ" 0 does NOT include "v" (killed by MSIZE at inst0)
   - so_analyze_block produces needed=["v"] (via ASSIGN handler)
   - so_record_from_to writes (pred, "succ") ↦ ["v"] into from_to'
   - from_to_wf lr from_to' requires MEM "v" (live_vars_at lr "succ" 0) — FALSE

   The ALL_DISTINCT part of so_get_stack_sound IS independently provable.
   ===================================================================== *)

(* =====================================================================
   INFORMAL COUNTEREXAMPLE for so_needed_are_live_proof (original, no single_use_form)
   =====================================================================

   Function: blocks A (defines x, uses x, jumps to B) and B (uses x, stops).

   1. so_analyze_block for A with from_to("A","B")=["x"]:
      - inst0 pushes Var "x" onto stack
      - inst1 finds Var "x" on stack, pops it, pushes Var "y"
      - inst2 (JMP): from_to → so_merge [["x"]] = ["x"],
        Var "x" not on stack [Var "y"] → adds "x" to needed
      Result: needed = ["x"]

   2. Liveness at ("A", 0):
      - "x" is live at ("A", 1) — used by inst1
      - inst0 DEFINES "x" (MSIZE outputs=["x"]), killing it
      - So "x" is NOT live at ("A", 0)

   3. from_to_wf holds: "x" IS live at ("B", 0) — B uses x

   Therefore: MEM "x" needed ∧ ¬MEM "x" (live_vars_at lr "A" 0)
   contradicting so_needed_are_live_proof.

   Full mechanical proof would require computing liveness_analyze
   (worklist fixpoint) and cfg_analyze (DFS walk), which EVAL cannot
   fully reduce. The key lemmas above are proved mechanically.

   =====================================================================
   INFORMAL COUNTEREXAMPLE for so_get_stack_sound_proof
   =====================================================================

   so_get_stack_sound_proof claims from_to_wf lr from_to' where from_to'
   is the updated from_to after so_get_stack. This depends on
   so_needed_are_live_proof (needed vars must be live for from_to_wf
   to be preserved when recording them). Since so_needed_are_live_proof
   is false, the same counterexample applies: the needed list ["x"]
   gets recorded into from_to', but "x" is not live at "A" entry,
   violating from_to_wf for the new entry.

   The ALL_DISTINCT part of so_get_stack_sound IS independently provable
   (follows from so_analyze_block_needed_distinct_proof).
   ===================================================================== *)


