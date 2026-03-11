(*
 * Branch Optimization Pass — Definitions
 *
 * Ports vyper/venom/passes/branch_optimization.py to HOL4.
 *
 * Optimizes JNZ branches by comparing liveness at each successor:
 *   - If condition comes from ISZERO and fst is more live: remove ISZERO,
 *     swap branches (uses original condition directly)
 *   - If fst is more live or ISZERO preferred: insert ISZERO, swap branches
 *
 * The heuristic reduces register pressure by swapping so the less-live
 * successor is the fall-through path.
 *
 * Uses DFG (get_producing_instruction), liveness (live count at successors),
 * and CFG (successor blocks).
 *
 * TOP-LEVEL:
 *   is_cmp_opcode            — comparator opcode check
 *   prefer_iszero_op         — heuristic: would benefit from iszero
 *   branch_opt_inst          — per-instruction transform
 *   branch_opt_block         — block-level transform
 *   branch_opt_function      — function-level transform
 *
 * Helper:
 *   bo_fresh_var             — fresh variable for inserted ISZERO
 *
 * Source: vyper/venom/passes/branch_optimization.py
 *)

Theory branchOptDefs
Ancestors
  passSimulationDefs dfgDefs venomExecSemantics venomInst

(* ===== Comparator Opcodes ===== *)

(* Python: COMPARATOR_INSTRUCTIONS = ("gt", "lt", "sgt", "slt") *)
Definition is_cmp_opcode_def:
  is_cmp_opcode (GT : opcode) = T /\
  is_cmp_opcode LT = T /\
  is_cmp_opcode SGT = T /\
  is_cmp_opcode SLT = T /\
  is_cmp_opcode _ = F
End

(* Python: prefer_iszero checks if an instruction could benefit from iszero.
   EQ always prefers; comparators prefer when they have a literal operand. *)
Definition prefer_iszero_op_def:
  prefer_iszero_op inst =
    if inst.inst_opcode = EQ then T
    else if is_cmp_opcode inst.inst_opcode then
      EXISTS (\op. case op of Lit _ => T | _ => F) inst.inst_operands
    else F
End

(* ===== Fresh Variable ===== *)

Definition bo_fresh_var_def:
  bo_fresh_var (id:num) = STRCAT "bo_tmp_" (toString id)
End

(* ===== Per-Block Transform ===== *)

(*
 * Transform the last instruction of a block if it's a JNZ.
 *
 * Parameters:
 *   dfg       — DFG analysis for finding producing instructions
 *   live_at   — maps block label to cardinality of live vars at entry
 *   block     — basic block to transform
 *
 * The transform examines the JNZ terminator:
 *   jnz %cond, @fst, @snd
 *
 * Case 1: cond comes from ISZERO and |live(fst)| >= |live(snd)|
 *   Remove ISZERO: use ISZERO's input directly, swap branches
 *   Result: jnz %iszero_input, @snd, @fst
 *
 * Case 2: |live(fst)| > |live(snd)| OR
 *          (|live(fst)| >= |live(snd)| AND prefer_iszero(producing_inst))
 *   Insert ISZERO: swap branches
 *   Result: %tmp = iszero %cond; jnz %tmp, @snd, @fst
 *)
Definition branch_opt_block_def:
  branch_opt_block dfg (live_at : string -> num) bb =
    if NULL bb.bb_instructions then bb
    else
      let term = LAST bb.bb_instructions in
        if term.inst_opcode <> JNZ then bb
        else case term.inst_operands of
          [cond_op; Label fst_lbl; Label snd_lbl] =>
            (* Python cfg_out reverses out_bbs, so fst=if_zero, snd=if_nonzero.
               JNZ operands: [cond; if_nonzero(fst_lbl); if_zero(snd_lbl)].
               cost_a = liveness of Python's fst = if_zero = snd_lbl *)
            let cost_a = live_at snd_lbl in
            let cost_b = live_at fst_lbl in
            (case cond_op of
               Var v =>
                 (case dfg_get_def dfg v of
                    SOME prev_inst =>
                      if cost_a >= cost_b /\ prev_inst.inst_opcode = ISZERO then
                        (* Case 1: remove iszero, swap branches *)
                        let new_cond = HD prev_inst.inst_operands in
                        let new_term = term with inst_operands :=
                          [new_cond; Label snd_lbl; Label fst_lbl] in
                        bb with bb_instructions :=
                          FRONT bb.bb_instructions ++ [new_term]
                      else if cost_a > cost_b \/
                              (cost_a >= cost_b /\ prefer_iszero_op prev_inst) then
                        (* Case 2: insert iszero, swap branches *)
                        let id = term.inst_id in
                        let tmp = bo_fresh_var id in
                        let iz = <| inst_id := id;
                                    inst_opcode := ISZERO;
                                    inst_operands := [cond_op];
                                    inst_outputs := [tmp] |> in
                        let new_term = term with inst_operands :=
                          [Var tmp; Label snd_lbl; Label fst_lbl] in
                        bb with bb_instructions :=
                          FRONT bb.bb_instructions ++ [iz; new_term]
                      else bb
                  | NONE => bb)
             | _ => bb)
        | _ => bb
End

(* ===== Function-Level Transform ===== *)

(*
 * Transform a function: build DFG, compute liveness, apply branch_opt
 * to each block.
 *
 * live_at is computed externally (from liveness analysis) and passed in.
 * This avoids circular dependency between pass defs and analysis defs.
 *)
Definition branch_opt_function_def:
  branch_opt_function (live_at : string -> num) fn =
    let dfg = dfg_build_function fn in
    fn with fn_blocks :=
      MAP (branch_opt_block dfg live_at) fn.fn_blocks
End

(* ===== Fresh Variable Tracking ===== *)

Definition bo_fresh_vars_fn_def:
  bo_fresh_vars_fn fn =
    BIGUNION (set (MAP (\bb.
      if NULL bb.bb_instructions then {}
      else
        let term = LAST bb.bb_instructions in
        if term.inst_opcode = JNZ then {bo_fresh_var term.inst_id}
        else {})
      fn.fn_blocks))
End
