(*
 * Pass Shared Properties
 *
 * Correctness theorems for pass-shared utilities (mk_nop_inst,
 * mk_assign_inst, clear_nops, subst_operands, subst_operands_map)
 * and general semantic properties used by multiple passes
 * (effects_independent_commute).
 *
 * TOP-LEVEL:
 *   Instruction builders:
 *     mk_nop_inst_correct        — NOP replacement is identity on state
 *     mk_assign_inst_correct     — ASSIGN replacement evaluates and binds output
 *
 *   NOP clearing:
 *     clear_nops_block_correct    — removing NOPs from a block preserves execution
 *     clear_nops_function_correct — removing NOPs from a function preserves execution
 *
 *   Operand substitution:
 *     subst_operand_eval           — single substitution preserves eval_operand
 *     subst_op_map_eval            — map substitution preserves eval_operand
 *     subst_operand_eval_operands  — single substitution preserves eval_operands (list)
 *     subst_op_map_eval_operands   — map substitution preserves eval_operands (list)
 *     subst_operands_correct       — single substitution preserves step_inst
 *     subst_operands_map_correct   — map substitution preserves step_inst
 *
 *   Effect independence:
 *     effects_independent_commute — data+effect independent instructions commute
 *)

Theory passSharedProps
Ancestors
  passSharedDefs venomExecSemantics venomEffects stateEquiv

(* ===================================================================== *)
(* ===== Section 1: Instruction Builder Correctness ==================== *)
(* ===================================================================== *)

(* NOP replacement always succeeds with unchanged state.
   mk_nop_inst sets opcode to NOP; NOP => OK s in step_inst_base. *)
Theorem mk_nop_inst_correct:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  cheat
QED

(* ASSIGN replacement evaluates src_op and binds the result to the
   single output variable. Requires src_op evaluable and exactly one output. *)
Theorem mk_assign_inst_correct:
  !fuel ctx inst src_op s v out.
    eval_operand src_op s = SOME v /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx (mk_assign_inst inst src_op) s =
      OK (update_var out v s)
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 2: NOP Clearing ======================================= *)
(* ===================================================================== *)

(* Removing NOP instructions from a block preserves execution.
   NOP always succeeds with unchanged state (step_inst NOP s = OK s)
   and is not a terminator, so run_block just advances vs_inst_idx
   past it. FILTER-ing NOPs from the instruction list produces the
   same execution result as running the block with NOPs present.

   Proof sketch: by induction on the block execution (fuel +
   instruction count). At each step:
   - If current instruction is NOP: step gives OK s, then recurse
     at next index. Equivalent to skipping it in the filtered list.
   - If current instruction is not NOP: same instruction appears at
     the corresponding index in the filtered list. Same step result.
   The filtered block's indices are a subsequence of the original. *)
Theorem clear_nops_block_correct:
  !fuel ctx bb s.
    s.vs_inst_idx = 0 ==>
    run_block fuel ctx (clear_nops_block bb) s =
    run_block fuel ctx bb s
Proof
  cheat
QED

(* Function-level: clear_nops_function preserves execution.
   Follows from clear_nops_block_correct applied to each block.
   clear_nops_block preserves bb_label, so block lookup is unchanged. *)
Theorem clear_nops_function_correct:
  !fuel ctx fn s.
    s.vs_inst_idx = 0 ==>
    run_function fuel ctx (clear_nops_function fn) s =
    run_function fuel ctx fn s
Proof
  cheat
QED

(* Corollary: wrapping any function transform with clear_nops_function
   preserves lift_result. If the un-cleared transform is correct,
   the cleared version is too. *)
Theorem clear_nops_lift_result:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx fn fn' s.
    s.vs_inst_idx = 0 /\
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s) ==>
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx (clear_nops_function fn') s)
Proof
  rpt strip_tac >>
  `run_function fuel ctx (clear_nops_function fn') s =
   run_function fuel ctx fn' s` by
    (irule clear_nops_function_correct >> simp[]) >>
  gvs[]
QED

(* ===================================================================== *)
(* ===== Section 3: Operand Substitution =============================== *)
(* ===================================================================== *)

(* Substituting a variable with an equal-valued operand preserves
   eval_operand for any operand. Covers Var (with/without match),
   Lit (unchanged), and Label (both NONE). *)
Theorem subst_operand_eval:
  !old new_op op s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operand (subst_operand old new_op op) s = eval_operand op s
Proof
  cheat
QED

(* Multi-variable substitution via fmap preserves eval_operand when
   every mapped variable is replaced by an equal-valued operand. *)
Theorem subst_op_map_eval:
  !subs op s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operand (subst_op_map subs op) s = eval_operand op s
Proof
  cheat
QED

(* Corollary: substitution preserves eval_operands (list version) *)
Theorem subst_operand_eval_operands:
  !old new_op ops s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operands (MAP (subst_operand old new_op) ops) s =
    eval_operands ops s
Proof
  cheat
QED

(* Corollary: map substitution preserves eval_operands (list version) *)
Theorem subst_op_map_eval_operands:
  !subs ops s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operands (MAP (subst_op_map subs) ops) s =
    eval_operands ops s
Proof
  cheat
QED

(* Single-variable operand substitution preserves step_inst when the
   replacement evaluates to the same defined value. Requires both sides
   SOME to prevent Var→Label structural changes (which break INVOKE's
   decode_invoke and DJMP's extract_labels). Excludes PHI (positional
   operand semantics: Label/Var pairs indexed by predecessor block). *)
Theorem subst_operands_correct:
  !fuel ctx inst s old new_op v.
    lookup_var old s = SOME v /\
    eval_operand new_op s = SOME v /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands old new_op inst) s =
    step_inst fuel ctx inst s
Proof
  cheat
QED

(* Multi-variable operand substitution preserves step_inst when all
   replacements evaluate to the same defined values. IS_SOME prevents
   Label substitutions. Excludes PHI. *)
Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                IS_SOME (eval_operand new_op s) /\
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 4: Effect Independence ================================ *)
(* ===================================================================== *)

(* Instructions with independent effects and no data dependencies
   (no output-to-operand or output-to-output aliasing) commute
   under step_inst. Generalizes dftCorrectness.independent_commute. *)
Theorem effects_independent_commute:
  !fuel ctx inst1 inst2 s.
    (* No data dependency: outputs don't feed operands *)
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    (* No output aliasing *)
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    (* No effect conflict *)
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    (* Neither is a terminator (terminators transfer control) *)
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode ==>
    (case step_inst fuel ctx inst1 s of
       OK s1 => step_inst fuel ctx inst2 s1
     | other => other)
    =
    (case step_inst fuel ctx inst2 s of
       OK s2 => step_inst fuel ctx inst1 s2
     | other => other)
Proof
  cheat
QED
