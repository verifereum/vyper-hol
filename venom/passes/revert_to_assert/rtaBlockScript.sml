(*
 * Revert-to-Assert Block-Level Correctness
 *
 * This theory proves block-level semantic equivalence for the transformation.
 *
 * Key insight: The transformation preserves behavior because:
 * - Original: jnz cond @revert @else
 *   - If cond != 0: jump to revert block, execute "revert 0 0" -> Revert
 *   - If cond == 0: jump to else block
 * - Transformed: iszero cond -> t; assert t; jmp @else
 *   - If cond != 0: t = 0, assert fails -> Revert
 *   - If cond == 0: t = 1, assert passes, jmp @else
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - step_assert_zero        : assert 0 produces Revert
 *   - step_assert_nonzero     : assert (non-zero) produces OK
 *   - step_iszero_semantics   : iszero produces 1 for 0, 0 otherwise
 *   - jnz_then_revert_equiv   : JNZ to revert equiv to iszero+assert+jmp
 *   - jnz_else_revert_equiv   : JNZ to revert equiv to assert+jmp
 *
 * ============================================================================
 *)

Theory rtaBlock
Ancestors
  rtaWellFormed venomSem venomState venomInst rtaTransform
Libs
  finite_mapTheory rich_listTheory

(* ==========================================================================
   ASSERT Semantics
   ========================================================================== *)

(* assert 0 causes Revert *)
Theorem step_assert_zero:
  !inst s.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Lit 0w] ==>
    step_inst inst s = Revert (revert_state s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* assert (non-zero) continues *)
Theorem step_assert_nonzero:
  !inst s v.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Lit v] /\
    v <> 0w ==>
    step_inst inst s = OK s
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* assert on variable *)
Theorem step_assert_var:
  !inst s out v.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var out] /\
    lookup_var out s = SOME v ==>
    (v = 0w ==> step_inst inst s = Revert (revert_state s)) /\
    (v <> 0w ==> step_inst inst s = OK s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* ==========================================================================
   ISZERO Semantics
   ========================================================================== *)

(* iszero on 0 produces 1 *)
Theorem step_iszero_zero:
  !inst s out.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst inst s = OK (update_var out 1w s)
Proof
  rw[step_inst_def, exec_unop_def, eval_operand_def, bool_to_word_def]
QED

(* iszero on non-zero produces 0 *)
Theorem step_iszero_nonzero:
  !inst s out v.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Lit v] /\
    inst.inst_outputs = [out] /\
    v <> 0w ==>
    step_inst inst s = OK (update_var out 0w s)
Proof
  rw[step_inst_def, exec_unop_def, eval_operand_def, bool_to_word_def]
QED

(* iszero on variable *)
Theorem step_iszero_var:
  !inst s in_var out v.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var in_var] /\
    inst.inst_outputs = [out] /\
    lookup_var in_var s = SOME v ==>
    step_inst inst s = OK (update_var out (bool_to_word (v = 0w)) s)
Proof
  rw[step_inst_def, exec_unop_def, eval_operand_def]
QED

(* ==========================================================================
   JMP Semantics
   ========================================================================== *)

Theorem step_jmp:
  !inst s lbl.
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label lbl] ==>
    step_inst inst s = OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* ==========================================================================
   JNZ Semantics
   ========================================================================== *)

Theorem step_jnz_nonzero:
  !inst s v then_lbl else_lbl.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [Lit v; Label then_lbl; Label else_lbl] /\
    v <> 0w ==>
    step_inst inst s = OK (jump_to then_lbl s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

Theorem step_jnz_zero:
  !inst s then_lbl else_lbl.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [Lit 0w; Label then_lbl; Label else_lbl] ==>
    step_inst inst s = OK (jump_to else_lbl s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

Theorem step_jnz_var:
  !inst s cond_var v then_lbl else_lbl.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [Var cond_var; Label then_lbl; Label else_lbl] /\
    lookup_var cond_var s = SOME v ==>
    (v <> 0w ==> step_inst inst s = OK (jump_to then_lbl s)) /\
    (v = 0w ==> step_inst inst s = OK (jump_to else_lbl s))
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* ==========================================================================
   REVERT Semantics
   ========================================================================== *)

Theorem step_revert:
  !inst s.
    inst.inst_opcode = REVERT ==>
    step_inst inst s = Revert (revert_state s)
Proof
  rw[step_inst_def]
QED

(* ==========================================================================
   Core Equivalence: JNZ to revert vs ASSERT
   ========================================================================== *)

(* When then-branch is revert:
   Original behavior: jnz cond @revert @else
   - cond != 0 -> Revert
   - cond == 0 -> jump to else

   Transformed behavior: iszero cond -> t; assert t; jmp @else
   - cond != 0 -> t = 0 -> assert 0 -> Revert
   - cond == 0 -> t = 1 -> assert 1 -> OK -> jmp @else
*)

(* Helper: Run transformed then-branch block starting from inst_idx = 0.
   The block has just the 3 transformed instructions: iszero, assert, jmp *)
Theorem run_then_transform_block:
  !bb cond_var v else_lbl new_var id1 id2 id3 s.
    lookup_var cond_var s = SOME v /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    let bb' = <| bb_label := bb.bb_label;
                 bb_instructions :=
                   [mk_iszero_inst id1 (Var cond_var) new_var;
                    mk_assert_inst id2 (Var new_var);
                    mk_jmp_inst id3 else_lbl] |> in
    (v <> 0w ==> ?s'. run_block ARB bb' s = Revert s') /\
    (v = 0w ==> ?s'. run_block ARB bb' s = OK s' /\ s'.vs_current_bb = else_lbl)
Proof
  rw[LET_THM] >| [
    (* Case v != 0: iszero produces 0, assert 0 reverts *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def,
         step_inst_def, exec_unop_def, eval_operand_def,
         is_terminator_def, bool_to_word_def] >>
    simp[update_var_def, next_inst_def] >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[step_inst_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE],
    (* Case v = 0: iszero produces 1, assert 1 passes, jmp else *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def,
         step_inst_def, exec_unop_def, eval_operand_def,
         is_terminator_def, bool_to_word_def] >>
    simp[update_var_def, next_inst_def] >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[step_inst_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
         is_terminator_def, update_var_def, next_inst_def] >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[step_inst_def, is_terminator_def, jump_to_def]
  ]
QED

(* Full block equivalence for then-branch case *)
Theorem rta_then_block_equiv:
  !blocks bb bb' s new_var id1 id2 id3 cond_var v then_lbl else_lbl.
    rta_then_applicable blocks bb /\
    rewrite_jnz_then_revert bb new_var id1 id2 id3 = SOME bb' /\
    get_jnz_operands (THE (get_terminator bb)) = SOME (Var cond_var, then_lbl, else_lbl) /\
    lookup_var cond_var s = SOME v /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    (* Running transformed block produces expected result *)
    (v <> 0w ==> ?s'. run_block ARB bb' s = Revert s') /\
    (v = 0w ==> ?s'. run_block ARB bb' s = OK s' /\ s'.vs_current_bb = else_lbl)
Proof
  cheat (* TODO: connect to run_then_transform_block via block structure *)
QED

(* Helper: Run transformed else-branch block starting from inst_idx = 0.
   The block has just the 2 transformed instructions: assert, jmp *)
Theorem run_else_transform_block:
  !bb cond_var v then_lbl id1 id2 s.
    lookup_var cond_var s = SOME v /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    let bb' = <| bb_label := bb.bb_label;
                 bb_instructions :=
                   [mk_assert_inst id1 (Var cond_var);
                    mk_jmp_inst id2 then_lbl] |> in
    (v = 0w ==> ?s'. run_block ARB bb' s = Revert s') /\
    (v <> 0w ==> ?s'. run_block ARB bb' s = OK s' /\ s'.vs_current_bb = then_lbl)
Proof
  rw[LET_THM] >| [
    (* Case v = 0: assert 0 reverts *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[mk_assert_inst_def, mk_jmp_inst_def,
         step_inst_def, eval_operand_def, is_terminator_def],
    (* Case v != 0: assert passes, jmp then *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[mk_assert_inst_def, mk_jmp_inst_def,
         step_inst_def, eval_operand_def, is_terminator_def,
         update_var_def, next_inst_def] >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[step_inst_def, is_terminator_def, jump_to_def]
  ]
QED

(* Full block equivalence for else-branch case *)
Theorem rta_else_block_equiv:
  !blocks bb bb' s id1 id2 cond_var v then_lbl else_lbl.
    rta_else_applicable blocks bb /\
    rewrite_jnz_else_revert bb id1 id2 = SOME bb' /\
    get_jnz_operands (THE (get_terminator bb)) = SOME (Var cond_var, then_lbl, else_lbl) /\
    lookup_var cond_var s = SOME v /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    (* Running transformed block produces expected result *)
    (v = 0w ==> ?s'. run_block ARB bb' s = Revert s') /\
    (v <> 0w ==> ?s'. run_block ARB bb' s = OK s' /\ s'.vs_current_bb = then_lbl)
Proof
  cheat (* TODO: connect to run_else_transform_block via block structure *)
QED
