(*
 * Revert-to-Assert Well-Formedness Predicates
 *
 * This theory defines well-formedness conditions for the revert-to-assert pass.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - rta_applicable         : Predicate for when transform applies to a block
 *   - rta_then_applicable    : JNZ then-branch goes to revert
 *   - rta_else_applicable    : JNZ else-branch goes to revert
 *
 * ============================================================================
 *)

Theory rtaWellFormed
Ancestors
  rtaTransform venomInst

(* ==========================================================================
   Applicability Predicates
   ========================================================================== *)

(* The transform applies to then-branch: jnz cond @revert @else *)
Definition rta_then_applicable_def:
  rta_then_applicable blocks bb <=>
    case get_terminator bb of
      NONE => F
    | SOME term =>
        is_jnz_inst term /\
        case get_jnz_operands term of
          NONE => F
        | SOME (cond_op, then_lbl, else_lbl) =>
            is_revert_label then_lbl blocks
End

(* The transform applies to else-branch: jnz cond @then @revert *)
Definition rta_else_applicable_def:
  rta_else_applicable blocks bb <=>
    case get_terminator bb of
      NONE => F
    | SOME term =>
        is_jnz_inst term /\
        case get_jnz_operands term of
          NONE => F
        | SOME (cond_op, then_lbl, else_lbl) =>
            ~is_revert_label then_lbl blocks /\
            is_revert_label else_lbl blocks
End

(* The transform applies to either branch *)
Definition rta_applicable_def:
  rta_applicable blocks bb <=>
    rta_then_applicable blocks bb \/
    rta_else_applicable blocks bb
End

(* ==========================================================================
   Revert Block Properties
   ========================================================================== *)

(* A revert block has exactly one instruction which is revert 0 0 *)
Theorem is_revert_block_single_inst:
  !bb. is_revert_block bb ==>
       ?inst. bb.bb_instructions = [inst] /\ is_zero_revert_inst inst
Proof
  rw[is_revert_block_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* revert 0 0 is a terminator *)
Theorem is_zero_revert_terminator:
  !inst. is_zero_revert_inst inst ==> is_terminator inst.inst_opcode
Proof
  rw[is_zero_revert_inst_def, is_terminator_def]
QED

(* ==========================================================================
   Transform Applicability Lemmas
   ========================================================================== *)

(* If transform_block changes the block, then rta_applicable held *)
Theorem transform_block_changes_applicable:
  !blocks next_id bb bb' next_id'.
    transform_block blocks next_id bb = (bb', next_id') /\
    bb' <> bb ==>
    rta_applicable blocks bb
Proof
  rw[transform_block_def, rta_applicable_def,
     rta_then_applicable_def, rta_else_applicable_def] >>
  gvs[AllCaseEqs()]
QED

(* If rta_then_applicable, the transform produces a block with assert + jmp *)
Theorem rta_then_produces_assert:
  !blocks bb new_var id1 id2 id3 bb'.
    rta_then_applicable blocks bb /\
    rewrite_jnz_then_revert bb new_var id1 id2 id3 = SOME bb' ==>
    ?cond_op else_lbl prefix.
      bb'.bb_instructions =
        prefix ++ [mk_iszero_inst id1 cond_op new_var;
                   mk_assert_inst id2 (Var new_var);
                   mk_jmp_inst id3 else_lbl]
Proof
  rw[rta_then_applicable_def, rewrite_jnz_then_revert_def] >>
  gvs[AllCaseEqs()] >>
  qexistsl_tac [`cond_op`, `else_lbl`] >> simp[]
QED

(* If rta_else_applicable, the transform produces a block with assert + jmp *)
Theorem rta_else_produces_assert:
  !blocks bb id1 id2 bb'.
    rta_else_applicable blocks bb /\
    rewrite_jnz_else_revert bb id1 id2 = SOME bb' ==>
    ?cond_op then_lbl prefix.
      bb'.bb_instructions =
        prefix ++ [mk_assert_inst id1 cond_op;
                   mk_jmp_inst id2 then_lbl]
Proof
  rw[rta_else_applicable_def, rewrite_jnz_else_revert_def] >>
  gvs[AllCaseEqs()] >>
  qexistsl_tac [`cond_op`, `then_lbl`] >> simp[]
QED

