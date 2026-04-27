(*
 * Algebraic Optimization — Iszero Resolution & CMP Flip Correctness
 *
 * TOP-LEVEL:
 *   ao_resolve_iszero_inst_opcode    — iszero resolution preserves opcode
 *   ao_resolve_iszero_inst_outputs   — iszero resolution preserves outputs
 *   ao_resolve_iszero_inst_id        — iszero resolution preserves inst_id
 *   ao_cmp_flip_apply_inst_structural — cmp_flip structural properties
 *   ao_cmp_flip_identity             — most instructions pass through unchanged
 *)

Theory algebraicOptResolveSim
Ancestors
  algebraicOptDefs passSharedDefs venomExecSemantics venomState venomInst
Libs
  pairLib BasicProvers

(* ===== Iszero Resolution Structural Properties ===== *)

(* ao_resolve_iszero_inst only changes operands, preserving all other fields *)
Theorem ao_resolve_iszero_inst_opcode:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_opcode = inst.inst_opcode
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_resolve_iszero_inst_outputs:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_resolve_iszero_inst_id:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  simp[ao_resolve_iszero_inst_def]
QED

(* Iszero resolution preserves terminator status *)
Theorem ao_resolve_iszero_inst_is_terminator:
  !targets inst.
    is_terminator (ao_resolve_iszero_inst targets inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  simp[ao_resolve_iszero_inst_opcode]
QED

(* Iszero resolution preserves INVOKE status *)
Theorem ao_resolve_iszero_inst_invoke:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_opcode = INVOKE <=>
    inst.inst_opcode = INVOKE
Proof
  simp[ao_resolve_iszero_inst_opcode]
QED

(* For ISZERO use-opcode, resolution is identity on operands *)
Theorem ao_resolve_iszero_op_iszero_identity:
  !targets op.
    ao_resolve_iszero_op targets ISZERO op = op
Proof
  rpt gen_tac >>
  Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  CASE_TAC >> simp[]
QED

(* For non-Var operands, resolution is identity *)
Theorem ao_resolve_iszero_op_lit:
  !targets opc v.
    ao_resolve_iszero_op targets opc (Lit v) = Lit v
Proof
  simp[ao_resolve_iszero_op_def]
QED

Theorem ao_resolve_iszero_op_label:
  !targets opc l.
    ao_resolve_iszero_op targets opc (Label l) = Label l
Proof
  simp[ao_resolve_iszero_op_def]
QED

(* Resolution is identity when variable not in targets *)
Theorem ao_resolve_iszero_op_not_in_targets:
  !targets opc x.
    ALOOKUP targets x = NONE ==>
    ao_resolve_iszero_op targets opc (Var x) = Var x
Proof
  simp[ao_resolve_iszero_op_def]
QED

(* ===== Pre/Post Flip Helpers ===== *)

(* pre_flip is identity for non-commutative opcodes *)
Theorem ao_pre_flip_inst_non_comm:
  !inst.
    inst.inst_opcode <> ADD /\ inst.inst_opcode <> MUL /\
    inst.inst_opcode <> AND /\ inst.inst_opcode <> OR /\
    inst.inst_opcode <> XOR /\ inst.inst_opcode <> EQ ==>
    ao_pre_flip_inst inst = inst
Proof
  rpt strip_tac >> simp[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* post_flip is identity for non-commutative opcodes *)
Theorem ao_post_flip_inst_non_comm:
  !inst.
    inst.inst_opcode <> ADD /\ inst.inst_opcode <> MUL /\
    inst.inst_opcode <> AND /\ inst.inst_opcode <> OR /\
    inst.inst_opcode <> XOR /\ inst.inst_opcode <> EQ ==>
    ao_post_flip_inst inst = inst
Proof
  rpt strip_tac >> simp[ao_post_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* post_flip preserves opcode *)
Theorem ao_post_flip_inst_opcode:
  !inst. (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  gen_tac >> simp[ao_post_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >> rw[]
QED

(* ===== CMP Flip Structural Properties ===== *)

(* When instruction is not in any of the three lists, cmp_flip is identity *)
Theorem ao_cmp_flip_identity:
  !flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    ao_cmp_flip_apply_inst flips removes inserts inst = [inst]
Proof
  rw[ao_cmp_flip_apply_inst_def]
QED

(* Flip case: produces a singleton *)
Theorem ao_cmp_flip_apply_flip:
  !flips removes inserts inst new_opc new_w orig_op1.
    ALOOKUP flips inst.inst_id = SOME (new_opc, new_w, orig_op1) ==>
    ao_cmp_flip_apply_inst flips removes inserts inst =
    [inst with <| inst_opcode := new_opc;
                  inst_operands := [orig_op1; Lit new_w] |>]
Proof
  rw[ao_cmp_flip_apply_inst_def]
QED

(* Remove case: produces a singleton with ASSIGN *)
Theorem ao_cmp_flip_apply_remove:
  !flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    MEM inst.inst_id removes ==>
    ao_cmp_flip_apply_inst flips removes inserts inst =
    [inst with <| inst_opcode := ASSIGN |>]
Proof
  rw[ao_cmp_flip_apply_inst_def]
QED

(* Insert case: produces two instructions *)
Theorem ao_cmp_flip_apply_insert:
  !flips removes inserts inst cmp_out fresh cmp_id.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh, cmp_id) ==>
    ao_cmp_flip_apply_inst flips removes inserts inst =
    [<| inst_id := cmp_id; inst_opcode := ISZERO;
        inst_operands := [Var cmp_out];
        inst_outputs := [fresh] |>;
     inst with <| inst_operands := [Var fresh] |>]
Proof
  rw[ao_cmp_flip_apply_inst_def]
QED

(* cmp_flip never produces empty lists *)
Theorem ao_cmp_flip_apply_inst_nonempty:
  !flips removes inserts inst.
    ao_cmp_flip_apply_inst flips removes inserts inst <> []
Proof
  rw[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> simp[]
QED

(* cmp_flip preserves terminator status for identity case *)
Theorem ao_cmp_flip_identity_terminator:
  !flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    is_terminator (HD (ao_cmp_flip_apply_inst flips removes inserts inst)).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[ao_cmp_flip_apply_inst_def]
QED

(* flip_comparison_opcode on comparators produces non-terminators *)
Theorem flip_comparison_not_terminator:
  !opc. is_comparator opc ==> ~is_terminator (flip_comparison_opcode opc)
Proof
  Cases >> simp[is_comparator_def, flip_comparison_opcode_def, is_terminator_def]
QED

(* flip_comparison_opcode on comparators produces non-INVOKE *)
Theorem flip_comparison_not_invoke:
  !opc. is_comparator opc ==> flip_comparison_opcode opc <> INVOKE
Proof
  Cases >> simp[is_comparator_def, flip_comparison_opcode_def]
QED

(* ===== CMP Flip Semantic Properties ===== *)

(* The flip transformation: GT(x,w) with ISZERO → LT(x,w+1)
   is semantically correct when w+1 doesn't overflow.
   Specifically: iszero(GT(x, w)) = LT(x, w+1) for unsigned,
   when w < MAX (i.e., w+1 doesn't wrap to 0).

   This is the core semantic identity behind cmp_flip. *)

(* Helper: bool_to_word b = 0w iff ~b, bool_to_word b = 1w iff b *)
Triviality btw_0[local]:
  !b. (bool_to_word b = 0w) <=> ~b
Proof Cases >> simp[bool_to_word_def]
QED

Triviality btw_1[local]:
  !b. (bool_to_word b = 1w) <=> b
Proof Cases >> simp[bool_to_word_def]
QED

(* For unsigned GT �� LT flip: iszero(x > w) = (x < w+1) when w < MAX *)
Theorem cmp_flip_gt_lt:
  !x w : bytes32.
    w <> 0w - 1w ==>
    (bool_to_word (w2n x > w2n w) = 0w) =
    (bool_to_word (w2n x < w2n (w + 1w)) = 1w)
Proof
  rpt strip_tac >> simp[btw_0, btw_1] >>
  (* ~(w2n x > w2n w) <=> w2n x <= w2n w <=> w2n x < w2n w + 1 *)
  (* w2n (w + 1w) = w2n w + 1 when w <> MAX *)
  `w2n (w + 1w) = w2n w + 1` by (
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
    `w2n w < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
    `w2n w + 1 < dimword(:256)` by (
      spose_not_then strip_assume_tac >>
      `w2n w = dimword(:256) - 1` by simp[] >>
      `w = n2w (dimword(:256) - 1)` by metis_tac[wordsTheory.n2w_w2n] >>
      `0w - 1w : bytes32 = n2w (dimword(:256) - 1)` by
        simp[wordsTheory.word_sub_def, wordsTheory.word_2comp_def,
             wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
      gvs[]) >>
    simp[]) >>
  simp[]
QED

(* Helper: w2n (w - 1w) = w2n w - 1 when w ≠ 0w *)
Triviality w2n_sub1[local]:
  !w : bytes32. w <> 0w ==> w2n (w - 1w) = w2n w - 1
Proof
  rpt strip_tac >>
  imp_res_tac wordsTheory.SUC_WORD_PRED >>
  (* SUC (w2n (w - 1w)) = w2n w, so w2n (w - 1w) = w2n w - 1 *)
  decide_tac
QED

(* For unsigned LT → GT flip: iszero(x < w) = (x > w-1) when w > 0 *)
Theorem cmp_flip_lt_gt:
  !x w : bytes32.
    w <> 0w ==>
    (bool_to_word (w2n x < w2n w) = 0w) =
    (bool_to_word (w2n x > w2n (w - 1w)) = 1w)
Proof
  rpt strip_tac >>
  imp_res_tac wordsTheory.SUC_WORD_PRED >>
  (* SUC (w2n (w - 1w)) = w2n w *)
  simp[btw_0, btw_1, arithmeticTheory.GREATER_DEF,
       arithmeticTheory.NOT_LESS] >>
  (* Goal: w2n w <= w2n x <=> w2n (w - 1w) < w2n x *)
  (* From SUC_WORD_PRED: w2n (w-1w) < a <=> SUC(w2n(w-1w)) <= a <=> w2n w <= a *)
  `!a. w2n (w - 1w) < a <=> w2n w <= a` by simp[] >>
  simp[]
QED

(* ===== CMP Flip Remove: ISZERO → ASSIGN preserves value ===== *)

(* When an ISZERO is converted to ASSIGN, the value passes through.
   This is correct because:
   - The ISZERO was: out = iszero(cmp_result)
   - After flip, the comparator already computes the negated result
   - So ASSIGN just passes through: out = flipped_cmp_result
   The values match because the flip was designed to make this so. *)
Theorem ao_cmp_flip_remove_step_equiv:
  !inst s.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out] ==>
    step_inst_base (inst with inst_opcode := ASSIGN) s =
    case eval_operand op s of
      SOME v => OK (update_var out v s)
    | NONE => Error "undefined operand"
Proof
  rw[step_inst_base_def]
QED

(* ISZERO semantics for reference *)
Theorem iszero_step:
  !inst op out s v.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out] /\
    eval_operand op s = SOME v ==>
    step_inst_base inst s = OK (update_var out (bool_to_word (v = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure1_def]
QED

(* ===== ao_transform_inst structural properties ===== *)

(* ao_transform_inst preserves terminator instructions as singletons.
   Terminators in Venom IR don't have outputs (inst_outputs = []),
   so they hit the first branch in ao_transform_inst. *)
Theorem ao_transform_inst_terminator:
  !dfg ra lbl idx targets inst.
    is_terminator inst.inst_opcode /\
    inst.inst_outputs = [] ==>
    ?inst'. ao_transform_inst dfg ra lbl idx targets inst = [inst'] /\
            inst'.inst_opcode = inst.inst_opcode /\
            inst'.inst_id = inst.inst_id /\
            inst'.inst_outputs = inst.inst_outputs
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM,
       ao_resolve_iszero_inst_outputs,
       ao_resolve_iszero_inst_opcode,
       ao_resolve_iszero_inst_id]
QED

(* ao_transform_inst preserves INVOKE: INVOKE is not in any peephole
   dispatch case, so it passes through (possibly with resolved operands).
   Proof requires tracing through the full peephole dispatch for INVOKE. *)
Theorem ao_transform_inst_invoke:
  !dfg ra lbl idx targets inst.
    inst.inst_opcode = INVOKE ==>
    ?inst'. ao_transform_inst dfg ra lbl idx targets inst = [inst'] /\
            inst'.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM,
       ao_resolve_iszero_inst_opcode,
       ao_resolve_iszero_inst_outputs] >>
  Cases_on `inst.inst_outputs`
  >- simp[ao_resolve_iszero_inst_opcode]
  >> (simp[] >>
      simp[ao_opt_producer_def, ao_resolve_iszero_inst_opcode] >>
      (* pre_flip is identity for INVOKE (not commutative) *)
      `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst) =
       ao_resolve_iszero_inst targets inst` by (
        irule ao_pre_flip_inst_non_comm >>
        simp[ao_resolve_iszero_inst_opcode]) >>
      simp[] >>
      (* ao_peephole_inst: INVOKE doesn't match any dispatch case *)
      simp[ao_peephole_inst_def, LET_THM,
           ao_resolve_iszero_inst_opcode] >>
      (* post_flip is identity for INVOKE *)
      simp[ao_post_flip_inst_non_comm, ao_resolve_iszero_inst_opcode])
QED

(* ao_cmp_flip_apply_inst structural: non-terminators produce non-terminators
   (for the identity case which covers most instructions) *)
Theorem ao_cmp_flip_apply_identity_every_non_term:
  !flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE /\
    ~is_terminator inst.inst_opcode ==>
    EVERY (\j. ~is_terminator j.inst_opcode)
      (ao_cmp_flip_apply_inst flips removes inserts inst)
Proof
  rw[ao_cmp_flip_apply_inst_def, listTheory.EVERY_DEF]
QED

(* ao_cmp_flip_apply_inst: non-terminators produce non-INVOKE
   (for the identity case) *)
Theorem ao_cmp_flip_apply_identity_every_non_invoke:
  !flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE /\
    inst.inst_opcode <> INVOKE ==>
    EVERY (\j. j.inst_opcode <> INVOKE)
      (ao_cmp_flip_apply_inst flips removes inserts inst)
Proof
  rw[ao_cmp_flip_apply_inst_def, listTheory.EVERY_DEF]
QED

val _ = export_theory();
