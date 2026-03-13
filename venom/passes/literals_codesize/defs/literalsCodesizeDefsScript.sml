(*
 * Literals Codesize — Definitions
 *
 * Ports vyper/venom/passes/literals_codesize.py to HOL4.
 *
 * Pure peephole: replaces ASSIGN of large literals with NOT or SHL
 * of smaller literals to reduce deployed bytecode size.
 *
 * Framework: block_sim_function (no analysis needed).
 * Key property: step_inst equality — each rewritten instruction
 * produces the identical result as the original.
 *
 * TOP-LEVEL:
 *   lit_codesize_inst     — per-instruction transform
 *   lit_codesize_function — function-level transform
 *
 * Helper:
 *   push_size             — matches Python len(hex(val)) // 2
 *   trailing_zeros        — count trailing zero bits
 *)

Theory literalsCodesizeDefs
Ancestors
  passSimulationDefs passSharedDefs

(* ===== Push size helper ===== *)

(* Matches Python's `len(hex(val)) // 2` exactly.
   This approximates the EVM PUSH operand byte count and is used
   only to decide WHEN to apply the NOT/SHL rewrite — the correctness
   proof doesn't depend on what push_size computes, only on the
   semantic identities NOT(NOT x)=x and (x>>>tz)<<<tz=x. *)
Definition push_size_def:
  push_size (w : 256 word) =
    if w = 0w then 1n
    else (3 + w2n (word_log2 w) DIV 4) DIV 2
End

(* ===== Trailing zeros ===== *)

(* Count trailing zero bits *)
Definition trailing_zeros_def:
  trailing_zeros (w : 256 word) =
    if w = 0w then 256n
    else if word_bit 0 w then 0n
    else 1 + trailing_zeros (w >>> 1)
Termination
  WF_REL_TAC `measure w2n` >>
  rw[wordsTheory.w2n_lsr] >>
  rpt strip_tac >> irule arithmeticTheory.DIV_LESS >> simp[]
End

(* ===== Per-instruction transform ===== *)

(* Python benefit formulas (both in bits):
     not_benefit = (push_size(val) - push_size(~val) - NOT_THRESHOLD) * 8
     shl_benefit = trailing_zeros + 1 - SHL_THRESHOLD * 8
   where NOT_THRESHOLD = 1, SHL_THRESHOLD = 3.

   Decision tree:
     if not_benefit <= 0 and shl_benefit <= 0: skip
     if not_benefit >= shl_benefit: use NOT
     else: use SHL (shift amount = trailing_zeros)

   We encode the comparisons directly to avoid negative numbers.
     not_benefit > 0 ⟺ push_size val > push_size(~val) + 1
     shl_benefit > 0 ⟺ trailing_zeros >= 24  (tz+1 > 24)
     not_benefit >= shl_benefit ⟺
       (psz - pnot - 1) * 8 >= tz + 1 - 24
       rearranged (safe when both > 0):
       (psz - pnot - 1) * 8 + 23 >= tz

   NOTE: The correctness proof does NOT depend on push_size computing
   anything meaningful. It only needs the semantic identities:
     NOT case: word_1comp (word_1comp w) = w
     SHL case: word_lsl (word_lsr w tz) tz = w  (when tz = trailing_zeros w)
   The push_size logic just decides WHEN to apply the rewrite. *)
Definition lit_codesize_inst_def:
  lit_codesize_inst inst =
    if inst.inst_opcode <> ASSIGN then inst
    else case inst.inst_operands of
      [Lit w] =>
        let psz = push_size w in
        let pnot = push_size (word_1comp w) in
        let tz = trailing_zeros w in
        let has_not = (psz > pnot + 1) in
        let has_shl = (w <> 0w /\ tz > 23) in
        if ~has_not /\ ~has_shl then inst
        else if has_not /\ ~has_shl then
          (* only NOT profitable *)
          inst with <| inst_opcode := NOT;
                       inst_operands := [Lit (word_1comp w)] |>
        else if ~has_not /\ has_shl then
          (* only SHL profitable *)
          inst with <| inst_opcode := SHL;
                       inst_operands := [Lit (n2w tz); Lit (w >>> tz)] |>
        else
          (* both profitable: pick higher benefit *)
          if tz < (psz - pnot - 1) * 8 + 24 then
            inst with <| inst_opcode := NOT;
                         inst_operands := [Lit (word_1comp w)] |>
          else
            inst with <| inst_opcode := SHL;
                         inst_operands := [Lit (n2w tz); Lit (w >>> tz)] |>
    | _ => inst
End

(* ===== Function-level transform ===== *)

(* Pure peephole: no analysis. block_sim_function lifts per-block
   simulation to function level. Per-block follows from step_inst
   equality (each rewritten instruction produces identical output). *)
Definition lit_codesize_function_def:
  lit_codesize_function fn =
    function_map_transform
      (block_map_transform lit_codesize_inst) fn
End
