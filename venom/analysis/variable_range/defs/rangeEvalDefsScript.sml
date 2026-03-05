(*
 * Range Evaluators — Definitions
 *
 * Ports vyper/venom/analysis/variable_range/evaluators.py to HOL4.
 *
 * Per-opcode abstract evaluation: given input value_ranges,
 * produce an output value_range that over-approximates the
 * concrete result for all values within the input ranges.
 *
 * TOP-LEVEL:
 *   eval_range              — dispatch by opcode
 *   operand_range           — get range for an operand (Lit/Var)
 *   operand_lit             — get literal int value from operand (for precision)
 *
 * Helper:
 *   eval_range_add/sub/mul/div/mod/and/or/xor/not/shr/shl/sar/sdiv/smod
 *   eval_range_lt/gt/slt/sgt/eq/iszero/byte/signextend/assign
 *   vr_check_width          — widen to TOP if range too wide
 *   wrap256_signed           — wrap integer to signed 256-bit range
 *)

Theory rangeEvalDefs
Ancestors
  valueRangeDefs venomInst

(* ===== Range State ===== *)

(* Maps variables to their ranges. Variables absent from the map have TOP
   (unknown range), matching Python's env.get(var, ValueRange.top()). *)
Type range_state = ``:(string, value_range) fmap``

(* Look up range for a variable; absent = TOP *)
Definition rs_lookup_def:
  rs_lookup (rs : (string, value_range) fmap) v =
    case FLOOKUP rs v of
      NONE => VR_Top
    | SOME r => r
End

(* Write a range. TOP → delete (normalize, matching Python _write_range). *)
Definition rs_write_def:
  rs_write (rs : (string, value_range) fmap) v r =
    if vr_is_top r then rs \\ v
    else rs |+ (v, r)
End

(* All variables in state satisfy their ranges *)
Definition in_range_state_def:
  in_range_state (rs : (string, value_range) fmap)
                 (env : (string, 256 word) fmap) =
    ∀v r. FLOOKUP rs v = SOME r ⇒
      ∀w. FLOOKUP env v = SOME w ⇒ in_range r w
End

(* ===== Helpers ===== *)

(* Width check: ranges wider than RANGE_WIDTH_LIMIT are imprecise.
   Matches Python's implicit checks in each evaluator. *)
Definition vr_check_width_def:
  vr_check_width (VR_Range lo hi) =
    (if hi - lo > RANGE_WIDTH_LIMIT then VR_Top
     else VR_Range lo hi) ∧
  vr_check_width x = x
End

(* Wrap to signed 256-bit range: (v + 2^255) mod 2^256 - 2^255.
   Matches Python wrap256(v, signed=True).
   Note: we use int_mod for proper signed modular arithmetic. *)
Definition wrap256_signed_def:
  wrap256_signed (v : int) : int =
    let shifted = v + &(2 ** 255) in
    let wrapped = shifted % &(2 ** 256) in
    wrapped - &(2 ** 255)
End

(* Get range for an operand.
   Lit → constant range (signed interpretation).
   Var → look up in state, default TOP.
   Label → TOP. *)
Definition operand_range_def:
  operand_range rs (Lit v) = vr_constant (w2i v) ∧
  operand_range rs (Var v) = rs_lookup rs v ∧
  operand_range rs (Label l) = VR_Top
End

(* Extract literal value from operand for evaluator precision.
   Lit → SOME (signed interpretation); Var/Label → NONE. *)
Definition operand_lit_def:
  operand_lit (Lit v) = SOME (w2i v) ∧
  operand_lit _ = NONE
End

(* ===== Arithmetic Evaluators ===== *)

(* ADD: matches Python _eval_add *)
Definition eval_range_add_def:
  eval_range_add r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (VR_Top, _) => VR_Top
    | (_, VR_Top) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo1 = hi1 ∧ lo2 = hi2 then
          vr_constant (wrap256_signed (lo1 + lo2))
        else if lo1 < 0 ∨ lo2 < 0 then VR_Top
        else if hi1 - lo1 > RANGE_WIDTH_LIMIT ∨
                hi2 - lo2 > RANGE_WIDTH_LIMIT then VR_Top
        else
          let lo = lo1 + lo2 in
          let hi = hi1 + hi2 in
          if hi > INT256_MAX then VR_Top
          else VR_Range lo hi
End

(* SUB: matches Python _eval_sub *)
Definition eval_range_sub_def:
  eval_range_sub r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (VR_Top, _) => VR_Top
    | (_, VR_Top) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo1 = hi1 ∧ lo2 = hi2 then
          vr_constant (wrap256_signed (lo1 - lo2))
        else if hi1 - lo1 > RANGE_WIDTH_LIMIT ∨
                hi2 - lo2 > RANGE_WIDTH_LIMIT then VR_Top
        else
          let lo = lo1 - hi2 in
          let hi = hi1 - lo2 in
          if lo < INT256_MIN ∨ hi > INT256_MAX ∨ lo > hi then VR_Top
          else VR_Range lo hi
End

(* MUL: matches Python _eval_mul *)
Definition eval_range_mul_def:
  eval_range_mul r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (VR_Top, _) => VR_Top
    | (_, VR_Top) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo1 = hi1 ∧ lo1 = 0 then vr_constant 0
        else if lo2 = hi2 ∧ lo2 = 0 then vr_constant 0
        else if lo1 = hi1 ∧ lo2 = hi2 then
          vr_constant (wrap256_signed (lo1 * lo2))
        else if lo1 < 0 ∨ lo2 < 0 then VR_Top
        else if hi1 - lo1 > RANGE_WIDTH_LIMIT ∨
                hi2 - lo2 > RANGE_WIDTH_LIMIT then VR_Top
        else if hi1 > 0 ∧ hi2 > INT256_MAX / hi1 then VR_Top
        else
          let hi = hi1 * hi2 in
          if hi > INT256_MAX then VR_Top
          else VR_Range (lo1 * lo2) hi
End

(* DIV (unsigned): matches Python _eval_div.
   Divisor literal is w2i; negative w2i means unsigned divisor ≥ 2^255.
   For non-negative dividend (< 2^255), dividing by ≥ 2^255 gives 0. *)
Definition eval_range_div_def:
  eval_range_div r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (_, VR_Top) => VR_Top
    | (VR_Top, _) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo2 = hi2 then
          if lo2 = 0 then vr_constant 0
          else if lo1 < 0 then VR_Top
          else if lo2 < 0 then vr_constant 0  (* large unsigned divisor *)
          else VR_Range (lo1 / lo2) (hi1 / lo2)
        else VR_Top
End

(* MOD (unsigned): matches Python _eval_mod.
   Divisor literal is w2i; negative w2i means unsigned divisor ≥ 2^255.
   For non-negative dividend, mod by large divisor = dividend itself. *)
Definition eval_range_mod_def:
  eval_range_mod r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (_, VR_Top) => VR_Top
    | (VR_Top, _) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo2 = hi2 then
          if lo2 = 0 then vr_constant 0
          else if lo2 < 0 then VR_Top  (* large unsigned divisor *)
          else VR_Range 0 (lo2 - 1)
        else VR_Top
End

(* SDIV (signed): matches Python _eval_sdiv *)
Definition eval_range_sdiv_def:
  eval_range_sdiv r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (_, VR_Top) => VR_Top
    | (VR_Top, _) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo2 = hi2 then
          if lo2 = 0 then vr_constant 0
          else if lo1 = hi1 then
            if lo1 = INT256_MIN ∧ lo2 = -1 then vr_constant INT256_MIN
            else
              let sign = if (lo1 < 0) ≠ (lo2 < 0) then -1 else (1:int) in
              vr_constant (sign * (ABS lo1 / ABS lo2))
          else if lo2 < 0 then VR_Top
          else if lo1 ≥ 0 then
            VR_Range (lo1 / lo2) (hi1 / lo2)
          else if hi1 < 0 then
            VR_Range (-(ABS lo1 / lo2)) (-(ABS hi1 / lo2))
          else
            VR_Range (-(ABS lo1 / lo2)) (hi1 / lo2)
        else VR_Top
End

(* SMOD (signed): matches Python _eval_smod *)
Definition eval_range_smod_def:
  eval_range_smod r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | (_, VR_Top) => VR_Top
    | (VR_Top, _) => VR_Top
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo2 = hi2 then
          if lo2 = 0 then vr_constant 0
          else
            let limit = ABS lo2 - 1 in
            if lo1 ≥ 0 then
              VR_Range 0 (int_min limit hi1)
            else if hi1 ≤ 0 then
              VR_Range (int_max (-limit) lo1) 0
            else
              VR_Range (-limit) limit
        else VR_Top
End

(* ===== Bitwise Evaluators ===== *)

(* AND: matches Python _eval_and.
   lit1/lit2 are w2i of the literal operand.
   w2i(-1w) = -1, which is all-bits-set (identity for AND).
   Negative mask (w2i < 0) means high bit set → large unsigned mask → imprecise. *)
Definition eval_range_and_def:
  eval_range_and r1 r2 lit1 lit2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case (lit1, lit2) of
          (SOME mask, _) =>
            if mask = -1 then r2               (* AND with all-ones is identity *)
            else if mask < 0 then VR_Top       (* negative w2i = large unsigned mask *)
            else if vr_lo r2 < 0 then VR_Range 0 mask
            else VR_Range 0 (int_min (vr_hi r2) mask)
        | (_, SOME mask) =>
            if mask = -1 then r1
            else if mask < 0 then VR_Top
            else if vr_lo r1 < 0 then VR_Range 0 mask
            else VR_Range 0 (int_min (vr_hi r1) mask)
        | _ => VR_Top
End

(* OR: matches Python _eval_or *)
Definition eval_range_or_def:
  eval_range_or r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        if vr_is_constant r1 ∧ vr_is_constant r2 then
          let a = vr_lo r1 in let b = vr_lo r2 in
          (* can't compute exact OR in int domain without word ops *)
          VR_Top
        else if vr_is_constant r1 ∧ vr_lo r1 = 0 then r2
        else if vr_is_constant r2 ∧ vr_lo r2 = 0 then r1
        else VR_Top
End

(* XOR: matches Python _eval_xor *)
Definition eval_range_xor_def:
  eval_range_xor r1 r2 same_var =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        if same_var then vr_constant 0
        else VR_Top
End

(* NOT: matches Python _eval_not — only precise for constants *)
Definition eval_range_not_def:
  eval_range_not r1 =
    case r1 of
      VR_Bottom => VR_Bottom
    | _ => VR_Top
End

(* ===== Shift Evaluators ===== *)

(* SHR: matches Python _eval_shr.
   Shift literal is w2i; negative w2i means unsigned shift ≥ 2^255 ≥ 256 → result 0. *)
Definition eval_range_shr_def:
  eval_range_shr r_shift r_val (shift_lit : int option) =
    case (r_shift, r_val) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case shift_lit of
          NONE => VR_Top
        | SOME sh =>
            if sh < 0 then vr_constant 0    (* unsigned shift ≥ 2^255 *)
            else if sh ≥ 256 then vr_constant 0
            else if vr_lo r_val < 0 then VR_Top
            else
              let amount = 2 ** Num sh in
              VR_Range (vr_lo r_val / &amount) (vr_hi r_val / &amount)
End

(* SHL: matches Python _eval_shl.
   Shift literal is w2i; negative w2i means unsigned shift ≥ 2^255 ≥ 256 → result 0. *)
Definition eval_range_shl_def:
  eval_range_shl r_shift r_val (shift_lit : int option) =
    case (r_shift, r_val) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case shift_lit of
          NONE => VR_Top
        | SOME sh =>
            if sh < 0 then vr_constant 0    (* unsigned shift ≥ 2^255 *)
            else if sh ≥ 256 then vr_constant 0
            else if vr_lo r_val < 0 then VR_Top
            else
              let max_input = UINT256_MAX_int / &(2 ** Num sh) in
              if vr_hi r_val > max_input then VR_Top
              else
                let lo = vr_lo r_val * &(2 ** Num sh) in
                let hi = vr_hi r_val * &(2 ** Num sh) in
                let lo' = wrap256_signed lo in
                let hi' = wrap256_signed hi in
                if lo' > hi' then VR_Top
                else VR_Range lo' hi'
End

(* SAR (arithmetic shift right): matches Python _eval_sar.
   Shift literal is w2i; negative w2i means unsigned shift ≥ 2^255.
   For SAR with huge shift: result is 0 (non-negative) or -1 (negative). *)
Definition eval_range_sar_def:
  eval_range_sar r_shift r_val (shift_lit : int option) =
    case (r_shift, r_val) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case shift_lit of
          NONE => VR_Top
        | SOME sh =>
            if vr_hi r_val > INT256_MAX then VR_Top
            else if sh < 0 ∨ sh ≥ 256 then  (* huge shift *)
              if vr_lo r_val ≥ 0 then vr_constant 0
              else if vr_hi r_val < 0 then vr_constant (-1)
              else VR_Range (-1) 0
            else
              (* Arithmetic right shift preserves sign and order *)
              VR_Range (vr_lo r_val / &(2 ** Num sh))
                       (vr_hi r_val / &(2 ** Num sh))
End

(* ===== Comparison Evaluators ===== *)

(* LT/GT/SLT/SGT: matches Python _eval_compare.
   For unsigned ops (LT/GT), ranges on opposite sides of the sign boundary
   have reversed ordering: negative signed values are large unsigned values.
   After sign-boundary-span check, ranges are entirely one side or the other. *)
Definition eval_range_compare_def:
  eval_range_compare op r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        let signed = (op = SLT ∨ op = SGT) in
        (* For unsigned, if either spans sign boundary → bool_range *)
        if ¬signed ∧ (vr_spans_sign_boundary r1 ∨
                       vr_spans_sign_boundary r2) then vr_bool_range
        (* For unsigned, ranges on opposite sides of sign boundary *)
        else if ¬signed ∧ vr_hi r1 < 0 ∧ vr_lo r2 ≥ 0 then
          (* r1 all-negative (large unsigned), r2 all-non-negative (small unsigned) *)
          if op = LT then vr_constant 0 else vr_constant 1
        else if ¬signed ∧ vr_lo r1 ≥ 0 ∧ vr_hi r2 < 0 then
          (* r1 all-non-negative (small unsigned), r2 all-negative (large unsigned) *)
          if op = LT then vr_constant 1 else vr_constant 0
        else
          (* Same sign or signed comparison: signed ordering is correct *)
          let is_lt = (op = LT ∨ op = SLT) in
          if is_lt then
            if vr_hi r1 < vr_lo r2 then vr_constant 1
            else if vr_lo r1 ≥ vr_hi r2 then vr_constant 0
            else vr_bool_range
          else (* GT or SGT *)
            if vr_lo r1 > vr_hi r2 then vr_constant 1
            else if vr_hi r1 ≤ vr_lo r2 then vr_constant 0
            else vr_bool_range
End

(* EQ: matches Python _eval_eq *)
Definition eval_range_eq_def:
  eval_range_eq r1 r2 =
    case (r1, r2) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        if vr_spans_sign_boundary r1 ∨ vr_spans_sign_boundary r2 then
          vr_bool_range
        else if vr_hi r1 < vr_lo r2 ∨ vr_hi r2 < vr_lo r1 then
          vr_constant 0
        else vr_bool_range
End

(* ISZERO: matches Python _eval_iszero *)
Definition eval_range_iszero_def:
  eval_range_iszero r1 =
    case r1 of
      VR_Bottom => VR_Bottom
    | VR_Top => vr_bool_range
    | VR_Range lo hi =>
        if lo = 0 ∧ hi = 0 then vr_constant 1
        else if lo > 0 ∨ hi < 0 then vr_constant 0
        else vr_bool_range
End

(* ===== Byte / Signextend ===== *)

(* BYTE: matches Python _eval_byte.
   Index literal is w2i; negative w2i means unsigned index ≥ 2^255 ≥ 32 → result 0. *)
Definition eval_range_byte_def:
  eval_range_byte r_idx r_val (idx_lit : int option) =
    case (r_idx, r_val) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case idx_lit of
          NONE => vr_bytes_range 1
        | SOME idx =>
            if idx < 0 ∨ idx ≥ 32 then vr_constant 0
            else vr_bytes_range 1
End

(* SIGNEXTEND: matches Python _eval_signextend.
   Index literal is w2i; negative w2i means unsigned index ≥ 2^255 ≥ 32 → identity. *)
Definition eval_range_signextend_def:
  eval_range_signextend r_idx r_val (idx_lit : int option) =
    case (r_idx, r_val) of
      (VR_Bottom, _) => VR_Bottom
    | (_, VR_Bottom) => VR_Bottom
    | _ =>
        case idx_lit of
          NONE => VR_Top
        | SOME idx =>
            if idx < 0 ∨ idx ≥ 32 then r_val  (* large index → identity *)
            else
              let bits = 8 * (Num idx + 1) in
              let lo = -(&(2 ** (bits - 1))) in
              let hi = &(2 ** (bits - 1)) - 1 in
              if vr_lo r_val ≥ lo ∧ vr_hi r_val ≤ hi then r_val
              else VR_Range lo hi
End

(* ===== ASSIGN ===== *)

Definition eval_range_assign_def:
  eval_range_assign r1 = r1
End

(* ===== Top-Level Dispatch ===== *)

(* Dispatch evaluator by opcode.
   Takes opcode + list of operand ranges + optional literal info.
   For bitwise ops, literal values needed for precision (AND mask etc).
   Returns output range.

   Note: ops that need literal values (AND, BYTE, SHR, SHL, SAR,
   SIGNEXTEND) get NONE if the operand is not a known literal.
   The analysis layer extracts literals before calling this. *)
Definition eval_range_def:
  eval_range op (ranges : value_range list) (lits : (int option) list) =
    case (op, ranges) of
      (ASSIGN, [r]) => eval_range_assign r
    | (ADD, [r1; r2]) => eval_range_add r1 r2
    | (SUB, [r1; r2]) => eval_range_sub r1 r2
    | (MUL, [r1; r2]) => eval_range_mul r1 r2
    | (Div, [r1; r2]) => eval_range_div r1 r2
    | (Mod, [r1; r2]) => eval_range_mod r1 r2
    | (SDIV, [r1; r2]) => eval_range_sdiv r1 r2
    | (SMOD, [r1; r2]) => eval_range_smod r1 r2
    | (AND, [r1; r2]) =>
        eval_range_and r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
          (case lits of [_; l2] => l2 | _ => NONE)
    | (OR, [r1; r2]) => eval_range_or r1 r2
    | (XOR, [r1; r2]) => eval_range_xor r1 r2 F
    | (NOT, [r1]) => eval_range_not r1
    | (SHR, [r1; r2]) =>
        eval_range_shr r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
    | (SHL, [r1; r2]) =>
        eval_range_shl r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
    | (SAR, [r1; r2]) =>
        eval_range_sar r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
    | (SIGNEXTEND, [r1; r2]) =>
        eval_range_signextend r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
    | (LT, [r1; r2]) => eval_range_compare LT r1 r2
    | (GT, [r1; r2]) => eval_range_compare GT r1 r2
    | (SLT, [r1; r2]) => eval_range_compare SLT r1 r2
    | (SGT, [r1; r2]) => eval_range_compare SGT r1 r2
    | (EQ, [r1; r2]) => eval_range_eq r1 r2
    | (ISZERO, [r1]) => eval_range_iszero r1
    | (BYTE, [r1; r2]) =>
        eval_range_byte r1 r2
          (case lits of [l1; _] => l1 | _ => NONE)
    | _ => VR_Top
End
