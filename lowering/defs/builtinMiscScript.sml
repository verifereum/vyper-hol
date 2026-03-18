(*
 * Miscellaneous Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_ecrecover   — ecrecover(hash, v, r, s) via precompile 0x1
 *   compile_ecadd       — ecadd(p1, p2) via precompile 0x6
 *   compile_ecmul       — ecmul(p, s) via precompile 0x7
 *   compile_blockhash   — blockhash(n) via BLOCKHASH opcode
 *   compile_blobhash    — blobhash(n) via BLOBHASH opcode
 *   compile_floor       — floor(x) for decimal → int (round toward -∞)
 *   compile_ceil        — ceil(x) for decimal → int (round toward +∞)
 *   compile_isqrt       — isqrt(x) integer square root via Newton's method
 *   compile_as_wei_value — multiply by denomination scale factor
 *   compile_min_value   — minimum value for a type
 *   compile_max_value   — maximum value for a type
 *   compile_epsilon     — smallest positive decimal (1 / DECIMAL_DIVISOR)
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/misc.py
 *)

Theory builtinMisc
Ancestors
  builtinSimple abiEncoder emitHelper context compileEnv venomInst

(* ===== Precompile Calls ===== *)

(* ecrecover(hash, v, r, s) → address
   Precompile at address 0x1
   Input: 4 × 32 bytes = 128 bytes
   Output: 32 bytes (padded address) *)
Definition compile_ecrecover_def:
  compile_ecrecover hash_op v_op r_op s_op st =
        let (in_buf_alloc, st2) = compile_alloc_buffer 128 st in
        let in_buf = in_buf_alloc.buf_operand in
    let (_, st3) = emit_void MSTORE [in_buf; hash_op] st2 in
    let (off1, st4) = emit_op ADD [in_buf; Lit 32w] st3 in
    let (_, st5) = emit_void MSTORE [off1; v_op] st4 in
    let (off2, st6) = emit_op ADD [in_buf; Lit 64w] st5 in
    let (_, st7) = emit_void MSTORE [off2; r_op] st6 in
    let (off3, st8) = emit_op ADD [in_buf; Lit 96w] st7 in
    let (_, st9) = emit_void MSTORE [off3; s_op] st8 in
        let (out_buf_alloc, st11) = compile_alloc_buffer 32 st9 in
        let out_buf = out_buf_alloc.buf_operand in
    (* Zero output buffer — ecrecover returns 0 bytes on invalid signature *)
    let (_, st11a) = emit_void MSTORE [out_buf; Lit 0w] st11 in
    let (gas_op, st12) = emit_op GAS [] st11a in
    let (success, st13) = emit_op STATICCALL
      [gas_op; Lit 1w; in_buf; Lit 128w; out_buf; Lit 32w] st12 in
    let (_, st14) = emit_void ASSERT [success] st13 in
    emit_op MLOAD [out_buf] st14
End

(* ecadd(x1, y1, x2, y2) → (x3, y3)
   Precompile at address 0x6
   Input: 4 × 32 = 128 bytes; Output: 2 × 32 = 64 bytes *)
Definition compile_ecadd_def:
  compile_ecadd x1 y1 x2 y2 st =
        let (in_buf_alloc, st2) = compile_alloc_buffer 128 st in
        let in_buf = in_buf_alloc.buf_operand in
    let (_, st3) = emit_void MSTORE [in_buf; x1] st2 in
    let (o1, st4) = emit_op ADD [in_buf; Lit 32w] st3 in
    let (_, st5) = emit_void MSTORE [o1; y1] st4 in
    let (o2, st6) = emit_op ADD [in_buf; Lit 64w] st5 in
    let (_, st7) = emit_void MSTORE [o2; x2] st6 in
    let (o3, st8) = emit_op ADD [in_buf; Lit 96w] st7 in
    let (_, st9) = emit_void MSTORE [o3; y2] st8 in
        let (out_buf_alloc, st11) = compile_alloc_buffer 64 st9 in
        let out_buf = out_buf_alloc.buf_operand in
    let (gas_op, st12) = emit_op GAS [] st11 in
    let (success, st13) = emit_op STATICCALL
      [gas_op; Lit 6w; in_buf; Lit 128w; out_buf; Lit 64w] st12 in
    let (_, st14) = emit_void ASSERT [success] st13 in
    (out_buf, st14)
End

(* ecmul(x, y, scalar) → (x', y')
   Precompile at address 0x7
   Input: 3 × 32 = 96 bytes; Output: 2 × 32 = 64 bytes *)
Definition compile_ecmul_def:
  compile_ecmul x y scalar st =
        let (in_buf_alloc, st2) = compile_alloc_buffer 96 st in
        let in_buf = in_buf_alloc.buf_operand in
    let (_, st3) = emit_void MSTORE [in_buf; x] st2 in
    let (o1, st4) = emit_op ADD [in_buf; Lit 32w] st3 in
    let (_, st5) = emit_void MSTORE [o1; y] st4 in
    let (o2, st6) = emit_op ADD [in_buf; Lit 64w] st5 in
    let (_, st7) = emit_void MSTORE [o2; scalar] st6 in
        let (out_buf_alloc, st9) = compile_alloc_buffer 64 st7 in
        let out_buf = out_buf_alloc.buf_operand in
    let (gas_op, st10) = emit_op GAS [] st9 in
    let (success, st11) = emit_op STATICCALL
      [gas_op; Lit 7w; in_buf; Lit 96w; out_buf; Lit 64w] st10 in
    let (_, st12) = emit_void ASSERT [success] st11 in
    (out_buf, st12)
End

(* ===== Block/Blob Hash ===== *)
(* Mirrors Python: misc.py lower_blockhash
   Validates block_num is in [block.number - 256, block.number).
   Reverts if out of range. *)
Definition compile_blockhash_def:
  compile_blockhash n_op st =
    let (current_block, st1) = emit_op NUMBER [] st in
    let (lower_bound, st2) = emit_op SUB [current_block; Lit 256w] st1 in
    (* Assert n >= lower_bound (signed comparison) *)
    let (too_old, st3) = emit_op SLT [n_op; lower_bound] st2 in
    let (ok1, st4) = emit_op ISZERO [too_old] st3 in
    let (_, st5) = emit_void ASSERT [ok1] st4 in
    (* Assert n < current_block *)
    let (in_range, st6) = emit_op LT [n_op; current_block] st5 in
    let (_, st7) = emit_void ASSERT [in_range] st6 in
    emit_op BLOCKHASH [n_op] st7
End

Definition compile_blobhash_def:
  compile_blobhash n_op = emit_op BLOBHASH [n_op]
End

(* ===== Decimal Rounding ===== *)
(* DECIMAL_DIVISOR = 10^10 = 10000000000 *)

(* floor(x): round decimal toward -infinity
   floor(x) = sdiv(x, DECIMAL_DIVISOR)
   for negative: need to subtract (DECIMAL_DIVISOR-1) before dividing *)
Definition compile_floor_def:
  compile_floor val_op divisor st =
    let (is_neg, st1) = emit_op SLT [val_op; Lit 0w] st in
    (* For negative: sub (divisor-1) to round toward -inf *)
    let (adjusted, st2) = emit_op SUB [val_op; Lit (n2w (divisor - 1))] st1 in
    (* select: is_neg ? adjusted : val_op *)
    let (input, st3) = compile_select is_neg adjusted val_op st2 in
    emit_op SDIV [input; Lit (n2w divisor)] st3
End

(* ceil(x): round decimal toward +infinity
   For positive: add (divisor-1) before dividing *)
Definition compile_ceil_def:
  compile_ceil val_op divisor st =
    let (is_pos, st1) = emit_op SGT [val_op; Lit 0w] st in
    let (adjusted, st2) = emit_op ADD [val_op; Lit (n2w (divisor - 1))] st1 in
    (* select: is_pos ? adjusted : val_op *)
    let (input, st3) = compile_select is_pos adjusted val_op st2 in
    emit_op SDIV [input; Lit (n2w divisor)] st3
End

(* ===== isqrt ===== *)
(* Integer square root via Babylonian method (branchless, unrolled).
   Mirrors Python: misc.py lower_isqrt — port of legacy IRnode.
   Uses select() for conditional updates, no loops.
   Steps:
   1. Initialize y=x, z=181
   2. Scale based on magnitude (4 conditional right-shifts on y, left-shifts on z)
   3. z = z * (y + 2^16) / 2^18
   4. 7 iterations of Newton refinement: z = (z + x/z) / 2
   5. Final: select(lt(z, x/z), z, x/z) *)
Definition compile_isqrt_def:
  compile_isqrt val_op st =
    (* Create mutable variables y and z *)
    let (y_var, st1) = fresh_var st in
    let (z_var, st2) = fresh_var st1 in
    let (_, st3) = emit_inst ASSIGN [val_op] [y_var] st2 in
    let (_, st4) = emit_inst ASSIGN [Lit 181w] [z_var] st3 in
    (* Scale 1: if y >= 2^136: y >>= 128, z <<= 64 *)
    let (cond1, st5) = emit_op LT [Var y_var; Lit (n2w (2 ** 136))] st4 in
    let (cond1_n, st6) = emit_op ISZERO [cond1] st5 in
    let (new_y1, st7) = emit_op SHR [Lit 128w; Var y_var] st6 in
    let (new_z1, st8) = emit_op SHL [Lit 64w; Var z_var] st7 in
    (* select: cond1_n ? new_y1 : y *)
    let (sel_y1, st9) = compile_select cond1_n new_y1 (Var y_var) st8 in
    let (sel_z1, st10) = compile_select cond1_n new_z1 (Var z_var) st9 in
    let (_, st11) = emit_inst ASSIGN [sel_y1] [y_var] st10 in
    let (_, st12) = emit_inst ASSIGN [sel_z1] [z_var] st11 in
    (* Scale 2: if y >= 2^72: y >>= 64, z <<= 32 *)
    let (cond2, st13) = emit_op LT [Var y_var; Lit (n2w (2 ** 72))] st12 in
    let (cond2_n, st14) = emit_op ISZERO [cond2] st13 in
    let (new_y2, st15) = emit_op SHR [Lit 64w; Var y_var] st14 in
    let (new_z2, st16) = emit_op SHL [Lit 32w; Var z_var] st15 in
    let (sel_y2, st17) = compile_select cond2_n new_y2 (Var y_var) st16 in
    let (sel_z2, st18) = compile_select cond2_n new_z2 (Var z_var) st17 in
    let (_, st19) = emit_inst ASSIGN [sel_y2] [y_var] st18 in
    let (_, st20) = emit_inst ASSIGN [sel_z2] [z_var] st19 in
    (* Scale 3: if y >= 2^40: y >>= 32, z <<= 16 *)
    let (cond3, st21) = emit_op LT [Var y_var; Lit (n2w (2 ** 40))] st20 in
    let (cond3_n, st22) = emit_op ISZERO [cond3] st21 in
    let (new_y3, st23) = emit_op SHR [Lit 32w; Var y_var] st22 in
    let (new_z3, st24) = emit_op SHL [Lit 16w; Var z_var] st23 in
    let (sel_y3, st25) = compile_select cond3_n new_y3 (Var y_var) st24 in
    let (sel_z3, st26) = compile_select cond3_n new_z3 (Var z_var) st25 in
    let (_, st27) = emit_inst ASSIGN [sel_y3] [y_var] st26 in
    let (_, st28) = emit_inst ASSIGN [sel_z3] [z_var] st27 in
    (* Scale 4: if y >= 2^24: y >>= 16, z <<= 8 *)
    let (cond4, st29) = emit_op LT [Var y_var; Lit (n2w (2 ** 24))] st28 in
    let (cond4_n, st30) = emit_op ISZERO [cond4] st29 in
    let (new_y4, st31) = emit_op SHR [Lit 16w; Var y_var] st30 in
    let (new_z4, st32) = emit_op SHL [Lit 8w; Var z_var] st31 in
    let (sel_y4, st33) = compile_select cond4_n new_y4 (Var y_var) st32 in
    let (sel_z4, st34) = compile_select cond4_n new_z4 (Var z_var) st33 in
    let (_, st35) = emit_inst ASSIGN [sel_y4] [y_var] st34 in
    let (_, st36) = emit_inst ASSIGN [sel_z4] [z_var] st35 in
    (* z = z * (y + 2^16) / 2^18 *)
    let (y_plus, st37) = emit_op ADD [Var y_var; Lit (n2w (2 ** 16))] st36 in
    let (z_mul, st38) = emit_op MUL [Var z_var; y_plus] st37 in
    let (z_scaled, st39) = emit_op Div [z_mul; Lit (n2w (2 ** 18))] st38 in
    let (_, st40) = emit_inst ASSIGN [z_scaled] [z_var] st39 in
    (* 7 Newton iterations: z = (z + x/z) / 2 *)
    let (xdz1, st41) = emit_op Div [val_op; Var z_var] st40 in
    let (s1, st42) = emit_op ADD [xdz1; Var z_var] st41 in
    let (nz1, st43) = emit_op Div [s1; Lit 2w] st42 in
    let (_, st44) = emit_inst ASSIGN [nz1] [z_var] st43 in
    let (xdz2, st45) = emit_op Div [val_op; Var z_var] st44 in
    let (s2, st46) = emit_op ADD [xdz2; Var z_var] st45 in
    let (nz2, st47) = emit_op Div [s2; Lit 2w] st46 in
    let (_, st48) = emit_inst ASSIGN [nz2] [z_var] st47 in
    let (xdz3, st49) = emit_op Div [val_op; Var z_var] st48 in
    let (s3, st50) = emit_op ADD [xdz3; Var z_var] st49 in
    let (nz3, st51) = emit_op Div [s3; Lit 2w] st50 in
    let (_, st52) = emit_inst ASSIGN [nz3] [z_var] st51 in
    let (xdz4, st53) = emit_op Div [val_op; Var z_var] st52 in
    let (s4, st54) = emit_op ADD [xdz4; Var z_var] st53 in
    let (nz4, st55) = emit_op Div [s4; Lit 2w] st54 in
    let (_, st56) = emit_inst ASSIGN [nz4] [z_var] st55 in
    let (xdz5, st57) = emit_op Div [val_op; Var z_var] st56 in
    let (s5, st58) = emit_op ADD [xdz5; Var z_var] st57 in
    let (nz5, st59) = emit_op Div [s5; Lit 2w] st58 in
    let (_, st60) = emit_inst ASSIGN [nz5] [z_var] st59 in
    let (xdz6, st61) = emit_op Div [val_op; Var z_var] st60 in
    let (s6, st62) = emit_op ADD [xdz6; Var z_var] st61 in
    let (nz6, st63) = emit_op Div [s6; Lit 2w] st62 in
    let (_, st64) = emit_inst ASSIGN [nz6] [z_var] st63 in
    let (xdz7, st65) = emit_op Div [val_op; Var z_var] st64 in
    let (s7, st66) = emit_op ADD [xdz7; Var z_var] st65 in
    let (nz7, st67) = emit_op Div [s7; Lit 2w] st66 in
    let (_, st68) = emit_inst ASSIGN [nz7] [z_var] st67 in
    (* Final: t = x/z; return select(lt(z, t), z, t) *)
    let (t_op, st69) = emit_op Div [val_op; Var z_var] st68 in
    let (lt_cond, st70) = emit_op LT [Var z_var; t_op] st69 in
    compile_select lt_cond (Var z_var) t_op st70
End

(* ===== as_wei_value ===== *)
(* Multiply by denomination scale factor.
   Mirrors Python: misc.py lower_as_wei_value
   Three cases:
   1. Decimal with denom=1: assert non-negative, div by DECIMAL_DIVISOR
   2. Decimal with denom>1: assert non-negative, mul then div by DECIMAL_DIVISOR
   3. Integer: mul with overflow check (div(product, value) == denom || value == 0)
      For signed types: also assert non-negative *)

(* Integer case *)
Definition compile_as_wei_value_int_def:
  compile_as_wei_value_int val_op scale is_signed st =
    if scale = 1 then (val_op, st)
    else
      let (product, st1) = emit_op MUL [val_op; Lit (n2w scale)] st in
      (* Overflow check: div(product, value) == denom || value == 0 *)
      let (quotient, st2) = emit_op Div [product; val_op] st1 in
      let (is_safe, st3) = emit_op EQ [quotient; Lit (n2w scale)] st2 in
      let (is_zero, st4) = emit_op ISZERO [val_op] st3 in
      let (ok, st5) = emit_op OR [is_safe; is_zero] st4 in
      (* For signed types: also check value >= 0 *)
      let (ok_final, st6) =
        if is_signed then
          let (is_pos, st_a) = emit_op SLT [val_op; Lit 0w] st5 in
          let (not_neg, st_b) = emit_op ISZERO [is_pos] st_a in
          emit_op AND [not_neg; ok] st_b
        else (ok, st5) in
      let (_, st7) = emit_void ASSERT [ok_final] st6 in
      (product, st7)
End

(* Decimal case *)
Definition compile_as_wei_value_decimal_def:
  compile_as_wei_value_decimal val_op scale decimal_divisor st =
    (* Assert non-negative *)
    let (neg, st1) = emit_op SLT [val_op; Lit 0w] st in
    let (not_neg, st2) = emit_op ISZERO [neg] st1 in
    let (_, st3) = emit_void ASSERT [not_neg] st2 in
    if scale = 1 then
      emit_op Div [val_op; Lit (n2w decimal_divisor)] st3
    else
      let (product, st4) = emit_op MUL [val_op; Lit (n2w scale)] st3 in
      emit_op Div [product; Lit (n2w decimal_divisor)] st4
End

(* NOTE: compile_min_value, compile_max_value, compile_epsilon deleted —
   exprLoweringScript inlines these as Lit values via type_bounds. *)

(* NOTE: compile_print, compile_breakpoint deleted — debug builtins
   not wired into the lowering pipeline. *)
