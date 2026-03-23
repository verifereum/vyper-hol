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
Libs
  monadsyntax

(* ===== Precompile Calls ===== *)

(* ecrecover(hash, v, r, s) → address
   Precompile at address 0x1
   Input: 4 × 32 bytes = 128 bytes
   Output: 32 bytes (padded address) *)
Definition compile_ecrecover_def:
  compile_ecrecover hash_op v_op r_op s_op =
    do in_buf_alloc <- compile_alloc_buffer 128;
       in_buf <- return in_buf_alloc.buf_operand;
       emit_void MSTORE [in_buf; hash_op];
       off1 <- emit_op ADD [in_buf; Lit 32w];
       emit_void MSTORE [off1; v_op];
       off2 <- emit_op ADD [in_buf; Lit 64w];
       emit_void MSTORE [off2; r_op];
       off3 <- emit_op ADD [in_buf; Lit 96w];
       emit_void MSTORE [off3; s_op];
       out_buf_alloc <- compile_alloc_buffer 32;
       out_buf <- return out_buf_alloc.buf_operand;
       (* Zero output buffer — ecrecover returns 0 bytes on invalid signature *)
       emit_void MSTORE [out_buf; Lit 0w];
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 1w; in_buf; Lit 128w; out_buf; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [out_buf]
    od
End

(* ecadd(x1, y1, x2, y2) → (x3, y3)
   Precompile at address 0x6
   Input: 4 × 32 = 128 bytes; Output: 2 × 32 = 64 bytes *)
Definition compile_ecadd_def:
  compile_ecadd x1 y1 x2 y2 =
    do in_buf_alloc <- compile_alloc_buffer 128;
       in_buf <- return in_buf_alloc.buf_operand;
       emit_void MSTORE [in_buf; x1];
       o1 <- emit_op ADD [in_buf; Lit 32w];
       emit_void MSTORE [o1; y1];
       o2 <- emit_op ADD [in_buf; Lit 64w];
       emit_void MSTORE [o2; x2];
       o3 <- emit_op ADD [in_buf; Lit 96w];
       emit_void MSTORE [o3; y2];
       out_buf_alloc <- compile_alloc_buffer 64;
       out_buf <- return out_buf_alloc.buf_operand;
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 6w; in_buf; Lit 128w; out_buf; Lit 64w];
       emit_void ASSERT [success];
       return out_buf
    od
End

(* ecmul(x, y, scalar) → (x', y')
   Precompile at address 0x7
   Input: 3 × 32 = 96 bytes; Output: 2 × 32 = 64 bytes *)
Definition compile_ecmul_def:
  compile_ecmul x y scalar =
    do in_buf_alloc <- compile_alloc_buffer 96;
       in_buf <- return in_buf_alloc.buf_operand;
       emit_void MSTORE [in_buf; x];
       o1 <- emit_op ADD [in_buf; Lit 32w];
       emit_void MSTORE [o1; y];
       o2 <- emit_op ADD [in_buf; Lit 64w];
       emit_void MSTORE [o2; scalar];
       out_buf_alloc <- compile_alloc_buffer 64;
       out_buf <- return out_buf_alloc.buf_operand;
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 7w; in_buf; Lit 96w; out_buf; Lit 64w];
       emit_void ASSERT [success];
       return out_buf
    od
End

(* ===== Block/Blob Hash ===== *)
(* Mirrors Python: misc.py lower_blockhash
   Validates block_num is in [block.number - 256, block.number).
   Reverts if out of range. *)
Definition compile_blockhash_def:
  compile_blockhash n_op =
    do current_block <- emit_op NUMBER [];
       lower_bound <- emit_op SUB [current_block; Lit 256w];
       (* Assert n >= lower_bound (signed comparison) *)
       too_old <- emit_op SLT [n_op; lower_bound];
       ok1 <- emit_op ISZERO [too_old];
       emit_void ASSERT [ok1];
       (* Assert n < current_block *)
       in_range <- emit_op LT [n_op; current_block];
       emit_void ASSERT [in_range];
       emit_op BLOCKHASH [n_op]
    od
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
  compile_floor val_op divisor =
    do is_neg <- emit_op SLT [val_op; Lit 0w];
       (* For negative: sub (divisor-1) to round toward -inf *)
       adjusted <- emit_op SUB [val_op; Lit (n2w (divisor - 1))];
       (* select: is_neg ? adjusted : val_op *)
       input <- compile_select is_neg adjusted val_op;
       emit_op SDIV [input; Lit (n2w divisor)]
    od
End

(* ceil(x): round decimal toward +infinity
   For positive: add (divisor-1) before dividing *)
Definition compile_ceil_def:
  compile_ceil val_op divisor =
    do is_pos <- emit_op SGT [val_op; Lit 0w];
       adjusted <- emit_op ADD [val_op; Lit (n2w (divisor - 1))];
       (* select: is_pos ? adjusted : val_op *)
       input <- compile_select is_pos adjusted val_op;
       emit_op SDIV [input; Lit (n2w divisor)]
    od
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
  compile_isqrt val_op =
    do (* Create mutable variables y and z *)
       y_var <- fresh_var;
       z_var <- fresh_var;
       emit_inst ASSIGN [val_op] [y_var];
       emit_inst ASSIGN [Lit 181w] [z_var];
       (* Scale 1: if y >= 2^136: y >>= 128, z <<= 64 *)
       cond1 <- emit_op LT [Var y_var; Lit (n2w (2 ** 136))];
       cond1_n <- emit_op ISZERO [cond1];
       new_y1 <- emit_op SHR [Lit 128w; Var y_var];
       new_z1 <- emit_op SHL [Lit 64w; Var z_var];
       (* select: cond1_n ? new_y1 : y *)
       sel_y1 <- compile_select cond1_n new_y1 (Var y_var);
       sel_z1 <- compile_select cond1_n new_z1 (Var z_var);
       emit_inst ASSIGN [sel_y1] [y_var];
       emit_inst ASSIGN [sel_z1] [z_var];
       (* Scale 2: if y >= 2^72: y >>= 64, z <<= 32 *)
       cond2 <- emit_op LT [Var y_var; Lit (n2w (2 ** 72))];
       cond2_n <- emit_op ISZERO [cond2];
       new_y2 <- emit_op SHR [Lit 64w; Var y_var];
       new_z2 <- emit_op SHL [Lit 32w; Var z_var];
       sel_y2 <- compile_select cond2_n new_y2 (Var y_var);
       sel_z2 <- compile_select cond2_n new_z2 (Var z_var);
       emit_inst ASSIGN [sel_y2] [y_var];
       emit_inst ASSIGN [sel_z2] [z_var];
       (* Scale 3: if y >= 2^40: y >>= 32, z <<= 16 *)
       cond3 <- emit_op LT [Var y_var; Lit (n2w (2 ** 40))];
       cond3_n <- emit_op ISZERO [cond3];
       new_y3 <- emit_op SHR [Lit 32w; Var y_var];
       new_z3 <- emit_op SHL [Lit 16w; Var z_var];
       sel_y3 <- compile_select cond3_n new_y3 (Var y_var);
       sel_z3 <- compile_select cond3_n new_z3 (Var z_var);
       emit_inst ASSIGN [sel_y3] [y_var];
       emit_inst ASSIGN [sel_z3] [z_var];
       (* Scale 4: if y >= 2^24: y >>= 16, z <<= 8 *)
       cond4 <- emit_op LT [Var y_var; Lit (n2w (2 ** 24))];
       cond4_n <- emit_op ISZERO [cond4];
       new_y4 <- emit_op SHR [Lit 16w; Var y_var];
       new_z4 <- emit_op SHL [Lit 8w; Var z_var];
       sel_y4 <- compile_select cond4_n new_y4 (Var y_var);
       sel_z4 <- compile_select cond4_n new_z4 (Var z_var);
       emit_inst ASSIGN [sel_y4] [y_var];
       emit_inst ASSIGN [sel_z4] [z_var];
       (* z = z * (y + 2^16) / 2^18 *)
       y_plus <- emit_op ADD [Var y_var; Lit (n2w (2 ** 16))];
       z_mul <- emit_op MUL [Var z_var; y_plus];
       z_scaled <- emit_op Div [z_mul; Lit (n2w (2 ** 18))];
       emit_inst ASSIGN [z_scaled] [z_var];
       (* 7 Newton iterations: z = (z + x/z) / 2 *)
       xdz1 <- emit_op Div [val_op; Var z_var];
       s1 <- emit_op ADD [xdz1; Var z_var];
       nz1 <- emit_op Div [s1; Lit 2w];
       emit_inst ASSIGN [nz1] [z_var];
       xdz2 <- emit_op Div [val_op; Var z_var];
       s2 <- emit_op ADD [xdz2; Var z_var];
       nz2 <- emit_op Div [s2; Lit 2w];
       emit_inst ASSIGN [nz2] [z_var];
       xdz3 <- emit_op Div [val_op; Var z_var];
       s3 <- emit_op ADD [xdz3; Var z_var];
       nz3 <- emit_op Div [s3; Lit 2w];
       emit_inst ASSIGN [nz3] [z_var];
       xdz4 <- emit_op Div [val_op; Var z_var];
       s4 <- emit_op ADD [xdz4; Var z_var];
       nz4 <- emit_op Div [s4; Lit 2w];
       emit_inst ASSIGN [nz4] [z_var];
       xdz5 <- emit_op Div [val_op; Var z_var];
       s5 <- emit_op ADD [xdz5; Var z_var];
       nz5 <- emit_op Div [s5; Lit 2w];
       emit_inst ASSIGN [nz5] [z_var];
       xdz6 <- emit_op Div [val_op; Var z_var];
       s6 <- emit_op ADD [xdz6; Var z_var];
       nz6 <- emit_op Div [s6; Lit 2w];
       emit_inst ASSIGN [nz6] [z_var];
       xdz7 <- emit_op Div [val_op; Var z_var];
       s7 <- emit_op ADD [xdz7; Var z_var];
       nz7 <- emit_op Div [s7; Lit 2w];
       emit_inst ASSIGN [nz7] [z_var];
       (* Final: t = x/z; return select(lt(z, t), z, t) *)
       t_op <- emit_op Div [val_op; Var z_var];
       lt_cond <- emit_op LT [Var z_var; t_op];
       compile_select lt_cond (Var z_var) t_op
    od
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
  compile_as_wei_value_int val_op scale is_signed =
    if scale = 1 then return val_op
    else
      do product <- emit_op MUL [val_op; Lit (n2w scale)];
         (* Overflow check: div(product, value) == denom || value == 0 *)
         quotient <- emit_op Div [product; val_op];
         is_safe <- emit_op EQ [quotient; Lit (n2w scale)];
         is_zero <- emit_op ISZERO [val_op];
         ok <- emit_op OR [is_safe; is_zero];
         (* For signed types: also check value >= 0 *)
         ok_final <-
           (if is_signed then
              do is_pos <- emit_op SLT [val_op; Lit 0w];
                 not_neg <- emit_op ISZERO [is_pos];
                 emit_op AND [not_neg; ok]
              od
            else return ok);
         emit_void ASSERT [ok_final];
         return product
      od
End

(* Decimal case *)
Definition compile_as_wei_value_decimal_def:
  compile_as_wei_value_decimal val_op scale decimal_divisor =
    do (* Assert non-negative *)
       neg <- emit_op SLT [val_op; Lit 0w];
       not_neg <- emit_op ISZERO [neg];
       emit_void ASSERT [not_neg];
       if scale = 1 then
         emit_op Div [val_op; Lit (n2w decimal_divisor)]
       else
         do product <- emit_op MUL [val_op; Lit (n2w scale)];
            emit_op Div [product; Lit (n2w decimal_divisor)]
         od
    od
End

(* NOTE: compile_min_value, compile_max_value, compile_epsilon deleted —
   exprLoweringScript inlines these as Lit values via type_bounds. *)

(* NOTE: compile_print, compile_breakpoint deleted — debug builtins
   not wired into the lowering pipeline. *)
