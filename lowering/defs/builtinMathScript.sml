(*
 * Unsafe Math Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_unsafe_add/sub/mul/div — unchecked arithmetic
 *   compile_pow_mod256     — unchecked exponentiation mod 2^256
 *   compile_addmod         — (a + b) % c via ADDMOD
 *   compile_mulmod         — (a * b) % c via MULMOD
 *   compile_shift          — generalized shift (deprecated)
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/math.py
 *)

Theory builtinMath
Ancestors
  builtinSimple emitHelper compileEnv venomInst
Libs
  monadsyntax

(* ===== Unsafe Binary Ops ===== *)
(* Mirrors Python: math.py _lower_unsafe_binop
   For sub-256-bit types, wraps result:
   - Unsigned: mask to bit width via AND
   - Signed: sign-extend via SIGNEXTEND *)

Definition compile_unsafe_binop_def:
  compile_unsafe_binop opc x y bits is_signed =
    do result <- emit_op opc [x; y];
       if bits < 256 then
         if is_signed then
           emit_op SIGNEXTEND [Lit (n2w (bits DIV 8 - 1)); result]
         else
           let mask = n2w (2 ** bits - 1) : bytes32 in
           emit_op AND [result; Lit mask]
       else
         return result
    od
End

Definition compile_unsafe_add_def:
  compile_unsafe_add x y bits is_signed =
    compile_unsafe_binop ADD x y bits is_signed
End

Definition compile_unsafe_sub_def:
  compile_unsafe_sub x y bits is_signed =
    compile_unsafe_binop SUB x y bits is_signed
End

Definition compile_unsafe_mul_def:
  compile_unsafe_mul x y bits is_signed =
    compile_unsafe_binop MUL x y bits is_signed
End

Definition compile_unsafe_div_def:
  compile_unsafe_div x y bits is_signed =
    compile_unsafe_binop (if is_signed then SDIV else Div) x y bits is_signed
End

(* ===== pow_mod256 ===== *)
(* Mirrors Python: math.py lower_pow_mod256
   EXP opcode directly, no overflow check *)
Definition compile_pow_mod256_def:
  compile_pow_mod256 base_op exp_op = emit_op Exp [base_op; exp_op]
End

(* ===== uint256_addmod ===== *)
(* Mirrors Python: math.py lower_uint256_addmod
   Assert divisor non-zero, then ADDMOD *)
Definition compile_addmod_def:
  compile_addmod a b c =
    do emit_void ASSERT [c];
       emit_op ADDMOD [a; b; c]
    od
End

(* ===== uint256_mulmod ===== *)
(* Mirrors Python: math.py lower_uint256_mulmod *)
Definition compile_mulmod_def:
  compile_mulmod a b c =
    do emit_void ASSERT [c];
       emit_op MULMOD [a; b; c]
    od
End

(* ===== shift ===== *)
(* Mirrors Python: math.py lower_shift
   Generalized shift: bits < 0 → right shift, bits >= 0 → left shift.
   Right shift uses SAR for signed, SHR for unsigned. *)
Definition compile_shift_def:
  compile_shift val_op bits_op is_signed =
    do is_neg <- emit_op SLT [bits_op; Lit 0w];
       neg_bits <- emit_op SUB [Lit 0w; bits_op];
       right_shifted <-
         (if is_signed then emit_op SAR [neg_bits; val_op]
          else emit_op SHR [neg_bits; val_op]);
       left_shifted <- emit_op SHL [bits_op; val_op];
       (* select: is_neg ? right_shifted : left_shifted *)
       compile_select is_neg right_shifted left_shifted
    od
End
