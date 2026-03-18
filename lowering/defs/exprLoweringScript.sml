(*
 * Expression Lowering: Vyper expressions → Venom IR instructions
 *
 * TOP-LEVEL:
 *   compile_expr                 — compile expression, return vyper_value
 *   lower_value                  — compile + unwrap to operand
 *   compile_builtin_dispatch     — dispatch builtin operations
 *   compile_type_builtin_dispatch — dispatch type-level builtins
 *   compile_call                 — internal/external/send calls
 *
 * Helper (arithmetic):
 *   compile_safe_add/sub/mul/div/mod/pow — arithmetic with overflow checks
 *   compile_mul_overflow_check   — MUL overflow check (extracted from safe_mul)
 *   clamp_and_return             — compile_clamp + return (shared by safe_add/sub/mul/div)
 *   compile_clamp                — range check for sub-256-bit types
 *   wrap_truncate                — wrapping truncation for UAdd/USub/UMul/UDiv
 *   compile_binop                — dispatch binop to appropriate helper
 *   compile_compare              — signed/unsigned comparison dispatch
 *
 * Helper (expression forms):
 *   compile_name_vv              — variable load from alloca
 *   compile_literal_vv           — literal to value/buffer
 *   compile_neg                  — unary negation with overflow check
 *   compile_type_convert         — type conversion dispatch
 *   load_bytestring_as_word      — shared preamble for ConvBytestring* variants
 *   compile_subscript            — array/mapping subscript
 *   compile_attribute            — struct/module attribute access
 *   compile_var_array_membership — variable-array In/NotIn (extracted from Bop)
 *
 * Mirrors Python codegen: ~/vyper/vyper/codegen_venom/{expr,arithmetic}.py
 *)

Theory exprLowering
Ancestors
  emitHelper compileEnv context valueEncoding venomInst vyperValueOperation
  builtinAbi builtinBytes builtinCreate
  builtinHashing builtinMath builtinMisc builtinSimple
  builtinStrings builtinSystem

(* NOTE: emit_op, emit_void, emit_inst, emit_jmp_if_not_terminated
   moved to emitHelper theory to break circular dependency with builtin theories.
   Type helpers (is_signed_type, is_decimal_type, decimal_divisor,
   type_bits, type_bounds) in compileEnv. *)

(* ===== Array Location Inference ===== *)
(* Infer array data location from expression AST + compile_env.
   Attribute(Name "self", field) → look up field in ce_vars → StorageLoc/TransientLoc.
   Name var → look up in ce_vars.
   Otherwise → LocMemory (default).
   Mirrors Python: array_vv.location or node.iter._expr_info.location
   Note: CalldataLoc not in var_location. Calldata params are ABI-decoded
   to memory at function entry, so LocMemory is correct for them. *)
Definition infer_array_location_def:
  infer_array_location cenv (Attribute _ (Name _ "self") field_name) =
    (case FLOOKUP cenv.ce_vars field_name of
       SOME (StorageLoc _) => LocStorage
     | SOME (TransientLoc _) => LocTransient
     | SOME (ImmutableLoc _) => LocCode
     | _ => LocMemory) ∧
  infer_array_location cenv (Name _ var_name) =
    (case FLOOKUP cenv.ce_vars var_name of
       SOME (StorageLoc _) => LocStorage
     | SOME (TransientLoc _) => LocTransient
     | SOME (ImmutableLoc _) => LocCode
     | _ => LocMemory) ∧
  infer_array_location cenv _ = LocMemory
End

(* Infer whether an array is dynamic (DynArray) or static (SArray).
   Mirrors Python: isinstance(array_typ, DArrayT) vs SArrayT *)
Definition infer_array_is_dynamic_def:
  infer_array_is_dynamic cenv (Name _ var_name) =
    (case cenv.ce_var_type var_name of
       SOME (ArrayT _ (Dynamic _)) => T
     | _ => F) ∧
  infer_array_is_dynamic cenv (Attribute _ (Name _ "self") field_name) =
    (case cenv.ce_var_type field_name of
       SOME (ArrayT _ (Dynamic _)) => T
     | _ => F) ∧
  infer_array_is_dynamic cenv _ = T  (* default: assume dynamic for safety *)
End

(* Compute memory_bytes_required for an AST type.
   Mirrors Python: VyperType.memory_bytes_required (base.py, subscriptable.py).
   BytesT/StringT: 32 (length word) + ceil32(max_length) (data area).
   Mirrors Python: bytestrings.py size_in_bytes = 32 + ceil32(self.length). *)
(* NOTE: type_memory_bytes, elem_size_in_location, is_bytestring_type
   moved to compileEnvScript.sml (context needs them for typed copy). *)

(* ===== Overflow Check: Clamp ===== *)

(* Assert value is within type bounds.
   Mirrors Python: arithmetic.py clamp_basetype *)
Definition compile_clamp_def:
  compile_clamp val_op ty st =
    let (lo, hi) = type_bounds ty in
    if is_signed_type ty then
      (* signed: iszero(slt(val, lo)) AND iszero(sgt(val, hi)) *)
      let (slt_lo, st1) = emit_op SLT [val_op; Lit lo] st in
      let (ge_lo, st2) = emit_op ISZERO [slt_lo] st1 in
      let (sgt_hi, st3) = emit_op SGT [val_op; Lit hi] st2 in
      let (le_hi, st4) = emit_op ISZERO [sgt_hi] st3 in
      let (ok, st5) = emit_op AND [ge_lo; le_hi] st4 in
      emit_void ASSERT [ok] st5
    else
      (* unsigned: iszero(gt(val, hi)) *)
      let (gt_hi, st1) = emit_op GT [val_op; Lit hi] st in
      let (ok, st2) = emit_op ISZERO [gt_hi] st1 in
      emit_void ASSERT [ok] st2
End

(* ===== Safe Arithmetic ===== *)
(* Mirrors Python: arithmetic.py safe_add/sub/mul/div/mod *)

(* Clamp result and return: used by safe_mul, safe_add, safe_sub, etc.
   For sub-256-bit or decimal types, apply compile_clamp before returning. *)
Definition clamp_and_return_def:
  clamp_and_return res ty st =
    let (_, st1) = compile_clamp res ty st in
    (res, st1)
End

(* Safe add: ADD + overflow check *)
Definition compile_safe_add_def:
  compile_safe_add x y ty st =
    let (res, st1) = emit_op ADD [x; y] st in
    let bits = type_bits ty in
    if bits < 256 then clamp_and_return res ty st1
    else if is_signed_type ty then
      (* 256-bit signed: (y < 0) == (res < x) *)
      let (y_neg, st2) = emit_op SLT [y; Lit 0w] st1 in
      let (res_lt_x, st3) = emit_op SLT [res; x] st2 in
      let (ok, st4) = emit_op EQ [y_neg; res_lt_x] st3 in
      let (_, st5) = emit_void ASSERT [ok] st4 in
      (res, st5)
    else
      (* 256-bit unsigned: res >= x, i.e. iszero(lt(res, x)) *)
      let (lt_res, st2) = emit_op LT [res; x] st1 in
      let (ok, st3) = emit_op ISZERO [lt_res] st2 in
      let (_, st4) = emit_void ASSERT [ok] st3 in
      (res, st4)
End

(* Safe sub: SUB + overflow check *)
Definition compile_safe_sub_def:
  compile_safe_sub x y ty st =
    let (res, st1) = emit_op SUB [x; y] st in
    let bits = type_bits ty in
    if bits < 256 then clamp_and_return res ty st1
    else if is_signed_type ty then
      (* 256-bit signed: (y < 0) == (res > x) *)
      let (y_neg, st2) = emit_op SLT [y; Lit 0w] st1 in
      let (res_gt_x, st3) = emit_op SGT [res; x] st2 in
      let (ok, st4) = emit_op EQ [y_neg; res_gt_x] st3 in
      let (_, st5) = emit_void ASSERT [ok] st4 in
      (res, st5)
    else
      (* 256-bit unsigned: res <= x, i.e. iszero(gt(res, x)) *)
      let (gt_res, st2) = emit_op GT [res; x] st1 in
      let (ok, st3) = emit_op ISZERO [gt_res] st2 in
      let (_, st4) = emit_void ASSERT [ok] st3 in
      (res, st4)
End

(* Safe mul: MUL + overflow check.
   For DecimalT: divide result by divisor after multiplication.
   For int256: also check not (x == MIN_INT ∧ y == -1).
   Mirrors Python: arithmetic.py safe_mul *)
(* Mul overflow check: (res / y == x) OR (y == 0).
   For int256: additionally check not (x == MIN_INT ∧ y == -1).
   Only needed for bits > 128 (smaller types can't overflow 256-bit MUL).
   Mirrors Python: arithmetic.py safe_mul overflow check *)
Definition compile_mul_overflow_check_def:
  compile_mul_overflow_check x y res is_signed bits st =
    let div_op = if is_signed then SDIV else Div in
    let (div_res, st1) = emit_op div_op [res; y] st in
    let (div_ok, st2) = emit_op EQ [div_res; x] st1 in
    let (y_zero, st3) = emit_op ISZERO [y] st2 in
    let (ok, st4) = emit_op OR [div_ok; y_zero] st3 in
    let (final_ok, st5) =
      if is_signed ∧ bits = 256 then
        let (x_min, st4a) = emit_op EQ [x; Lit (n2w (2 ** 255))] st4 in
        let (ny, st4b) = emit_op NOT [y] st4a in
        let (y_neg1, st4c) = emit_op ISZERO [ny] st4b in
        let (special, st4d) = emit_op AND [x_min; y_neg1] st4c in
        let (not_special, st4e) = emit_op ISZERO [special] st4d in
        emit_op AND [ok; not_special] st4e
      else (ok, st4) in
    emit_void ASSERT [final_ok] st5
End

Definition compile_safe_mul_def:
  compile_safe_mul x y ty st =
    let bits = type_bits ty in
    let is_signed = is_signed_type ty in
    let (res, st1) = emit_op MUL [x; y] st in
    let (_, st2) =
      if bits > 128 then
        compile_mul_overflow_check x y res is_signed bits st1
      else ((), st1) in
    let (res1, st3) =
      if is_decimal_type ty then
        emit_op (if is_signed then SDIV else Div)
          [res; Lit (n2w (decimal_divisor ty))] st2
      else (res, st2) in
    if bits < 256 ∨ is_decimal_type ty then clamp_and_return res1 ty st3
    else (res1, st3)
End

(* Safe div: check divisor ≠ 0, then DIV or SDIV *)
(* Integer floor division (//) with overflow check.
   For signed int256: check not (x == -2^255 ∧ y == -1).
   For smaller signed: clamp result to type bounds.
   Mirrors Python: arithmetic.py safe_floordiv *)
Definition compile_safe_div_def:
  compile_safe_div x y ty st =
    let (y_zero, st1) = emit_op ISZERO [y] st in
    let (y_nonzero, st2) = emit_op ISZERO [y_zero] st1 in
    let (_, st3) = emit_void ASSERT [y_nonzero] st2 in
    if is_signed_type ty then
      let (res, st4) = emit_op SDIV [x; y] st3 in
      if type_bits ty = 256 then
        (* int256: check not (x == MIN_INT ∧ y == -1) *)
        let (x_min, st5) = emit_op EQ [x; Lit (n2w (2 ** 255))] st4 in
        let (ny, st6) = emit_op NOT [y] st5 in
        let (y_neg1, st7) = emit_op ISZERO [ny] st6 in
        let (bad, st8) = emit_op AND [x_min; y_neg1] st7 in
        let (ok, st9) = emit_op ISZERO [bad] st8 in
        let (_, st10) = emit_void ASSERT [ok] st9 in
        (res, st10)
      else if type_bits ty < 256 then clamp_and_return res ty st4
      else (res, st4)
    else
      emit_op Div [x; y] st3
End

(* safe_div for decimal: scale numerator by divisor, then sdiv, then clamp.
   Mirrors Python: arithmetic.py safe_div (DecimalT branch) *)
Definition compile_safe_decimal_div_def:
  compile_safe_decimal_div x y divisor ty st =
    (* Scale: x * divisor *)
    let (x_scaled, st1) = emit_op MUL [x; Lit (n2w divisor)] st in
    (* Check divisor != 0 *)
    let (y_zero, st2) = emit_op ISZERO [y] st1 in
    let (y_nonzero, st3) = emit_op ISZERO [y_zero] st2 in
    let (_, st4) = emit_void ASSERT [y_nonzero] st3 in
    let (res, st5) = emit_op SDIV [x_scaled; y] st4 in
    clamp_and_return res ty st5
End

(* Safe mod: check divisor ≠ 0, then MOD or SMOD *)
Definition compile_safe_mod_def:
  compile_safe_mod x y ty st =
    let (y_zero, st1) = emit_op ISZERO [y] st in
    let (y_nonzero, st2) = emit_op ISZERO [y_zero] st1 in
    let (_, st3) = emit_void ASSERT [y_nonzero] st2 in
    if is_signed_type ty then emit_op SMOD [x; y] st3
    else emit_op Mod [x; y] st3
End

(* safe_pow: exponentiation with post-clamp overflow check.
   Mirrors Python: arithmetic.py safe_pow
   KNOWN LIMITATION: For 256-bit types (uint256/int256), compile_clamp is
   vacuous (full-range), so overflow wraps silently. Python avoids this by
   requiring at least one literal operand and precomputing tight bounds
   (calculate_largest_base/calculate_largest_power). The HOL4 model lacks
   compile-time literal detection, so cannot implement the pre-check.
   For sub-256-bit types, the post-clamp correctly catches overflow. *)
Definition compile_safe_pow_def:
  compile_safe_pow x y ty st =
    let (res, st1) = emit_op Exp [x; y] st in
    let (_, st2) = compile_clamp res ty st1 in
    (res, st2)
End

(* ===== Comparison ===== *)

(* NOTE: struct_field_offset, struct_field_offset_slots, is_uint256
   moved to compileEnv *)

(* Compile comparison, choosing signed/unsigned based on type.
   Mirrors Python: expr.py lower_Compare *)

Definition compile_compare_def:
  compile_compare op x y ty st =
    let use_signed = ¬(is_uint256 ty) in
    case op of
      Lt => if use_signed then emit_op SLT [x; y] st else emit_op LT [x; y] st
    | Gt => if use_signed then emit_op SGT [x; y] st else emit_op GT [x; y] st
    | Eq => emit_op EQ [x; y] st
    | NotEq =>
        let (eq_res, st1) = emit_op EQ [x; y] st in
        emit_op ISZERO [eq_res] st1
    | LtE =>
        (* le = iszero(gt) *)
        let (gt_res, st1) =
          if use_signed then emit_op SGT [x; y] st
          else emit_op GT [x; y] st in
        emit_op ISZERO [gt_res] st1
    | GtE =>
        (* ge = iszero(lt) *)
        let (lt_res, st1) =
          if use_signed then emit_op SLT [x; y] st
          else emit_op LT [x; y] st in
        emit_op ISZERO [lt_res] st1
    | _ => let (_, st') = emit_inst INVALID [] [] st in (Lit 0w, st')
End

(* ===== Binop Dispatch ===== *)

(* Wrapping truncation for sub-256-bit types.
   Signed → SIGNEXTEND to sign-extend from byte boundary.
   Unsigned → AND with bit mask.
   Used by UAdd/USub/UMul/UDiv (wrapping arithmetic).
   Mirrors Python: builtins/math.py _lower_unsafe_binop truncation *)
Definition wrap_truncate_def:
  wrap_truncate res ty st =
    if type_bits ty < 256 then
      if is_signed_type ty then
        emit_op SIGNEXTEND [Lit (n2w (type_bits ty DIV 8 - 1)); res] st
      else emit_op AND [res; Lit (n2w (2 ** type_bits ty - 1))] st
    else (res, st)
End

(* Dispatch binary operation to appropriate compilation.
   Mirrors Python: arithmetic.py apply_binop *)
Definition compile_binop_def:
  compile_binop op x y ty st =
    case op of
    (* Checked arithmetic *)
      Add => compile_safe_add x y ty st
    | Sub => compile_safe_sub x y ty st
    | Mul => compile_safe_mul x y ty st
    | Div => if is_decimal_type ty
             then compile_safe_decimal_div x y (decimal_divisor ty) ty st
             else compile_safe_div x y ty st
    | Mod => compile_safe_mod x y ty st
    (* Wrapping arithmetic (no overflow checks).
       For bits < 256: signed → SIGNEXTEND, unsigned → AND mask.
       UDiv is unchecked (no zero-divisor ASSERT), dispatches SDIV for signed.
       Mirrors Python: builtins/math.py _lower_unsafe_binop *)
    | UAdd => let (res, st1) = emit_op ADD [x; y] st in wrap_truncate res ty st1
    | USub => let (res, st1) = emit_op SUB [x; y] st in wrap_truncate res ty st1
    | UMul => let (res, st1) = emit_op MUL [x; y] st in wrap_truncate res ty st1
    | UDiv =>
        let opc = if is_signed_type ty then SDIV else Div in
        let (res, st1) = emit_op opc [x; y] st in wrap_truncate res ty st1
    (* Bitwise *)
    | And => emit_op AND [x; y] st
    | Or => emit_op OR [x; y] st
    | XOr => emit_op XOR [x; y] st
    (* Shifts: SHL/SHR take (shift_amount, value) in EVM *)
    | ShL => emit_op SHL [y; x] st
    | ShR =>
        if is_signed_type ty then emit_op SAR [y; x] st
        else emit_op SHR [y; x] st
    (* Comparisons *)
    | Eq => compile_compare Eq x y ty st
    | NotEq => compile_compare NotEq x y ty st
    | Lt => compile_compare Lt x y ty st
    | LtE => compile_compare LtE x y ty st
    | Gt => compile_compare Gt x y ty st
    | GtE => compile_compare GtE x y ty st
    (* Exp: safe_pow with post-clamp (see compile_safe_pow KNOWN LIMITATION) *)
    | Exp => compile_safe_pow x y ty st
    (* Min/Max: branchless select with signed/unsigned dispatch.
       Python: simple.py _lower_minmax uses LT/SLT for min, GT/SGT for max.
       Uses unsigned (LT/GT) only for uint256, signed (SLT/SGT) for all others.
       select(cond, a, b) = xor(b, mul(cond, xor(a, b))) *)
    | Min =>
        let (cmp, st1) =
          if is_uint256 ty then emit_op LT [x; y] st
          else emit_op SLT [x; y] st in
        compile_select cmp x y st1
    | Max =>
        let (cmp, st1) =
          if is_uint256 ty then emit_op GT [x; y] st
          else emit_op SGT [x; y] st in
        compile_select cmp x y st1
    (* Membership: In/NotIn for flags (bitwise AND test).
       Array membership requires loop — handled separately via
       compile_array_membership_loop. *)
    | In =>
        (* Flag membership: iszero(iszero(x AND y)) *)
        let (inter, st1) = emit_op AND [x; y] st in
        let (z, st2) = emit_op ISZERO [inter] st1 in
        emit_op ISZERO [z] st2
    | NotIn =>
        (* Flag non-membership: iszero(x AND y) *)
        let (inter, st1) = emit_op AND [x; y] st in
        emit_op ISZERO [inter] st1
    (* Remaining ops: emit INVALID (unreachable if type-correct) *)
    | _ => let (_, st') = emit_inst INVALID [] [] st in (Lit 0w, st')
End

(* ===== Bytestring Hash ===== *)
(* Get keccak256 hash for bytestring comparison.
   For constant literals: hash is a compile-time literal.
   For variables: runtime SHA3.
   Mirrors Python: expr.py _get_bytestring_hash *)
Definition compile_bytestring_hash_def:
(* Hash a bytestring for comparison or log topics.
   For memory: data at ptr+32, length at MLOAD(ptr).
   For storage/transient: must copy to memory first (SHA3 reads memory).
   Currently only handles memory path; storage bytestrings need
   compile_ensure_in_memory first. Callers of compile_bytestring_hash
   should ensure the bytestring is in memory before calling.
   Mirrors Python: ctx.ensure_bytestring_in_memory → sha3 *)
  compile_bytestring_hash ptr_op st =
    let (data_ptr, st1) = emit_op ADD [ptr_op; Lit 32w] st in
    let (length, st2) = emit_op MLOAD [ptr_op] st1 in
    emit_op SHA3 [data_ptr; length] st2
End

(* ===== List Literal Membership (unrolled) ===== *)
(* x in [a, b, c] = (x==a) or (x==b) or (x==c)
   x not in [a, b, c] = (x!=a) and (x!=b) and (x!=c)
   Mirrors Python: expr.py _lower_list_literal_membership *)
(* Combine membership comparisons: fold OR for "in", fold AND-ISZERO for "not in" *)
Definition compile_list_membership_in_def:
  compile_list_membership_in needle [] st =
    (Lit 0w, st) ∧
  compile_list_membership_in needle [elem] st =
    emit_op EQ [needle; elem] st ∧
  compile_list_membership_in needle (elem::rest) st =
    (let (eq_res, st1) = emit_op EQ [needle; elem] st in
     let (rest_res, st2) = compile_list_membership_in needle rest st1 in
     emit_op OR [eq_res; rest_res] st2)
End

Definition compile_list_membership_notin_def:
  compile_list_membership_notin needle [] st =
    (Lit 1w, st) ∧
  compile_list_membership_notin needle [elem] st =
    (let (eq_res, st1) = emit_op EQ [needle; elem] st in
     emit_op ISZERO [eq_res] st1) ∧
  compile_list_membership_notin needle (elem::rest) st =
    (let (eq_res, st1) = emit_op EQ [needle; elem] st in
     let (neq_res, st2) = emit_op ISZERO [eq_res] st1 in
     let (rest_res, st3) = compile_list_membership_notin needle rest st2 in
     emit_op AND [neq_res; rest_res] st3)
End

(* ===== Array Membership ===== *)

(* x in array: loop with early break.
   result = 0; for i in 0..len: if arr[i]==x: result=1, break.
   For "not in": return iszero(result).
   Mirrors Python: expr.py _lower_array_membership *)
Definition compile_array_membership_loop_def:
  compile_array_membership_loop needle arr_op len_op
      elem_size offset_base load_opc is_in st =
    (* Pre-allocate result variable *)
    let (result_var, st1) = fresh_var st in
    (* Create blocks *)
    let (entry_lbl, st2) = fresh_label "in_entry" st1 in
    let (cond_lbl, st3) = fresh_label "in_cond" st2 in
    let (body_lbl, st4) = fresh_label "in_body" st3 in
    let (found_lbl, st5) = fresh_label "in_found" st4 in
    let (incr_lbl, st6) = fresh_label "in_incr" st5 in
    let (exit_lbl, st7) = fresh_label "in_exit" st6 in
    (* Jump to entry *)
    let (_, st8) = emit_inst JMP [Label entry_lbl] [] st7 in
    (* Entry: idx = 0, result = 0 *)
    let (_, st9) = new_block entry_lbl st8 in
    let (idx_var, st10) = fresh_var st9 in
    let (_, st11) = emit_inst ASSIGN [Lit 0w] [idx_var] st10 in
    let (_, st12) = emit_inst ASSIGN [Lit 0w] [result_var] st11 in
    let (_, st13) = emit_inst JMP [Label cond_lbl] [] st12 in
    (* Cond: check idx == length *)
    let (_, st14) = new_block cond_lbl st13 in
    let (done_op, st15) = emit_op EQ [Var idx_var; len_op] st14 in
    let (_, st16) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st15 in
    (* Body: load elem, compare.
       Uses elem_size (not word_scale) for element stride.
       Uses offset_base for DynArray length-word skip.
       Uses load_opc for location-aware load (MLOAD/SLOAD/TLOAD).
       Mirrors Python: expr.py _lower_array_membership body block *)
    let (_, st17) = new_block body_lbl st16 in
    let (idx_offset, st18) =
      emit_op MUL [Var idx_var; Lit (n2w elem_size)] st17 in
    let (total_offset, st19) =
      if offset_base > 0 then
        emit_op ADD [Lit (n2w offset_base); idx_offset] st18
      else (idx_offset, st18) in
    let (elem_addr, st20) = emit_op ADD [arr_op; total_offset] st19 in
    let (elem_val, st21) = emit_op load_opc [elem_addr] st20 in
    let (match_op, st22) = emit_op EQ [elem_val; needle] st21 in
    let (_, st23) = emit_inst JNZ [match_op; Label found_lbl; Label incr_lbl] [] st22 in
    (* Found: result = 1, jump to exit *)
    let (_, st24) = new_block found_lbl st23 in
    let (_, st25) = emit_inst ASSIGN [Lit 1w] [result_var] st24 in
    let (_, st26) = emit_inst JMP [Label exit_lbl] [] st25 in
    (* Incr: idx++ *)
    let (_, st27) = new_block incr_lbl st26 in
    let (new_idx, st28) = emit_op ADD [Var idx_var; Lit 1w] st27 in
    let (_, st29) = emit_inst ASSIGN [new_idx] [idx_var] st28 in
    let (_, st30) = emit_inst JMP [Label cond_lbl] [] st29 in
    (* Exit: return result or iszero(result) *)
    let (_, st31) = new_block exit_lbl st30 in
    if is_in then (Var result_var, st31)
    else emit_op ISZERO [Var result_var] st31
End

(* Variable-array membership: compute metadata from venom_value and call loop.
   Extracts element size, load opcode, offset base, length from the array type.
   Mirrors Python: expr.py lower_Compare In/NotIn variable-array path *)
Definition compile_var_array_membership_def:
  compile_var_array_membership cenv needle arr_vv rhs_ty is_in st =
    let arr_op = vv_operand arr_vv in
    let loc = (case vv_location arr_vv of
                 SOME l => l | NONE => LocMemory) in
    let ws = word_scale loc in
    let is_dyn = (case rhs_ty of ArrayT _ (Dynamic _) => T | _ => F) in
    let elem_ty = (case rhs_ty of ArrayT t _ => t
                   | _ => BaseT (UintT 256)) in
    let elem_sz = elem_size_in_location cenv loc elem_ty in
    let load_opc = (case loc of
        LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD) in
    let offset_base = if is_dyn then ws else 0 in
    let (len_op, st1) = if is_dyn then
        emit_op load_opc [arr_op] st
      else
        (case rhs_ty of
           ArrayT _ (Fixed n) => (Lit (n2w n), st)
         | _ => (Lit 0w, st)) in
    (* DynArray bounds check: assert length <= capacity *)
    let st2 = (if is_dyn then
      case rhs_ty of
        ArrayT _ (Dynamic cap) =>
          let (inv, sta) = emit_op GT [len_op; Lit (n2w cap)] st1 in
          let (valid, stb) = emit_op ISZERO [inv] sta in
          let (_, stc) = emit_inst ASSERT [valid] [] stb in
          stc
      | _ => st1
      else st1) in
    compile_array_membership_loop needle arr_op len_op
      elem_sz offset_base load_opc is_in st2
End

(* ===== Mapping Subscript ===== *)
(* Compute storage slot for mapping[key]: keccak256(slot || key).
   Both slot and key are 32 bytes, concatenated at scratch memory, then hashed.
   Mirrors Python: expr.py _lower_mapping_subscript *)
Definition compile_mapping_subscript_def:
  compile_mapping_subscript base_slot key_op st =
    (* Allocate 64-byte scratch for keccak256 input *)
        let (buf_op_alloc, st2) = compile_alloc_buffer 64 st in
        let buf_op = buf_op_alloc.buf_operand in
    (* Store slot at buf[0:32] *)
    let (_, st3) = emit_void MSTORE [buf_op; base_slot] st2 in
    (* Store key at buf[32:64] *)
    let (key_ptr, st4) = emit_op ADD [buf_op; Lit 32w] st3 in
    let (_, st5) = emit_void MSTORE [key_ptr; key_op] st4 in
    (* Hash *)
    emit_op SHA3 [buf_op; Lit 64w] st5
End

(* ===== Keccak256 Key for Mapping ===== *)
(* Hash a bytes/string key for mapping access.
   For bytes32: mstore + sha3.
   For bytes/string: sha3 over data portion.
   Mirrors Python: expr.py _lower_keccak256_key *)
Definition compile_keccak256_key_def:
  compile_keccak256_key key_op is_bytes32 st =
    if is_bytes32 then
            let (buf_op_alloc, st2) = compile_alloc_buffer 32 st in
            let buf_op = buf_op_alloc.buf_operand in
      let (_, st3) = emit_void MSTORE [buf_op; key_op] st2 in
      emit_op SHA3 [buf_op; Lit 32w] st3
    else
      (* key_op is ptr to [length][data] *)
      let (data_ptr, st1) = emit_op ADD [key_op; Lit 32w] st in
      let (length, st2) = emit_op MLOAD [key_op] st1 in
      emit_op SHA3 [data_ptr; length] st2
End

(* NOTE: compile_short_circuit_and/or removed — dead code.
   BoolOp is desugared to IfExp in jsonToVyperScript.sml (And→IfExp a b 0,
   Or→IfExp a 1 b). The IfExp path in compile_expr handles short-circuit. *)

(* ===== External Call (full) ===== *)
(* Full external call: pack args with method ID, dispatch CALL/STATICCALL,
   propagate revert on failure, ABI decode return.
   Mirrors Python: expr.py _lower_external_call *)

(* Check that contract address has code. Used for external calls when
   function returns nothing and skip_contract_check is False.
   Without this, calling an empty address succeeds silently.
   Mirrors Python: expr.py L1806-1809 extcodesize check *)
Definition compile_extcodesize_check_def:
  compile_extcodesize_check addr_op st =
    let (codesize_op, st1) = emit_op EXTCODESIZE [addr_op] st in
    emit_void ASSERT [codesize_op] st1
End

(* NOTE: compile_external_call deleted — superseded by
   compile_external_call_kwargs which handles all kwargs. *)

(* ===== Return Value Decode ===== *)
(* Decode return value from external call buffer.
   Check returndatasize >= min_return_size, then compute hi bound for ABI decode.
   Mirrors Python: expr.py _lower_external_call decode path *)
Definition compile_return_value_decode_def:
  compile_return_value_decode buf_op min_return_size max_return_size st =
    let (rds, st1) = emit_op RETURNDATASIZE [] st in
    let (too_small, st2) = emit_op LT [rds; Lit (n2w min_return_size)] st1 in
    let (ok, st3) = emit_op ISZERO [too_small] st2 in
    let (_, st4) = emit_void ASSERT [ok] st3 in
    (* Compute payload bound = min(returndatasize, max_return_size).
       select(cond, rds, max): cond=1 when rds<max → take rds *)
    let (is_smaller, st5) = emit_op LT [rds; Lit (n2w max_return_size)] st4 in
    let (payload_bound, st6) = compile_select is_smaller rds
                                 (Lit (n2w max_return_size)) st5 in
    (* hi = buf + payload_bound (cap for ABI decode reads) *)
    emit_op ADD [buf_op; payload_bound] st6
End

(* ===== Default Return Value Path ===== *)
(* Handle default_return_value for external calls:
   if returndatasize == 0, use default; else do normal decode.
   Also checks extcodesize if not skip_contract_check.
   Mirrors Python: expr.py _lower_external_call default_return_value path *)
Definition compile_default_return_path_def:
  compile_default_return_path buf_op result_op default_op addr_op
                              skip_contract_check min_return_size
                              max_return_size ret_mem_bytes
                              ret_dec_info is_prim_return st =
    let (rds, st1) = emit_op RETURNDATASIZE [] st in
    let (is_zero, st2) = emit_op ISZERO [rds] st1 in
    let (default_lbl, st3) = fresh_label "extcall_default" st2 in
    let (decode_lbl, st4) = fresh_label "extcall_decode" st3 in
    let (exit_lbl, st5) = fresh_label "extcall_exit" st4 in
    let (_, st6) = emit_inst JNZ [is_zero; Label default_lbl;
                                  Label decode_lbl] [] st5 in
    (* Default block: store default value to result.
       Mirrors Python: ctx.store_memory(default_val, result_op, return_t)
       Prim: MSTORE; Complex: MCOPY. *)
    let (_, st7) = new_block default_lbl st6 in
    let (_, st8) =
      if is_prim_return then emit_void MSTORE [result_op; default_op] st7
      else emit_void MCOPY [result_op; default_op;
                            Lit (n2w ret_mem_bytes)] st7 in
    (* Extcodesize check in default path if not skipped *)
    let (_, st9) =
      if skip_contract_check then ((), st8)
      else compile_extcodesize_check addr_op st8 in
    let (_, st10) = emit_inst JMP [Label exit_lbl] [] st9 in
    (* Decode block: full ABI decode from buf to result.
       Mirrors Python: abi_decode_to_buf(ctx, result_val.operand, src, hi=hi) *)
    let (_, st11) = new_block decode_lbl st10 in
    let (hi_op, st12) = compile_return_value_decode buf_op min_return_size
                                                     max_return_size st11 in
    let (_, st12a) = compile_abi_decode_to_buf result_op buf_op MLOAD
                       hi_op ret_dec_info st12 in
    let (_, st13) = emit_inst JMP [Label exit_lbl] [] st12a in
    (* Exit block *)
    let (_, st14) = new_block exit_lbl st13 in
    (result_op, st14)
End

(* ===== Full External Call with Kwargs ===== *)
(* External call with full kwargs support: value, gas, skip_contract_check,
   default_return_value.
   call_value: operand for msg.value (Lit 0w if not payable)
   gas_op: operand for gas limit (GAS opcode result if not specified)
   skip_check: T to skip extcodesize check
   has_default: T if default_return_value provided
   default_op: operand for default return value (only used if has_default)
   Mirrors Python: expr.py _lower_external_call + _parse_external_call_kwargs *)
Definition compile_external_call_kwargs_def:
  compile_external_call_kwargs addr_op args_op args_abi_size method_id_val
                               return_abi_size min_return_size ret_mem_bytes
                               use_staticcall call_value gas_op
                               skip_check has_default default_op
                               is_prim_return
                               args_enc_info ret_dec_info st =
    (* Allocate buffer *)
    let buf_size = (if args_abi_size > return_abi_size
                    then args_abi_size else return_abi_size) + 32 in
        let (buf_op_alloc, st2) = compile_alloc_buffer buf_size st in
        let buf_op = buf_op_alloc.buf_operand in
    (* Store method ID *)
    let (_, st3) = emit_void MSTORE [buf_op; Lit (n2w method_id_val)] st2 in
    (* ABI-encode args from memory-layout buffer to buf+32.
       Replaces previous MCOPY which was only correct for word types.
       Mirrors Python: abi_encode_to_buf(ctx, encode_dst, args_val.operand, args_tuple_t) *)
    let (args_dst, st4) = emit_op ADD [buf_op; Lit 32w] st3 in
    let (_, st5) = compile_abi_encode_to_buf args_dst args_op args_enc_info st4 in
    let (call_offset, st6) = emit_op ADD [buf_op; Lit 28w] st5 in
    let call_len = Lit (n2w (4 + args_abi_size)) in
    let ret_len = Lit (n2w return_abi_size) in
    (* Extcodesize check for void calls without skip_contract_check *)
    let (_, st7) =
      if return_abi_size = 0 ∧ ¬skip_check then
        compile_extcodesize_check addr_op st6
      else ((), st6) in
    (* Dispatch CALL or STATICCALL with explicit gas *)
    let (success, st8) =
      if use_staticcall then
        emit_op STATICCALL [gas_op; addr_op; call_offset; call_len;
                            buf_op; ret_len] st7
      else
        emit_op CALL [gas_op; addr_op; call_value;
                      call_offset; call_len; buf_op; ret_len] st7 in
    (* Revert propagation *)
    let (fail_lbl, st9) = fresh_label "extcall_fail" st8 in
    let (cont_lbl, st10) = fresh_label "extcall_cont" st9 in
    let (_, st11) = emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [] st10 in
    let (_, st12) = new_block fail_lbl st11 in
    let (rds, st13) = emit_op RETURNDATASIZE [] st12 in
    let (_, st14) = emit_void RETURNDATACOPY [Lit 0w; Lit 0w; rds] st13 in
    let (_, st15) = emit_inst REVERT [Lit 0w; rds] [] st14 in
    let (_, st16) = new_block cont_lbl st15 in
    (* Return value handling *)
    if return_abi_size = 0 then
      (Lit 0w, st16)
    else if has_default then
      (* Allocate result, use default_return_path *)
            let (result_op_alloc, st18) = compile_alloc_buffer return_abi_size st16 in
            let result_op = result_op_alloc.buf_operand in
      compile_default_return_path buf_op result_op default_op addr_op
                                  skip_check min_return_size return_abi_size
                                  ret_mem_bytes ret_dec_info is_prim_return st18
    else
      (* Simple decode path: check returndatasize, ABI-decode to result buffer.
         Mirrors Python: abi_decode_to_buf(ctx, result_val.operand, src, hi=hi) *)
            let (result_op_alloc, st18) = compile_alloc_buffer return_abi_size st16 in
            let result_op = result_op_alloc.buf_operand in
      let (hi_op, st19) = compile_return_value_decode buf_op min_return_size
                                                       return_abi_size st18 in
      let (_, st20) = compile_abi_decode_to_buf result_op buf_op MLOAD
                        hi_op ret_dec_info st19 in
      (result_op, st20)
End

(* ===== DynArray Append (location-aware) ===== *)
(* Full dynarray append with overlap detection and location-aware store.
   word_scale: 1 for storage/transient, 32 for memory
   elem_size: size of element in location units
   capacity: compile-time max length
   is_prim: T for primitive single-word types
   store_opc: MSTORE, SSTORE, or TSTORE
   load_opc: MLOAD, SLOAD, or TLOAD
   Mirrors Python: expr.py _lower_dynarray_append *)
Definition compile_dynarray_append_def:
  compile_dynarray_append cenv base_op val_op word_scale elem_size
                               dst_elem_ty src_elem_ty
                               capacity is_prim
                               (load_opc : opcode) (store_opc : opcode) st =
    (* Load current length *)
    let (len_op, st1) = emit_op load_opc [base_op] st in
    (* Bounds check: length < capacity *)
    let (valid, st2) = emit_op LT [len_op; Lit (n2w capacity)] st1 in
    let (_, st3) = emit_void ASSERT [valid] st2 in
    (* elem_ptr = base + overhead + len * elem_size *)
    let overhead = word_scale in
    let (data_ptr, st4) = emit_op ADD [base_op; Lit (n2w overhead)] st3 in
    let (offset, st5) = emit_op MUL [len_op; Lit (n2w elem_size)] st4 in
    let (elem_ptr, st6) = emit_op ADD [data_ptr; offset] st5 in
    (* Store element.
       For primitive types, single-word store.
       For complex types, val_op is a memory pointer — need multi-word copy.
       Memory destination: use typed copy (compile_store_memory_typed).
       Storage/transient: use word copy loop.
       Mirrors Python: _lower_dynarray_append elem dispatch *)
    let st7 =
      if is_prim then SND (emit_void store_opc [elem_ptr; val_op] st6)
      else
        let dst_loc = (case store_opc of
                         SSTORE => LocStorage
                       | TSTORE => LocTransient
                       | _ => LocMemory) in
        if dst_loc = LocMemory then
          (* Memory destination uses typed copy, matching Python's
             ctx.store_memory(elem_val, elem_ptr, elem_typ, src_typ=...) *)
          SND (compile_store_memory_typed cenv elem_ptr dst_elem_ty
                                          val_op src_elem_ty st6)
        else
          (* Storage/transient: word-by-word copy.
             Matches Python's ctx.store_storage / ctx.store_transient *)
          let word_count = elem_size DIV word_scale in
          SND (compile_word_copy_loop val_op elem_ptr word_count
                                      LocMemory dst_loc F st6) in
    (* Increment and store new length *)
    let (new_len, st8) = emit_op ADD [len_op; Lit 1w] st7 in
    emit_void store_opc [base_op; new_len] st8
End

(* ===== DynArray Pop (location-aware) ===== *)
(* Full dynarray pop with location-aware load.
   Returns element pointer for complex types, loaded value for primitives.
   SEMANTIC DIFFERENCE: The Vyper interpreter zeros the popped element slot
   (write_storage_slot ... default_value). This lowering does NOT zero it,
   matching the Python compiler behavior. The popped slot contains stale data,
   but is inaccessible (past the length). Gas accounting differs: interpreter
   gets SSTORE refund for clearing, lowering does not.
   Mirrors Python: expr.py _lower_dynarray_pop *)
Definition compile_dynarray_pop_def:
  compile_dynarray_pop base_op word_scale elem_size
                            (load_opc : opcode) (store_opc : opcode) st =
    (* Load current length *)
    let (len_op, st1) = emit_op load_opc [base_op] st in
    (* Assert length > 0 *)
    let (nz, st2) = emit_op ISZERO [len_op] st1 in
    let (valid, st3) = emit_op ISZERO [nz] st2 in
    let (_, st4) = emit_void ASSERT [valid] st3 in
    (* new_len = len - 1 *)
    let (new_len, st5) = emit_op SUB [len_op; Lit 1w] st4 in
    (* Store new length *)
    let (_, st6) = emit_void store_opc [base_op; new_len] st5 in
    (* elem_ptr = base + overhead + new_len * elem_size *)
    let overhead = word_scale in
    let (data_ptr, st7) = emit_op ADD [base_op; Lit (n2w overhead)] st6 in
    let (offset, st8) = emit_op MUL [new_len; Lit (n2w elem_size)] st7 in
    emit_op ADD [data_ptr; offset] st8
End

(* ===== Internal Call with Return Buffer ===== *)
(* Stage internal call arguments based on pass_via_stack classification.
   For stack-passed args: use value directly (load from memory if struct/tuple).
   For memory-passed args: allocate buffer, copy value, pass pointer.
   Mirrors Python: expr.py _lower_internal_call arg staging loop *)
(* ABI return size for external call return type.
   NoneT (void) → 0, BaseT → 32, complex → type_memory_bytes *)

(* Convert a Vyper type to ABI encoding info.
   Mirrors Python: construction of abi_type from VyperType, then dispatch.
   KNOWN LIMITATION: StructT uses AbiCopy fallback (no field type info).
   To encode structs properly, need ce_struct_field_types. *)
Definition type_to_abi_enc_info_def:
  type_to_abi_enc_info cenv (BaseT (BytesT (Dynamic n))) = AbiBytestring n ∧
  type_to_abi_enc_info cenv (BaseT (StringT n)) = AbiBytestring n ∧
  type_to_abi_enc_info cenv (ArrayT elem (Dynamic n)) =
    AbiDynArray (type_to_abi_enc_info cenv elem)
      (abi_embedded_static_size (cenv_sft cenv) elem) (type_memory_bytes cenv elem)
      (is_abi_dynamic (cenv_sft cenv) elem) ∧
  type_to_abi_enc_info cenv (ArrayT elem (Fixed n)) =
    AbiComplex (GENLIST (K (type_to_abi_enc_info cenv elem,
                              abi_embedded_static_size (cenv_sft cenv) elem,
                              type_memory_bytes cenv elem,
                              is_abi_dynamic (cenv_sft cenv) elem)) n) ∧
  type_to_abi_enc_info cenv (TupleT tys) =
    AbiComplex (MAP (λt. (type_to_abi_enc_info cenv t,
                          abi_embedded_static_size (cenv_sft cenv) t,
                          type_memory_bytes cenv t,
                          is_abi_dynamic (cenv_sft cenv) t)) tys) ∧
  (* StructT uses per-field recursive encoding, same as TupleT.
     Mirrors Python: StructT.abi_type is ABI_Tuple(field_types). *)
  type_to_abi_enc_info cenv (StructT name) =
    AbiComplex (MAP (λ(fn, fty, sz).
                       (type_to_abi_enc_info cenv fty,
                        abi_embedded_static_size (cenv_sft cenv) fty,
                        type_memory_bytes cenv fty,
                        is_abi_dynamic (cenv_sft cenv) fty))
                    (cenv.ce_struct_fields name)) ∧
  type_to_abi_enc_info cenv _ = AbiPrimWord
Termination
  cheat
End

(* ABI clamp info from type — used for decoding validation.
   Mirrors Python: abi clamp logic based on type bounds. *)
Definition type_to_abi_clamp_def:
  type_to_abi_clamp (BaseT BoolT) = BoolClamp ∧
  type_to_abi_clamp (BaseT AddressT) = IntClamp 160 F ∧
  type_to_abi_clamp (BaseT (UintT n)) =
    (if n = 256 then NoClamp else IntClamp n F) ∧
  type_to_abi_clamp (BaseT (IntT n)) =
    (if n = 256 then NoClamp else IntClamp n T) ∧
  type_to_abi_clamp (BaseT DecimalT) = IntClamp 168 T ∧
  type_to_abi_clamp (BaseT (BytesT (Fixed n))) =
    (if n = 32 then NoClamp else BytesMClamp n) ∧
  (* FlagT needs cenv for n_members — handled by type_to_abi_dec_info directly.
     This catch-all is conservative; callers with cenv should use type_to_abi_dec_info. *)
  type_to_abi_clamp (FlagT _) = NoClamp ∧
  type_to_abi_clamp _ = NoClamp
End

(* Convert a Vyper type to ABI decoding info.
   Mirrors Python: construction of decode info for ABI decoding.
   StructT uses per-field recursive decoding. *)
Definition type_to_abi_dec_info_def:
  type_to_abi_dec_info cenv (BaseT (BytesT (Dynamic n))) = DecBytestring n ∧
  type_to_abi_dec_info cenv (BaseT (StringT n)) = DecBytestring n ∧
  type_to_abi_dec_info cenv (ArrayT elem (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info cenv elem)
      (abi_embedded_static_size (cenv_sft cenv) elem) (type_memory_bytes cenv elem)
      (is_abi_dynamic (cenv_sft cenv) elem) n ∧
  type_to_abi_dec_info cenv (ArrayT elem (Fixed n)) =
    DecComplex (is_abi_dynamic (cenv_sft cenv) elem)
      (GENLIST (K (type_to_abi_dec_info cenv elem,
                     abi_embedded_static_size (cenv_sft cenv) elem,
                     type_memory_bytes cenv elem)) n) ∧
  type_to_abi_dec_info cenv (TupleT tys) =
    DecComplex (EXISTS (is_abi_dynamic (cenv_sft cenv)) tys)
      (MAP (λt. (type_to_abi_dec_info cenv t,
                 abi_embedded_static_size (cenv_sft cenv) t,
                 type_memory_bytes cenv t)) tys) ∧
  (* StructT uses per-field recursive decoding, same as TupleT.
     Mirrors Python: StructT.abi_type is ABI_Tuple(field_types). *)
  type_to_abi_dec_info cenv (StructT name) =
    DecComplex (EXISTS (is_abi_dynamic (cenv_sft cenv)) (cenv_sft cenv name))
      (MAP (λ(fn, fty, sz).
              (type_to_abi_dec_info cenv fty,
               abi_embedded_static_size (cenv_sft cenv) fty,
               type_memory_bytes cenv fty))
           (cenv.ce_struct_fields name)) ∧
  type_to_abi_dec_info cenv (FlagT name) =
    (* Flags are unsigned integers with n_members bits.
       Mirrors Python: clamp_basetype → int_clamp(bits=n_members, signed=False) *)
    DecPrimWord (IntClamp (cenv.ce_flag_n_members name) F) ∧
  type_to_abi_dec_info cenv ty = DecPrimWord (type_to_abi_clamp ty)
Termination
  cheat
End

(* Stage internal call arguments based on pass_via_stack classification.
   arg_types: parallel list of argument types (for computing alloca size).
   For stack-passed word args: use value directly.
   For memory-passed: allocate type-sized buffer, copy value, pass pointer.
   Mirrors Python: expr.py _lower_internal_call arg staging loop *)
Definition compile_stage_intcall_args_def:
  compile_stage_intcall_args cenv [] _ _ st = ([] : operand list, st) ∧
  compile_stage_intcall_args cenv (val_op :: vals) (T :: flags) (_ :: tys) st =
    (* Stack-passed: use value directly. *)
    (let (rest, st1) = compile_stage_intcall_args cenv vals flags tys st in
     (val_op :: rest, st1)) ∧
  compile_stage_intcall_args cenv (val_op :: vals) (F :: flags) (ty :: tys) st =
    (* Memory-passed: allocate buffer with proper type size, copy, pass ptr.
       For word types: MSTORE the value.
       For complex types: val_op is a pointer; MCOPY the data. *)
    (let mem_size = type_memory_bytes cenv ty in
          let (buf_alloc, st2) = compile_alloc_buffer (MAX 32 mem_size) st in
          let buf = buf_alloc.buf_operand in
     (* 3-way store_memory dispatch matching Python:
        prim → MSTORE, bytestring → dynamic copy, complex → static MCOPY *)
     let is_bs = (case ty of
         BaseT (BytesT (Dynamic _)) => T
       | BaseT (StringT _) => T
       | _ => F) in
     let (_, st3) =
       if is_word_type ty then emit_void MSTORE [buf; val_op] st2
       else if is_bs then
         compile_store_bytestring val_op buf st2
       else emit_void MCOPY [buf; val_op; Lit (n2w mem_size)] st2 in
     let (rest, st4) = compile_stage_intcall_args cenv vals flags tys st3 in
     (buf :: rest, st4)) ∧
  (* Fallback: extra args without flags/types default to stack *)
  compile_stage_intcall_args cenv (val_op :: vals) _ _ st =
    (let (rest, st1) = compile_stage_intcall_args cenv vals [] [] st in
     (val_op :: rest, st1))
End

(* Full internal call with return buffer allocation and multi-return support.
   returns_count: number of stack returns (0 = memory return)
   return_buf_size: size of memory return buffer (for complex types)
   arg_ops: pre-evaluated argument operands
   label: function label string
   Mirrors Python: expr.py _lower_internal_call *)
(* Store list of operands to consecutive 32-byte slots in a buffer.
   Mirrors Python: for i, outv in enumerate(outs): b.mstore(dst_i, outv) *)
Definition store_multi_results_def:
  store_multi_results buf_op [] (offset:num) st = ((), st) ∧
  store_multi_results buf_op (op::ops) offset st =
    let (dst, st1) =
      (if offset = 0 then (buf_op, st)
       else emit_op ADD [buf_op; Lit (n2w offset)] st) in
    let (_, st2) = emit_void MSTORE [dst; op] st1 in
    store_multi_results buf_op ops (offset + 32) st2
End

(* NOTE: compile_internal_call deleted — superseded by
   compile_call IntCall which handles all internal calls. *)

(* NOTE: compile_bytelike_literal moved below compile_store_byte_chunks
   (near compile_literal) to support multi-chunk storage. *)

(* ===== Array Subscript (full) ===== *)
(* Full array subscript with location-aware access and bounds checking.
   Mirrors Python: expr.py _lower_array_subscript
   is_dynamic: T for DynArray (has length word), F for SArray (known count)
   word_scale: 1 for storage/transient, 32 for memory/code/calldata
   static_count: compile-time count for SArray, 0 for DynArray *)
Definition compile_array_subscript_def:
  compile_array_subscript base_op idx_op is_dynamic static_count
                               word_scale elem_size is_signed_idx
                               (load_opc : opcode) st =
    (* Get length: load from base using location-appropriate opcode *)
    let (len_op, st1) =
      if is_dynamic then emit_op load_opc [base_op] st
      else (Lit (n2w static_count), st) in
    (* Bounds check: assert not (idx < 0) and not (idx >= length).
       For signed index types, check SLT(idx, 0) for negative indices.
       Negative signed indices are huge unsigned values and would pass
       the unsigned LT check. Mirrors Python: expr.py L909-912 *)
    let (is_neg, st1a) =
      if is_signed_idx then emit_op SLT [idx_op; Lit 0w] st1
      else (Lit 0w, st1) in
    let (is_oob, st2) = emit_op LT [idx_op; len_op] st1a in
    let (not_oob, st2a) = emit_op ISZERO [is_oob] st2 in
    let (invalid, st2b) = emit_op OR [is_neg; not_oob] st2a in
    let (valid, st2c) = emit_op ISZERO [invalid] st2b in
    let (_, st3) = emit_void ASSERT [valid] st2c in
    (* Data pointer: skip length word for DynArray *)
    let (data_ptr, st4) =
      if is_dynamic then
        let overhead = word_scale in  (* 1 slot or 32 bytes *)
        emit_op ADD [base_op; Lit (n2w overhead)] st3
      else
        (base_op, st3) in
    (* Element offset: idx * elem_size *)
    let (offset, st5) = emit_op MUL [idx_op; Lit (n2w elem_size)] st4 in
    emit_op ADD [data_ptr; offset] st5
End

(* Helper: extract literal integer index from an expression.
   Used for tuple/struct subscript where the index must be a compile-time constant. *)
Definition literal_int_index_def:
  literal_int_index (Literal _ (IntL n)) = Num (ABS n) ∧
  literal_int_index _ = 0
End

(* ===== Tuple Subscript ===== *)
(* Access tuple[N] with compile-time offset.
   offset: pre-computed byte offset to element N.
   Mirrors Python: expr.py _lower_tuple_subscript *)
Definition compile_tuple_subscript_def:
  compile_tuple_subscript base_op 0 st = (base_op, st) ∧
  compile_tuple_subscript base_op offset st =
    emit_op ADD [base_op; Lit (n2w offset)] st
End

(* NOTE: compile_struct_field deleted — was never called.
   Struct field access goes through compile_attribute → struct_field_offset. *)

(* ===== Literal Compilation ===== *)

(* Store byte data in 32-byte chunks to memory at data_ptr.
   Each chunk is right-padded with zeros (big-endian word from up to 32 bytes).
   offset: byte offset from data_ptr for current chunk.
   Mirrors Python: expr.py _lower_bytelike data storage loop. *)
Definition compile_store_byte_chunks_def:
  compile_store_byte_chunks data_ptr [] offset st = ((), st) ∧
  compile_store_byte_chunks data_ptr bs offset st =
    let chunk = TAKE 32 (bs ++ REPLICATE 31 (0w:word8)) in
    let word_val : bytes32 = word_of_bytes T 0w chunk in
    let (dst, st1) = emit_op ADD [data_ptr; Lit (n2w offset)] st in
    let (_, st2) = emit_void MSTORE [dst; Lit word_val] st1 in
    compile_store_byte_chunks data_ptr (DROP 32 bs) (offset + 32) st2
Termination
  WF_REL_TAC `measure (λ(_, bs, _, _). LENGTH bs)` >>
  rw[listTheory.LENGTH_DROP]
End

(* Allocate buffer and store bytes/string literal.
   Memory layout: ptr+0 = length (32 bytes), ptr+32 = data (right-padded).
   Returns pointer to allocated buffer (address, not value).
   Mirrors Python: expr.py _lower_bytelike. *)
(* Returns (buffer # compile_state) — buffer record carries provenance. *)
Definition compile_bytelike_literal_def:
  compile_bytelike_literal bytez max_len st =
    let bytez_length = LENGTH bytez in
    let alloc_size = 32 + ((max_len + 31) DIV 32) * 32 in
        let (buf_alloc, st2) = compile_alloc_buffer alloc_size st in
        let buf_op = buf_alloc.buf_operand in
    (* Store length at buf_op *)
    let (_, st3) = emit_void MSTORE [buf_op; Lit (n2w bytez_length)] st2 in
    (* Store data in 32-byte chunks at buf_op + 32 *)
    let (data_ptr, st4) = emit_op ADD [buf_op; Lit 32w] st3 in
    let (_, st5) = compile_store_byte_chunks data_ptr bytez 0 st4 in
    (buf_alloc, st5)
End

(* compile_literal_vv: returns vyper_value with type.
   Word literals → StackValue.  Bytestring/string literals → LocatedValue LocMemory. *)
Definition compile_literal_vv_def:
  compile_literal_vv ty (BoolL T) st = (StackValue ty (Lit 1w), st) ∧
  compile_literal_vv ty (BoolL F) st = (StackValue ty (Lit 0w), st) ∧
  compile_literal_vv ty (IntL n) st = (StackValue ty (Lit (i2w n)), st) ∧
  compile_literal_vv ty (DecimalL n) st = (StackValue ty (Lit (i2w n)), st) ∧
  (* BytesL: Fixed → word literal; Dynamic → memory buffer.
     Discriminated by ty parameter (from Literal type literal). *)
  compile_literal_vv ty (BytesL bs) st =
    (case ty of
       BaseT (BytesT (Fixed m)) =>
         (StackValue ty (Lit (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))), st)
     | BaseT (BytesT (Dynamic max_len)) =>
         let (buf, st') = compile_bytelike_literal bs max_len st in
         (LocatedValue ty (base_ptr buf), st')
     | _ => (* AddressT or fallback: treat as word *)
         (StackValue ty (Lit (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))), st)) ∧
  compile_literal_vv ty (StringL s) st =
    (case ty of
       BaseT (StringT max_len) =>
         let (buf, st') = compile_bytelike_literal (MAP (n2w o ORD) s) max_len st in
         (LocatedValue ty (base_ptr buf), st')
     | _ => (* fallback: use string length *)
         let (buf, st') = compile_bytelike_literal (MAP (n2w o ORD) s) (LENGTH s) st in
         (LocatedValue ty (base_ptr buf), st'))
End

(* ===== Name (Variable Reference) ===== *)

(* Return VyperValue for a local variable reference.
   Always returns LocatedValue — the variable's alloca address + location.
   unwrap_value handles loading for word types.
   Mirrors Python: expr.py lower_Name → VyperValue.from_ptr *)
Definition compile_name_vv_def:
  compile_name_vv cenv ty id st =
    case FLOOKUP cenv.ce_vars id of
      SOME (MemLoc offset _) =>
        (LocatedValue ty (mk_ptr (Lit (n2w offset)) LocMemory), st)
    | SOME (PtrVar ptr_op _) =>
        (* Memory-passed param: operand IS the pointer, no MLOAD needed.
           Mirrors Python: register_variable maps name directly to PARAM ptr. *)
        (LocatedValue ty (mk_ptr ptr_op LocMemory), st)
    | _ => let (_, st') = emit_inst INVALID [] [] st in
           (StackValue ty (Lit 0w), st')
End

(* ===== Environment Variable Access ===== *)

(* Compile environment variable opcodes.
   Mirrors Python: expr.py _lower_environment_attr *)
Definition compile_env_var_def:
  compile_env_var Sender st = emit_op CALLER [] st ∧
  compile_env_var SelfAddr st = emit_op ADDRESS [] st ∧
  compile_env_var ValueSent st = emit_op CALLVALUE [] st ∧
  compile_env_var TimeStamp st = emit_op TIMESTAMP [] st ∧
  compile_env_var BlockNumber st = emit_op NUMBER [] st ∧
  compile_env_var BlobBaseFee st = emit_op BLOBBASEFEE [] st ∧
  compile_env_var GasPrice st = emit_op GASPRICE [] st ∧
  compile_env_var PrevHash st =
    (let (num, st1) = emit_op NUMBER [] st in
     let (prev_num, st2) = emit_op SUB [num; Lit 1w] st1 in
     emit_op BLOCKHASH [prev_num] st2) ∧
  compile_env_var ChainId st = emit_op CHAINID [] st ∧
  compile_env_var Coinbase st = emit_op COINBASE [] st ∧
  compile_env_var GasLimit st = emit_op GASLIMIT [] st ∧
  compile_env_var BaseFee st = emit_op BASEFEE [] st ∧
  compile_env_var PrevRandao st = emit_op PREVRANDAO [] st ∧
  compile_env_var TxOrigin st = emit_op ORIGIN [] st ∧
  compile_env_var MsgGas st = emit_op GAS [] st
End

(* ===== Denomination Multiplier ===== *)
(* Convert denomination to wei multiplier.
   Mirrors Python: builtins/misc.py as_wei_value *)
Definition denomination_multiplier_def:
  denomination_multiplier Wei = 1 ∧
  denomination_multiplier Kwei = 10 ** 3 ∧
  denomination_multiplier Mwei = 10 ** 6 ∧
  denomination_multiplier Gwei = 10 ** 9 ∧
  denomination_multiplier Szabo = 10 ** 12 ∧
  denomination_multiplier Finney = 10 ** 15 ∧
  denomination_multiplier Ether = 10 ** 18 ∧
  denomination_multiplier KEther = 10 ** 21 ∧
  denomination_multiplier MEther = 10 ** 24 ∧
  denomination_multiplier GEther = 10 ** 27 ∧
  denomination_multiplier TEther = 10 ** 30
End

(* NOTE: nsid_to_string moved to compileEnv *)

(* ===== Target Base Address ===== *)
(* Get the base operand for an assignment target.
   Returns the memory/storage address. *)
Definition compile_target_base_def:
  compile_target_base cenv (NameTarget id) =
    (case FLOOKUP cenv.ce_vars id of
       SOME (MemLoc offset _) => Lit (n2w offset)
     | _ => Lit 0w) ∧
  compile_target_base cenv (BareGlobalNameTarget id) =
    (case FLOOKUP cenv.ce_vars id of
       SOME (ImmutableLoc offset) => Lit (n2w offset)
     | _ => Lit 0w) ∧
  compile_target_base cenv (TopLevelNameTarget nsid) =
    (let name = nsid_to_string nsid in
     case FLOOKUP cenv.ce_vars name of
       SOME (StorageLoc slot) => Lit slot
     | SOME (TransientLoc slot) => Lit slot
     | _ => Lit 0w) ∧
  compile_target_base cenv (SubscriptTarget bt _) =
    compile_target_base cenv bt ∧
  compile_target_base cenv (AttributeTarget bt _) =
    compile_target_base cenv bt
End

(* ===== Type Conversion ===== *)
(* Conversion operation descriptor. Encodes what the conversion does.
   Mirrors Python: builtins/convert.py lower_convert dispatch.
   The caller constructs the appropriate convert_op from src/dst types.
   compile_type_convert executes the operation.

   ConvToBool: iszero(iszero(x))
   ConvIntToInt in_signed in_bits out_signed out_bits: integer→integer
   ConvBytesToInt m out_signed out_bits: bytesM→integer (right-shift + clamp)
   ConvIntToBytesM in_signed in_bits m: integer→bytesM (clamp + left-shift)
   ConvIntToDecimal in_signed in_bits divisor out_lo out_hi: int→decimal (clamp + mul)
   ConvDecimalToInt divisor in_lo in_hi out_lo out_hi in_signed: decimal→int (clamp + sdiv)
   ConvBoolToDecimal divisor: bool→decimal (mul by divisor)
   ConvToAddress: integer→address (clamp to uint160)
   ConvBytesToAddress m: bytesM→address (right-shift + clamp)
   ConvToFlag n_members: int→flag (mask check)
   ConvIdentity: no-op (same type or compatible) *)
Datatype:
  convert_op =
    ConvToBool
  | ConvIntToInt bool num bool num
  | ConvBytesToInt num bool num
  | ConvIntToBytesM bool num num
  | ConvIntToDecimal bool num num int int
  | ConvDecimalToInt num int int int int bool
  | ConvBoolToDecimal num
  | ConvToAddress
  | ConvBytesToAddress num
  | ConvToFlag num
  | ConvBytesMToDecimal num num int int  (* m, divisor, out_lo, out_hi *)
  | ConvBytesMToBytesM num num           (* in_m, out_m: downcast check *)
  (* Bytestring conversions: src is a memory pointer to [length][data].
     Load data, shift to align, then clamp/convert. *)
  | ConvBytestringToBool
  | ConvBytestringToInt bool num     (* is_signed_out, out_bits *)
  | ConvBytestringToAddress
  | ConvBytestringToDecimal num int int  (* divisor, out_lo, out_hi *)
  | ConvBytestringToBytesM num       (* out_m *)
  | ConvBytestringCast num           (* max_len: downcast length check *)
  | ConvFixedToBytestring num       (* m: bytesM → Bytes[N] allocation *)
  | ConvIdentity
End

(* Load bytestring data as right-aligned word.
   Shared preamble for ConvBytestring* conversions.
   Returns (shifted, num_zero_bits, st) where shifted = data >> (32-length)*8.
   shift_opc selects SAR (signed) or SHR (unsigned). *)
Definition load_bytestring_as_word_def:
  load_bytestring_as_word v shift_opc st =
    let (length, st1) = emit_op MLOAD [v] st in
    let (data_ptr, st2) = emit_op ADD [v; Lit 32w] st1 in
    let (data, st3) = emit_op MLOAD [data_ptr] st2 in
    let (sub32, st4) = emit_op SUB [Lit 32w; length] st3 in
    let (num_zero_bits, st5) = emit_op MUL [sub32; Lit 8w] st4 in
    let (shifted, st6) = emit_op shift_opc [num_zero_bits; data] st5 in
    (shifted, num_zero_bits, st6)
End

(* Execute a type conversion operation.
   Mirrors Python: builtins/convert.py lower_convert dispatch. *)
Definition compile_type_convert_def:
  (* Bool: iszero(iszero(x)) *)
  compile_type_convert v ConvToBool st =
    (let (z, st1) = emit_op ISZERO [v] st in
     emit_op ISZERO [z] st1) ∧
  (* Integer→integer conversion with bounds checking.
     Mirrors Python: convert.py _int_to_int *)
  compile_type_convert v (ConvIntToInt in_s in_b out_s out_b) st =
    (if in_s ∧ ¬out_s then
       (* signed→unsigned *)
       if out_b < in_b then
         let hi = n2w (2 ** out_b - 1) : bytes32 in
         let (le_hi, st1) = emit_op GT [v; Lit hi] st in
         let (ok_hi, st2) = emit_op ISZERO [le_hi] st1 in
         let (ge_zero, st3) = emit_op SLT [v; Lit 0w] st2 in
         let (ok_lo, st4) = emit_op ISZERO [ge_zero] st3 in
         let (ok, st5) = emit_op AND [ok_hi; ok_lo] st4 in
         let (_, st6) = emit_void ASSERT [ok] st5 in (v, st6)
       else
         let (neg, st1) = emit_op SLT [v; Lit 0w] st in
         let (ok, st2) = emit_op ISZERO [neg] st1 in
         let (_, st3) = emit_void ASSERT [ok] st2 in (v, st3)
     else if ¬in_s ∧ out_s then
       let hi = n2w (2 ** (out_b - 1) - 1) : bytes32 in
       let (too_big, st1) = emit_op GT [v; Lit hi] st in
       let (ok, st2) = emit_op ISZERO [too_big] st1 in
       let (_, st3) = emit_void ASSERT [ok] st2 in (v, st3)
     else if out_b < in_b then
       if out_s then
         let lo = i2w (- &(2 ** (out_b - 1))) : bytes32 in
         let hi = i2w (&(2 ** (out_b - 1) - 1)) : bytes32 in
         let (too_small, st1) = emit_op SLT [v; Lit lo] st in
         let (ok1, st2) = emit_op ISZERO [too_small] st1 in
         let (too_big, st3) = emit_op SGT [v; Lit hi] st2 in
         let (ok2, st4) = emit_op ISZERO [too_big] st3 in
         let (ok, st5) = emit_op AND [ok1; ok2] st4 in
         let (_, st6) = emit_void ASSERT [ok] st5 in (v, st6)
       else
         let hi = n2w (2 ** out_b - 1) : bytes32 in
         let (too_big, st1) = emit_op GT [v; Lit hi] st in
         let (ok, st2) = emit_op ISZERO [too_big] st1 in
         let (_, st3) = emit_void ASSERT [ok] st2 in (v, st3)
     else (v, st)) ∧
  (* BytesM→integer: right-shift + optional clamp *)
  compile_type_convert v (ConvBytesToInt m out_s out_b) st =
    (let shift = (32 - m) * 8 in
     let (shifted, st1) =
       if out_s then emit_op SAR [Lit (n2w shift); v] st
       else emit_op SHR [Lit (n2w shift); v] st in
     if m * 8 > out_b then
       if out_s then
         let lo = i2w (- &(2 ** (out_b - 1))) : bytes32 in
         let hi = i2w (&(2 ** (out_b - 1) - 1)) : bytes32 in
         let (ts, st2) = emit_op SLT [shifted; Lit lo] st1 in
         let (ok1, st3) = emit_op ISZERO [ts] st2 in
         let (tb, st4) = emit_op SGT [shifted; Lit hi] st3 in
         let (ok2, st5) = emit_op ISZERO [tb] st4 in
         let (ok, st6) = emit_op AND [ok1; ok2] st5 in
         let (_, st7) = emit_void ASSERT [ok] st6 in (shifted, st7)
       else
         let hi = n2w (2 ** out_b - 1) : bytes32 in
         let (tb, st2) = emit_op GT [shifted; Lit hi] st1 in
         let (ok, st3) = emit_op ISZERO [tb] st2 in
         let (_, st4) = emit_void ASSERT [ok] st3 in (shifted, st4)
     else (shifted, st1)) ∧
  (* Integer→bytesM: clamp + left-shift *)
  compile_type_convert v (ConvIntToBytesM in_s in_b m) st =
    (let (clamped, st1) =
       if in_b > m * 8 then
         if in_s then
           let (ext, st_a) = emit_op SIGNEXTEND [Lit (n2w (m - 1)); v] st in
           let (ok, st_b) = emit_op EQ [v; ext] st_a in
           let (_, st_c) = emit_void ASSERT [ok] st_b in (v, st_c)
         else
           let hi = n2w (2 ** (m * 8) - 1) : bytes32 in
           let (tb, st_a) = emit_op GT [v; Lit hi] st in
           let (ok, st_b) = emit_op ISZERO [tb] st_a in
           let (_, st_c) = emit_void ASSERT [ok] st_b in (v, st_c)
       else (v, st) in
     let shift = (32 - m) * 8 in
     emit_op SHL [Lit (n2w shift); clamped] st1) ∧
  (* Integer→decimal: clamp to pre-scaled bounds then multiply by divisor *)
  compile_type_convert v (ConvIntToDecimal in_s in_b divisor out_lo out_hi) st =
    (let pre_lo = out_lo / &divisor in
     let pre_hi = out_hi / &divisor in
     let in_lo = if in_s then - &(2 ** (in_b - 1)) else 0 in
     let in_hi = if in_s then &(2 ** (in_b - 1) - 1) else &(2 ** in_b - 1) in
     let st1 =
       if in_lo < pre_lo then
         let (ts, st_a) = emit_op SLT [v; Lit (i2w pre_lo)] st in
         let (ok, st_b) = emit_op ISZERO [ts] st_a in
         SND (emit_void ASSERT [ok] st_b)
       else st in
     let (_, st2) =
       if in_hi > pre_hi then
         let (tb, st_a) =
           (if in_s then emit_op SGT [v; Lit (i2w pre_hi)] st1
            else emit_op GT [v; Lit (i2w pre_hi)] st1) in
         let (ok, st_b) = emit_op ISZERO [tb] st_a in
         emit_void ASSERT [ok] st_b
       else ((), st1) in
     emit_op MUL [v; Lit (n2w divisor)] st2) ∧
  (* Decimal→integer: clamp scaled bounds then sdiv *)
  compile_type_convert v (ConvDecimalToInt divisor in_lo in_hi out_lo out_hi in_s) st =
    (let scaled_lo = out_lo * &divisor in
     let scaled_hi = out_hi * &divisor in
     let st1 =
       if in_lo < scaled_lo then
         let (ts, st_a) = emit_op SLT [v; Lit (i2w scaled_lo)] st in
         let (ok, st_b) = emit_op ISZERO [ts] st_a in
         SND (emit_void ASSERT [ok] st_b)
       else st in
     let (_, st2) =
       if in_hi > scaled_hi then
         let (tb, st_a) =
           (if in_s then emit_op SGT [v; Lit (i2w scaled_hi)] st1
            else emit_op GT [v; Lit (i2w scaled_hi)] st1) in
         let (ok, st_b) = emit_op ISZERO [tb] st_a in
         emit_void ASSERT [ok] st_b
       else ((), st1) in
     emit_op SDIV [v; Lit (n2w divisor)] st2) ∧
  (* Bool→decimal: multiply by divisor *)
  compile_type_convert v (ConvBoolToDecimal divisor) st =
    emit_op MUL [v; Lit (n2w divisor)] st ∧
  (* Integer→address: clamp to uint160 *)
  compile_type_convert v ConvToAddress st =
    (let hi = n2w (2 ** 160 - 1) : bytes32 in
     let (tb, st1) = emit_op GT [v; Lit hi] st in
     let (ok, st2) = emit_op ISZERO [tb] st1 in
     let (_, st3) = emit_void ASSERT [ok] st2 in (v, st3)) ∧
  (* BytesM→address: right-shift + clamp *)
  compile_type_convert v (ConvBytesToAddress m) st =
    (let shift = (32 - m) * 8 in
     let (shifted, st1) = emit_op SHR [Lit (n2w shift); v] st in
     if m * 8 > 160 then
       let hi = n2w (2 ** 160 - 1) : bytes32 in
       let (tb, st2) = emit_op GT [shifted; Lit hi] st1 in
       let (ok, st3) = emit_op ISZERO [tb] st2 in
       let (_, st4) = emit_void ASSERT [ok] st3 in (shifted, st4)
     else (shifted, st1)) ∧
  (* Integer→flag: assert only valid bits set *)
  compile_type_convert v (ConvToFlag n_members) st =
    (let mask = n2w (2 ** n_members - 1) : bytes32 in
     let (inv, st1) = emit_op NOT [Lit mask] st in
     let (extra, st2) = emit_op AND [v; inv] st1 in
     let (ok, st3) = emit_op ISZERO [extra] st2 in
     let (_, st4) = emit_void ASSERT [ok] st3 in (v, st4)) ∧
  (* BytesM→Decimal: right-shift by (32-m)*8 bits, then optional clamp.
     BytesM raw bits after right-alignment ARE the fixed-point representation.
     No multiplication needed — Python: convert.py _to_decimal for BytesM_T source
     just does SAR + optional clamp. *)
  compile_type_convert v (ConvBytesMToDecimal m divisor out_lo out_hi) st =
    (let shift = (32 - m) * 8 in
     let (shifted, st1) = emit_op SAR [Lit (n2w shift); v] st in
     (* Clamp if m*8 > 168 (decimal bits) *)
     if m * 8 > 168 then
       let (too_small, st2) = emit_op SLT [shifted; Lit (i2w out_lo)] st1 in
       let (ok1, st3) = emit_op ISZERO [too_small] st2 in
       let (too_big, st4) = emit_op SGT [shifted; Lit (i2w out_hi)] st3 in
       let (ok2, st5) = emit_op ISZERO [too_big] st4 in
       let (ok, st6) = emit_op AND [ok1; ok2] st5 in
       let (_, st7) = emit_void ASSERT [ok] st6 in (shifted, st7)
     else (shifted, st1)) ∧
  (* BytesM→BytesM: downcast check (assert truncated bits are zero).
     For out_m >= in_m: no-op (widening). For out_m < in_m: check.
     Mirrors Python: convert.py _to_bytes_m for BytesM_T source *)
  compile_type_convert v (ConvBytesMToBytesM in_m out_m) st =
    (if out_m < in_m then
       (* Downcast: SHL by out_m*8 bits, assert result is zero *)
       let check_shift = out_m * 8 in
       let (truncated, st1) = emit_op SHL [Lit (n2w check_shift); v] st in
       let (ok, st2) = emit_op ISZERO [truncated] st1 in
       let (_, st3) = emit_void ASSERT [ok] st2 in (v, st3)
     else (v, st)) ∧
  (* Bytestring→Bool: load data, shift, iszero(iszero).
     Mirrors Python: convert.py _to_bool bytestring path *)
  compile_type_convert v ConvBytestringToBool st =
    (let (shifted, num_zero_bits, st6) = load_bytestring_as_word v SHR st in
     let (z, st7) = emit_op ISZERO [shifted] st6 in
     emit_op ISZERO [z] st7) ∧
  (* Bytestring→Int/Uint: load data, shift (SAR for signed, SHR for unsigned), clamp.
     Mirrors Python: convert.py _to_int bytestring path *)
  compile_type_convert v (ConvBytestringToInt is_signed out_b) st =
    (let shift_opc = if is_signed then SAR else SHR in
     let (shifted, num_zero_bits, st6) = load_bytestring_as_word v shift_opc st in
     (* Clamp to output type bounds *)
     if out_b >= 256 then (shifted, st6)
     else if is_signed then
       let (ext, st7) = emit_op SIGNEXTEND [Lit (n2w (out_b DIV 8 - 1)); shifted] st6 in
       let (ok, st8) = emit_op EQ [ext; shifted] st7 in
       let (_, st9) = emit_void ASSERT [ok] st8 in (shifted, st9)
     else
       let (hi_bits, st7) = emit_op SHR [Lit (n2w out_b); shifted] st6 in
       let (ok, st8) = emit_op ISZERO [hi_bits] st7 in
       let (_, st9) = emit_void ASSERT [ok] st8 in (shifted, st9)) ∧
  (* Bytestring→Address: load data, shift (unsigned), clamp uint160.
     Mirrors Python: convert.py _to_address bytestring path *)
  compile_type_convert v ConvBytestringToAddress st =
    (let (shifted, num_zero_bits, st6) = load_bytestring_as_word v SHR st in
     (* Clamp to uint160 *)
     let (hi_bits, st7) = emit_op SHR [Lit 160w; shifted] st6 in
     let (ok, st8) = emit_op ISZERO [hi_bits] st7 in
     let (_, st9) = emit_void ASSERT [ok] st8 in (shifted, st9)) ∧
  (* Bytestring→Decimal: load data, SAR (signed), clamp 168-bit signed.
     Mirrors Python: convert.py _to_decimal bytestring path *)
  compile_type_convert v (ConvBytestringToDecimal divisor out_lo out_hi) st =
    (let (shifted, num_zero_bits, st6) = load_bytestring_as_word v SAR st in
     (* Clamp to decimal bounds *)
     let (too_small, st7) = emit_op SLT [shifted; Lit (i2w out_lo)] st6 in
     let (ok1, st8) = emit_op ISZERO [too_small] st7 in
     let (too_big, st9) = emit_op SGT [shifted; Lit (i2w out_hi)] st8 in
     let (ok2, st10) = emit_op ISZERO [too_big] st9 in
     let (ok, st11) = emit_op AND [ok1; ok2] st10 in
     let (_, st12) = emit_void ASSERT [ok] st11 in (shifted, st12)) ∧
  (* Bytestring→BytesM: load data, SHR to clean extra bits, SHL to restore.
     Mirrors Python: convert.py _to_bytes_m bytestring path *)
  compile_type_convert v (ConvBytestringToBytesM out_m) st =
    ((* SHR to get raw value right-aligned, then SHL to left-align for bytesM *)
     let (shifted_r, num_zero_bits, st6) = load_bytestring_as_word v SHR st in
     let (shifted_l, st7) = emit_op SHL [num_zero_bits; shifted_r] st6 in
     (* Verify no truncation: only low (32-out_m)*8 bits can be nonzero *)
     let check_bits = (32 - out_m) * 8 in
     let (truncated, st8) = emit_op SHL [Lit (n2w (out_m * 8)); shifted_l] st7 in
     let (ok, st9) = emit_op ISZERO [truncated] st8 in
     let (_, st10) = emit_void ASSERT [ok] st9 in (shifted_l, st10)) ∧
  (* Bytestring downcast: check length <= max_len.
     Mirrors Python: convert.py _check_bytes *)
  compile_type_convert v (ConvBytestringCast max_len) st =
    (let (length, st1) = emit_op MLOAD [v] st in
     let (too_long, st2) = emit_op GT [length; Lit (n2w max_len)] st1 in
     let (ok, st3) = emit_op ISZERO [too_long] st2 in
     let (_, st4) = emit_void ASSERT [ok] st3 in (v, st4)) ∧
  (* Fixed bytes to bytestring: allocate length-prefixed buffer.
     bytesM (word value) → Bytes[N] (memory pointer to [length][data]).
     Mirrors Python: convert.py _to_Bytes for BytesM source *)
  compile_type_convert v (ConvFixedToBytestring m) st =
    (let (buf_alloc, st2) = compile_alloc_buffer 64 st in
     let buf = buf_alloc.buf_operand in
     let (_, st3) = emit_void MSTORE [buf; Lit (n2w m)] st2 in
     let (data_ptr, st4) = emit_op ADD [buf; Lit 32w] st3 in
     let (_, st5) = emit_void MSTORE [data_ptr; v] st4 in
     (buf, st5)) ∧
  (* Identity: no-op *)
  compile_type_convert v ConvIdentity st = (v, st)
End

(* ===== Unary Negation ===== *)

(* Negate value with overflow check (operand > MIN_INT).
   Mirrors Python: expr.py lower_UnaryOp USub case *)
Definition compile_neg_def:
  compile_neg v ty st =
    let (lo, _) = type_bounds ty in
    let (ok, st1) = emit_op SGT [v; Lit lo] st in
    let (_, st2) = emit_void ASSERT [ok] st1 in
    emit_op SUB [Lit 0w; v] st2
End

(* ===== Convert Operation Constructor ===== *)

(* Check if a type is a dynamic bytestring (Bytes[N] or String[N]).
   Mirrors Python: isinstance(t, _BytestringT) *)
(* is_bytestring_type moved to compileEnvScript.sml *)

(* Extract byte count from a fixed bytes type. bytes1=1, ..., bytes32=32. *)
Definition fixed_bytes_size_def:
  fixed_bytes_size (BaseT (BytesT (Fixed m))) = m ∧
  fixed_bytes_size _ = 32  (* fallback: shouldn't be used for non-bytesM *)
End

Definition mk_convert_op_def:
  mk_convert_op src_ty dst_ty =
    let ddiv = 10000000000:num in
    let is_bs = is_bytestring_type src_ty in
    case dst_ty of
      BaseT BoolT =>
        if is_bs then ConvBytestringToBool else ConvToBool
    | BaseT AddressT =>
        (if is_bs then ConvBytestringToAddress
         else case src_ty of
           BaseT (BytesT (Fixed m)) => ConvBytesToAddress m
         | _ => ConvToAddress)
    | BaseT (IntT out_b) =>
        (if is_bs then ConvBytestringToInt T out_b
         else case src_ty of
           BaseT (IntT in_b) => ConvIntToInt T in_b T out_b
         | BaseT (UintT in_b) => ConvIntToInt F in_b T out_b
         | BaseT BoolT => ConvIntToInt F 8 T out_b
         | BaseT AddressT => ConvIntToInt F 160 T out_b
         | BaseT DecimalT =>
             let (in_lo, in_hi) = type_bounds (BaseT DecimalT) in
             let (out_lo, out_hi) = type_bounds (BaseT (IntT out_b)) in
             ConvDecimalToInt ddiv (w2i in_lo) (w2i in_hi)
                             (w2i out_lo) (w2i out_hi) T
         | BaseT (BytesT (Fixed m)) => ConvBytesToInt m T out_b
         | FlagT _ => ConvIntToInt F 256 T out_b
         | _ => ConvIdentity)
    | BaseT (UintT out_b) =>
        (if is_bs then ConvBytestringToInt F out_b
         else case src_ty of
           BaseT (IntT in_b) => ConvIntToInt T in_b F out_b
         | BaseT (UintT in_b) => ConvIntToInt F in_b F out_b
         | BaseT BoolT => ConvIntToInt F 8 F out_b
         | BaseT AddressT => ConvIntToInt F 160 F out_b
         | BaseT DecimalT =>
             let (in_lo, in_hi) = type_bounds (BaseT DecimalT) in
             (* For uint256: w2i(n2w(2^256-1)) overflows to -1, making
                scaled_hi negative and the upper clamp incorrect.
                Fix: use in_hi as out_hi to skip the upper clamp entirely —
                any valid 168-bit decimal ÷ 10^10 fits in uint256.
                For smaller uint types: w2i is fine (fits in signed range). *)
             let (out_lo, out_hi) =
               if out_b >= 256 then (0, w2i in_hi)  (* skip upper clamp *)
               else let (l,h) = type_bounds (BaseT (UintT out_b)) in
                    (w2i l, w2i h) in
             ConvDecimalToInt ddiv (w2i in_lo) (w2i in_hi)
                             out_lo out_hi T
         | BaseT (BytesT (Fixed m)) => ConvBytesToInt m F out_b
         | FlagT _ => ConvIntToInt F 256 F out_b
         | _ => ConvIdentity)
    | BaseT DecimalT =>
        (let (out_lo, out_hi) = type_bounds (BaseT DecimalT) in
         if is_bs then ConvBytestringToDecimal ddiv (w2i out_lo) (w2i out_hi)
         else case src_ty of
           BaseT (IntT in_b) =>
             ConvIntToDecimal T in_b ddiv (w2i out_lo) (w2i out_hi)
         | BaseT (UintT in_b) =>
             ConvIntToDecimal F in_b ddiv (w2i out_lo) (w2i out_hi)
         | BaseT BoolT => ConvBoolToDecimal ddiv
         | BaseT (BytesT (Fixed m)) =>
             ConvBytesMToDecimal m ddiv (w2i out_lo) (w2i out_hi)
         | _ => ConvIdentity)
    | BaseT (BytesT (Fixed m)) =>
        (if is_bs then ConvBytestringToBytesM m
         else case src_ty of
           BaseT (IntT in_b) => ConvIntToBytesM T in_b m
         | BaseT (UintT in_b) => ConvIntToBytesM F in_b m
         | BaseT BoolT => ConvIntToBytesM F 8 m
         | BaseT AddressT => ConvIntToBytesM F 160 m
         (* DecimalT→BytesM: decimal is signed 168-bit internally *)
         | BaseT DecimalT => ConvIntToBytesM T 168 m
         (* BytesM→BytesM: downcast check *)
         | BaseT (BytesT (Fixed in_m)) => ConvBytesMToBytesM in_m m
         | _ => ConvIdentity)
    (* Bytestring/BytesM → Bytes[N]/String[N]:
       - Bytestring source (is_bs=T): downcast length check only.
       - BytesM source (is_bs=F): allocate length-prefixed buffer.
       Mirrors Python: convert.py _to_Bytes, _to_String *)
    | BaseT (BytesT (Dynamic out_n)) =>
        (if is_bs then ConvBytestringCast out_n
         else ConvFixedToBytestring (fixed_bytes_size src_ty))
    | BaseT (StringT out_n) =>
        (if is_bs then ConvBytestringCast out_n
         else ConvFixedToBytestring (fixed_bytes_size src_ty))
    | _ => ConvIdentity
End

(* ===== Main Expression Compilation ===== *)

(* Load a value from a VyperValue, dispatching by type carried in the value.
   Mirrors Python: context.py unwrap()
   - StackValue: return operand directly (already a value)
   - LocatedValue + word type: compile_ptr_load (MLOAD/SLOAD/etc)
   - LocatedValue + complex type + LocMemory: return pointer (address)
   - LocatedValue + complex type + other loc: copy to memory
   Factoring: this is proved correct ONCE; every consumer applies the theorem.
   Type is embedded in VyperValue — no separate ty parameter needed. *)
Definition unwrap_value_def:
  unwrap_value cenv (StackValue ty op) st = (op, st) ∧
  unwrap_value cenv (LocatedValue ty p) st =
    if is_word_type ty then
      compile_ptr_load cenv.ce_is_ctor p.ptr_location p.ptr_operand st
    else
      (case p.ptr_location of
         LocMemory => (p.ptr_operand, st)
       | _ =>
           let mem_bytes = type_memory_bytes cenv ty in
           let word_count = (mem_bytes + 31) DIV 32 in
           compile_ensure_in_memory p.ptr_operand p.ptr_location
             mem_bytes word_count cenv.ce_is_ctor st)
End

(* Compile an expression and unwrap to get a usable operand.
   Mirrors Python: expr.py lower_value() = unwrap(lower())
   cfn is the compile_expr function (for open recursion).
   Type is embedded in VyperValue by compile_expr — unwrap uses it directly. *)
Definition lower_value_def:
  lower_value cfn cenv ty e st =
    let (vv, st1) = cfn cenv ty e st in
    unwrap_value cenv vv st1
End

(* Like lower_value but also returns the source data_location option.
   SOME loc for LocatedValues (ptr_location), NONE for StackValues.
   Mirrors Python: _copy_complex_type reads src_vv.location before unwrap. *)
Definition lower_value_with_loc_def:
  lower_value_with_loc cfn cenv ty e st =
    let (vv, st1) = cfn cenv ty e st in
    let src_loc = vv_location vv in
    let (op, st2) = unwrap_value cenv vv st1 in
    ((op, src_loc), st2)
End

(* Wrap (operand # compile_state) → (vyper_value # compile_state) as StackValue. *)
Definition as_stack_val_def:
  as_stack_val ty (op, st) = (StackValue ty op, st)
End

Definition as_ptr_val_def:
  as_ptr_val ty loc (op, st) = (LocatedValue ty (mk_ptr op loc), st)
End

(* Compile a Vyper expression to Venom IR instructions.
   Returns the operand holding the result value.

   Parameters:
     cenv : compile_env — maps Vyper var names to Venom locations
     ty   : type        — Vyper type of the expression (for signed/unsigned dispatch)
     e    : expr        — the expression to compile
     st   : compile_state — current compilation state

   Helper functions (compile_concat, compile_make_array, etc.) are defined
   separately with a cfn parameter to break mutual recursion. compile_expr
   passes itself as cfn. *)

(* ===== Expression compilation helpers (parameterized on cfn) ===== *)

(* Concat args into output buffer at data_ptr + offset_op.
   Each arg_info = (is_bytestring, fixed_m).
   Bytestring args: ensure in memory, copy dynamic length data.
   BytesM args: MSTORE value (left-aligned, full 32 bytes), advance by m.
   Mirrors Python: bytes.py lower_concat per-arg loop. *)
Definition compile_concat_def:
  compile_concat cfn cenv [] data_ptr arg_infos offset_op st =
    (offset_op, st) ∧
  compile_concat cfn cenv (e::es) data_ptr ((is_bs, fixed_m)::infos) offset_op st =
    (if is_bs then
       (* lower_value handles ensure_in_memory for bytestrings *)
       let (mem_ptr, st1) = lower_value cfn cenv (expr_type e) e st in
       let (arg_len, st2) = emit_op MLOAD [mem_ptr] st1 in
       let (arg_data, st3) = emit_op ADD [mem_ptr; Lit 32w] st2 in
       let (dst, st4) = emit_op ADD [data_ptr; offset_op] st3 in
       let (_, st5) = emit_void MCOPY [dst; arg_data; arg_len] st4 in
       let (new_offset, st6) = emit_op ADD [offset_op; arg_len] st5 in
       compile_concat cfn cenv es data_ptr infos new_offset st6
     else
       let (v, st1) = lower_value cfn cenv (expr_type e) e st in
       let (dst, st2) = emit_op ADD [data_ptr; offset_op] st1 in
       let (_, st3) = emit_void MSTORE [dst; v] st2 in
       let (new_offset, st4) = emit_op ADD [offset_op; Lit (n2w fixed_m)] st3 in
       compile_concat cfn cenv es data_ptr infos new_offset st4) ∧
  compile_concat cfn cenv _ data_ptr _ offset_op st = (offset_op, st)
Termination
  WF_REL_TAC `measure (λ(cfn,cenv,es,dp,infos,off,st). LENGTH es)` >> simp[]
End

Definition compile_make_array_def:
  compile_make_array cfn cenv [] elem_size has_length_word alloca_size
                     buf_op cur_idx st =
    (if has_length_word then
       let (_, st1) = emit_void MSTORE [buf_op; Lit (n2w cur_idx)] st in
       (buf_op, st1)
     else
       (buf_op, st)) ∧
  compile_make_array cfn cenv (e::es) elem_size has_length_word alloca_size
                     buf_op cur_idx st =
    (let e_ty = expr_type e in
     let is_prim = is_word_type e_ty in
     (* lower_value handles: prims loaded, complex non-memory → memory *)
     let (v, st1) = lower_value cfn cenv e_ty e st in
     let data_offset = if has_length_word then 32 + cur_idx * elem_size
                       else cur_idx * elem_size in
     let (dst, st2) = (if data_offset = 0 then (buf_op, st1)
                       else emit_op ADD [buf_op; Lit (n2w data_offset)] st1) in
     let (_, st3) = (if is_prim then
                       emit_void MSTORE [dst; v] st2
                     else
                       emit_void MCOPY [dst; v; Lit (n2w elem_size)] st2) in
     compile_make_array cfn cenv es elem_size has_length_word alloca_size
                        buf_op (cur_idx + 1) st3)
Termination
  WF_REL_TAC `measure (LENGTH o (FST o SND o SND))`
End

(* Compile list of expressions, unwrapping each to get usable operands.
   lower_value handles: prims from any location → loaded value,
   complex from non-memory → copied to memory pointer.
   Mirrors Python: [Expr(e).lower_value() for e in exprs] *)
Definition compile_multi_exprs_def:
  compile_multi_exprs cfn cenv [] st = ([] : operand list, st) ∧
  compile_multi_exprs cfn cenv (e::es) st =
    (let e_ty = expr_type e in
     let (v, st1) = lower_value cfn cenv e_ty e st in
     let (vs, st2) = compile_multi_exprs cfn cenv es st1 in
     (v :: vs, st2))
Termination
  WF_REL_TAC `measure (LENGTH o (FST o SND o SND))`
End

(* Compile subscript access: array[index], mapping[key], tuple[N].
   Dispatches on base type. HashMap (mapping) dispatched via ce_is_hashmap.
   Mirrors Python: expr.py _lower_subscript *)
Definition compile_subscript_def:
  compile_subscript cfn cenv ret_ty ty base_e idx_e st =
    (let var_name = (case base_e of
                       Name _ id => id
                     | Attribute _ (Name _ "self") fld => fld
                     | _ => "") in
     (* HashMap dispatch: check ce_is_hashmap first.
        Mirrors Python: isinstance(base_typ, HashMapT) *)
     if cenv.ce_is_hashmap var_name then
       let base_slot = (case FLOOKUP cenv.ce_vars var_name of
                          SOME (StorageLoc slot) => Lit slot
                        | _ => Lit 0w) in
       (* Index needs VALUE (for keccak256 hash key).
          Bytestring keys are pre-hashed via SHA3 before sha3_64(slot, key).
          Mirrors Python: _lower_mapping_subscript isinstance(key_typ, _BytestringT) *)
       let idx_ty = expr_type idx_e in
       let (key_op, st1) = lower_value cfn cenv idx_ty idx_e st in
       let (hashed_key, st2) =
         if is_bytestring_type idx_ty then compile_keccak256_key key_op F st1
         else (key_op, st1) in
       let (slot, st3) = compile_mapping_subscript base_slot hashed_key st2 in
       (LocatedValue ret_ty (mk_ptr slot LocStorage), st3)
     else
     let base_type = cenv.ce_var_type var_name in
     case base_type of
       SOME (TupleT tys) =>
         let (base_vv, st1) = cfn cenv ty base_e st in
         let base_op = vv_operand base_vv in
         let base_loc = (case vv_location base_vv of
                           SOME l => l | NONE => LocMemory) in
         let idx = literal_int_index idx_e in
         (* Location-aware sizing: storage uses slot counts, memory uses bytes.
            Mirrors Python: t.get_size_in(data_loc) in _lower_tuple_subscript *)
         let elem_sizes = MAP (elem_size_in_location cenv base_loc) tys in
         let offset = SUM (TAKE idx elem_sizes) in
         let (ptr, st2) = compile_tuple_subscript base_op offset st1 in
         (LocatedValue ret_ty (mk_ptr ptr base_loc), st2)
     | SOME (StructT sname) =>
         let (base_vv, st1) = cfn cenv ty base_e st in
         let base_op = vv_operand base_vv in
         let base_loc = (case vv_location base_vv of
                           SOME l => l | NONE => LocMemory) in
         let idx = literal_int_index idx_e in
         let fld_info = cenv.ce_struct_fields sname in
         (* Location-aware sizing: storage uses slot counts, memory uses bytes.
            Mirrors Python: t.get_size_in(data_loc) in _lower_tuple_subscript *)
         let elem_sizes =
           MAP (λ(name, fty, sz). if is_slot_addressed base_loc
                                  then (sz + 31) DIV 32 else sz)
               fld_info in
         let offset = SUM (TAKE idx elem_sizes) in
         let (ptr, st2) = compile_tuple_subscript base_op offset st1 in
         (LocatedValue ret_ty (mk_ptr ptr base_loc), st2)
     | _ =>
       (* Base needs raw pointer, idx needs VALUE *)
       let (base_vv, st1) = cfn cenv ty base_e st in
       let base_op = vv_operand base_vv in
       let (idx_op, st2) = lower_value cfn cenv ty idx_e st1 in
       let loc = infer_array_location cenv base_e in
       let is_dynamic = infer_array_is_dynamic cenv base_e in
       let elem_ty = (case base_type of
                        SOME (ArrayT t _) => t
                      | _ => BaseT (UintT 256)) in
       let static_count = (case base_type of
                             SOME (ArrayT _ (Fixed n)) => n
                           | _ => 0) in
       let ws = word_scale loc in
       let elem_size = elem_size_in_location cenv loc elem_ty in
       let load_opc = (case loc of
                         LocStorage => SLOAD
                       | LocTransient => TLOAD
                       | LocCalldata => CALLDATALOAD
                       | _ => MLOAD) in
       let is_signed_idx = is_signed_type (expr_type idx_e) in
       let (elem_ptr, st3) =
         compile_array_subscript base_op idx_op is_dynamic static_count
                                      ws elem_size is_signed_idx load_opc st2 in
       (LocatedValue ret_ty (mk_ptr elem_ptr loc), st3))
End

(* Compile attribute access. Returns VyperValue with correct location.
   unwrap_value handles loading for word types.
   Mirrors Python: expr.py lower_Attribute → VyperValue.from_ptr *)
Definition compile_attribute_def:
  compile_attribute cfn cenv ret_ty ty base_e field st =
    (let (base_vv, st1) = cfn cenv ty base_e st in
     case FLOOKUP cenv.ce_vars field of
       SOME (StorageLoc slot) =>
         (LocatedValue ret_ty (mk_ptr (Lit slot) LocStorage), st1)
     | SOME (TransientLoc slot) =>
         (LocatedValue ret_ty (mk_ptr (Lit slot) LocTransient), st1)
     | SOME (ImmutableLoc offset) =>
         (LocatedValue ret_ty (mk_ptr (Lit (n2w offset)) LocCode), st1)
     | _ =>
         let base_op = vv_operand base_vv in
         let base_loc = (case vv_location base_vv of
                           SOME l => l | NONE => LocMemory) in
         let struct_name = (case base_e of
                              Name _ id => (case cenv.ce_var_type id of
                                              SOME (StructT sn) => sn
                                            | _ => "")
                            | _ => "") in
         let is_storage_loc = (case base_loc of
                                 LocStorage => T
                               | LocTransient => T
                               | _ => F) in
         let fields = cenv.ce_struct_fields struct_name in
         let field_offset =
           if is_storage_loc then struct_field_offset_slots fields field
           else struct_field_offset fields field in
         if field_offset = 0 then (LocatedValue ret_ty (mk_ptr base_op base_loc), st1)
         else let (ptr, st2) = emit_op ADD [base_op; Lit (n2w field_offset)] st1 in
              (LocatedValue ret_ty (mk_ptr ptr base_loc), st2))
End

Definition compile_struct_lit_def:
  compile_struct_lit cfn cenv ty [] buf_op cur_offset st = (buf_op, st) ∧
  compile_struct_lit cfn cenv ty ((fname, e)::rest) buf_op cur_offset st =
    (let e_ty = expr_type e in
     let is_prim = is_word_type e_ty in
     let struct_name = (case ty of StructT n => n | _ => "") in
     let fld_info = cenv.ce_struct_fields struct_name in
     let field_size = (case ALOOKUP fld_info fname of
         SOME (fty, sz) => sz | NONE => 32) in
     let (dst, st1) = if cur_offset = 0 then (buf_op, st)
                       else emit_op ADD [buf_op; Lit (n2w cur_offset)] st in
     if is_prim then
       (* Word type: unwrap to get VALUE, MSTORE it *)
       let (v, st2) = lower_value cfn cenv e_ty e st1 in
       let (_, st3) = emit_void MSTORE [dst; v] st2 in
       compile_struct_lit cfn cenv ty rest buf_op (cur_offset + field_size) st3
     else
       (* Complex type: unwrap copies non-memory to memory, returns ptr. MCOPY. *)
       let (v, st2) = lower_value cfn cenv e_ty e st1 in
       let (_, st3) = emit_void MCOPY [dst; v; Lit (n2w field_size)] st2 in
       compile_struct_lit cfn cenv ty rest buf_op (cur_offset + field_size) st3)
Termination
  WF_REL_TAC `measure (λ(cfn,cenv,ty,flds,buf,off,st). LENGTH flds)` >> simp[]
End

(* NOTE: compile_call_args deleted — superseded by
   compile_stage_intcall_args which handles stack/memory dispatch. *)

(* Store compiled args to memory-layout buffer at proper type offsets.
   Used for ExtCall ABI encoding: each arg stored at
   offset += type_memory_bytes(arg_type), not fixed 32.
   For word types (is_word_type), store value via MSTORE.
   For complex types, compile_expr returns a memory pointer; MCOPY data.
   Mirrors Python: module.py loop `offset += arg_typ.memory_bytes_required` *)
Definition compile_extcall_store_args_def:
  compile_extcall_store_args cfn cenv [] _ buf_op offset st = ((), st) ∧
  compile_extcall_store_args cfn cenv (e::es) [] buf_op offset st =
    (* Fallback: no type info, treat as word. Use lower_value for unwrap. *)
    (let (v, st1) = lower_value cfn cenv (expr_type e) e st in
     let (dst, st2) = if offset = 0 then (buf_op, st1)
                       else emit_op ADD [buf_op; Lit (n2w offset)] st1 in
     let (_, st3) = emit_void MSTORE [dst; v] st2 in
     compile_extcall_store_args cfn cenv es [] buf_op (offset + 32) st3) ∧
  compile_extcall_store_args cfn cenv (e::es) (ty::tys) buf_op offset st =
    (let is_prim = is_word_type ty in
     let mem_size = type_memory_bytes cenv ty in
     (* lower_value unwraps: loads prims from any location,
        copies complex non-memory to memory. *)
     let (v, st1) = lower_value cfn cenv ty e st in
     let (dst, st2) = if offset = 0 then (buf_op, st1)
                       else emit_op ADD [buf_op; Lit (n2w offset)] st1 in
     let (_, st3) =
       if is_prim then emit_void MSTORE [dst; v] st2
       else if is_bytestring_type ty then
         compile_store_bytestring v dst st2
       else emit_void MCOPY [dst; v; Lit (n2w mem_size)] st2 in
     compile_extcall_store_args cfn cenv es tys buf_op (offset + mem_size) st3)
Termination
  WF_REL_TAC `measure (λ(cfn,cenv,es,tys,buf,off,st). LENGTH es)` >> simp[]
End

(* KNOWN LIMITATION: No safe_cast validation at internal call boundaries.
   The Vyper interpreter applies safe_cast per argument (bind_arguments) and
   per return value (after handle_function). The lowering emits no type checks.
   This is correct for well-typed programs (type checker guarantees safe_cast
   succeeds), but the formal proof needs: well_typed ⇒ safe_cast is identity.
   Also: default argument expansion not performed — frontend must inline defaults
   into the Call AST node before codegen (Python does this). *)
Definition compile_call_def:
  compile_call cfn cenv ret_ty ty (IntCall func_id) args default_ret st =
    (let label = nsid_to_string func_id in
     let (returns_count, return_buf_size, pass_via_stack) = cenv.ce_func_info label in
     let (arg_vals, st1) = compile_multi_exprs cfn cenv args st in
     let (return_buf, st2) =
       if returns_count > 0 then
                  let (rbuf_alloc, st_b) = compile_alloc_buffer (32 * returns_count) st1 in
         (SOME rbuf_alloc, st_b)
       else if return_buf_size > 0 then
                  let (rbuf_alloc, st_b) = compile_alloc_buffer return_buf_size st1 in
         (SOME rbuf_alloc, st_b)
       else (NONE, st1) in
     let arg_types = MAP expr_type args in
     let (invoke_args, st3) =
       compile_stage_intcall_args cenv arg_vals pass_via_stack arg_types st2 in
     let buf_prefix = (case return_buf of
         SOME rbuf => if returns_count = 0 then [rbuf.buf_operand] else []
       | NONE => []) in
     let all_invoke_args = buf_prefix ++ invoke_args in
     if returns_count > 0 then
       (* Multi-return: INVOKE with multiple outputs, store ALL results.
          Returns LocatedValue to buffer. unwrap_value handles MLOAD for word types.
          Mirrors Python: return VyperValue.from_ptr(return_buf, MEMORY) *)
       case return_buf of
         SOME rbuf =>
           let (results, st4) = emit_multi_op INVOKE
                 (Label label :: all_invoke_args) returns_count st3 in
           let (_, st5) = store_multi_results rbuf.buf_operand results 0 st4 in
           (LocatedValue ret_ty (base_ptr rbuf), st5)
       | NONE =>
           (* Single stack return — operand IS the value *)
           let (result, st4) = emit_op INVOKE
                 (Label label :: all_invoke_args) st3 in
           (StackValue ret_ty result, st4)
     else
       (* Void call or memory return *)
       let (_, st4) = emit_void INVOKE (Label label :: all_invoke_args) st3 in
       case return_buf of
         SOME rbuf => (LocatedValue ret_ty (base_ptr rbuf), st4)
       | NONE => (StackValue ret_ty (Lit 0w), st4)) ∧
  compile_call cfn cenv ret_ty ty (ExtCall is_static (func_name, arg_types,
                                           return_type))
              args default_ret st =
    (case args of
       [] => let (_, st') = emit_inst INVALID [] [] st in
             (StackValue ret_ty (Lit 0w), st')
     | (addr_e :: rest_after_addr) =>
       let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
       let (value_op, func_args, st2) =
         if is_static then (Lit 0w, rest_after_addr, st1)
         else case rest_after_addr of
                (val_e :: fa) =>
                  let (vo, st') = lower_value cfn cenv
                                    (BaseT (UintT 256)) val_e st1 in
                  (vo, fa, st')
              | _ => (Lit 0w, [], st1)
       in
       (* Compile args to memory-layout buffer (proper type offsets).
          Then ABI-encode via compile_external_call_kwargs.
          Mirrors Python: store each arg at arg_typ.memory_bytes_required
          offsets, then abi_encode_to_buf. *)
       let args_mem_size = SUM (MAP (type_memory_bytes cenv) arg_types) in
              let (args_buf_alloc, st4) = compile_alloc_buffer (MAX 32 args_mem_size) st2 in
              let args_buf = args_buf_alloc.buf_operand in
       let (_, st5) = compile_extcall_store_args cfn cenv func_args
                        arg_types args_buf 0 st4 in
       let args_abi_size = abi_size_bound (cenv_sft cenv) (TupleT arg_types) in
       let args_enc_info = type_to_abi_enc_info cenv (TupleT arg_types) in
       (* Return ABI sizes: wrap single non-tuple returns in TupleT.
          Python: calculate_type_for_external_return wraps non-tuple returns.
          return_abi_size = wrapped_return_t.abi_type.size_bound()
          min_return_size = wrapped_return_t.abi_type.static_size() *)
       (* ABI spec: return values are ALWAYS encoded as a tuple.
          Single-element tuples and non-tuple types get wrapped.
          Only multi-element tuples (length > 1) are already tuples.
          Mirrors Python: needs_external_call_wrap / calculate_type_for_external_return *)
       let wrapped_return = (case return_type of
                               TupleT ts =>
                                 if LENGTH ts > 1 then return_type
                                 else TupleT [return_type]
                             | _ => TupleT [return_type]) in
       let return_abi_size = abi_size_bound (cenv_sft cenv) wrapped_return in
       let min_return_size = abi_static_size (cenv_sft cenv) wrapped_return in
       let ret_mem_bytes = type_memory_bytes cenv return_type in
       let method_id_val = cenv.ce_method_id func_name in
       let skip_contract_check = F in
       let (gas_op, st6) = emit_op GAS [] st5 in
       let (has_default, default_op, st7) =
         case default_ret of
           SOME def_e =>
             (* lower_value handles materialization for all locations *)
             let (dop, st') = lower_value cfn cenv return_type def_e st6 in
             (T, dop, st')
         | NONE => (F, Lit 0w, st6) in
       let ret_dec_info = type_to_abi_dec_info cenv wrapped_return in
       let is_prim_return = is_word_type return_type in
       (* compile_external_call_kwargs returns (operand, st).
          Wrap as LocatedValue for non-void, StackValue for void. *)
       let (result_op, st8) =
         compile_external_call_kwargs addr_op args_buf args_abi_size
                                    method_id_val return_abi_size min_return_size
                                    ret_mem_bytes is_static value_op gas_op
                                    skip_contract_check has_default default_op
                                    is_prim_return
                                    args_enc_info ret_dec_info st7 in
       if return_abi_size = 0 then (StackValue ret_ty result_op, st8)
       else (LocatedValue ret_ty (mk_ptr result_op LocMemory), st8)) ∧
  compile_call cfn cenv ret_ty ty Send args default_ret st =
    (case args of
       [addr_e; val_e] =>
         let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
         let (val_op, st2) = lower_value cfn cenv (BaseT (UintT 256)) val_e st1 in
         let gas_op = Lit 0w in
         let (success, st3) = emit_op CALL [gas_op; addr_op; val_op;
                                            Lit 0w; Lit 0w; Lit 0w; Lit 0w] st2 in
         let (_, st4) = emit_void ASSERT [success] st3 in
         (StackValue ret_ty (Lit 0w), st4)
     | _ => let (_, st') = emit_inst INVALID [] [] st in
            (StackValue ret_ty (Lit 0w), st'))
End

(* ===== Builtin Dispatch Helpers ===== *)

(* Pattern predicates to avoid nested case on expr/type in dispatchers.
   HOL4's mk_functional expands nested case into pattern clauses,
   causing pattern completion explosion. Using if/then avoids this. *)
Definition is_msg_data_def:
  is_msg_data (Attribute _ (Name _ "msg") "data") = T ∧
  is_msg_data _ = F
End

Definition is_self_code_def:
  is_self_code (Attribute _ (Name _ "self") "code") = T ∧
  is_self_code _ = F
End

Definition is_extcode_def:
  is_extcode (Attribute _ _ "code") = T ∧
  is_extcode _ = F
End

Definition extcode_addr_expr_def:
  extcode_addr_expr (Attribute _ addr_e "code") = addr_e ∧
  extcode_addr_expr _ = Literal ARB (IntL 0)
End

(* Invert helper: avoids nested case on type in dispatcher.
   FlagT: XOR with member mask. Other: bitwise NOT.
   NOTE: Python only allows ~ on uint256, bytes32, FlagT.
   The catch-all relies on the Vyper type checker to prevent
   ~ on signed types where NOT has surprising semantics. *)
Definition compile_invert_def:
  compile_invert v (FlagT flag_name) cenv st =
    (let n_members = cenv.ce_flag_n_members flag_name in
     let mask = (2 ** n_members) - 1 in
     emit_op XOR [v; Lit (n2w mask)] st) ∧
  compile_invert v _ cenv st = emit_op NOT [v] st
End

(* Acc accessor dispatch: avoids nested case on addr_accessor in dispatcher.
   All accessors need the address VALUE (unwrapped). Returns (operand # state).
   Caller wraps with as_stack_val.
   NOTE: Python (post-#4869) always emits BALANCE(addr)/EXTCODESIZE(addr).
   The self.balance→SELFBALANCE fold is now an IR optimization pass
   (AlgebraicOptimizationPass), not done in the frontend. *)
Definition compile_acc_def:
  compile_acc cfn cenv addr_e Balance st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     emit_op BALANCE [addr_op] st1) ∧
  compile_acc cfn cenv addr_e Codesize st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     emit_op EXTCODESIZE [addr_op] st1) ∧
  compile_acc cfn cenv addr_e Codehash st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     emit_op EXTCODEHASH [addr_op] st1) ∧
  compile_acc cfn cenv addr_e IsContract st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     let (cs_op, st2) = emit_op EXTCODESIZE [addr_op] st1 in
     emit_op GT [cs_op; Lit 0w] st2) ∧
  compile_acc cfn cenv addr_e Address st =
    lower_value cfn cenv (BaseT AddressT) addr_e st ∧
  compile_acc cfn cenv addr_e Code st =
    (* Python: CompilerPanic(".code requires slice() context").
       Bare .code access is invalid — only valid inside slice(). *)
    let (_, st') = emit_inst INVALID [] [] st in
    (Lit 0w, st')
End


(* ===== VyperValue Unwrap ===== *)
(* ===== Expression Compiler ===== *)

(* compile_expr + dispatchers: 3-function mutual recursion.
   Returns vyper_value: StackValue for computed values, LocatedValue for pointers.
   Consumers use lower_value (= compile_expr + unwrap_value) when they need
   the loaded value, compile_expr directly when they need location info.
   Nested case expressions extracted to helpers (compile_invert, compile_acc,
   is_msg_data, is_self_code, is_extcode) to reduce pattern completion. *)
val compile_expr_defn = Defn.Hol_defn "compile_expr" `
  compile_expr cenv ty e st =
    (let ret_ty = expr_type e in
     case e of
     Literal _ l => compile_literal_vv ret_ty l st
   | Name _ id => compile_name_vv cenv ret_ty id st
   | IfExp _ cond_e then_e else_e =>
       (let (cond_op, st1) = lower_value compile_expr cenv
                               (BaseT BoolT) cond_e st in
        let (result_var, st2) = fresh_var st1 in
        let (then_lbl, st3) = fresh_label "then" st2 in
        let (else_lbl, st4) = fresh_label "else" st3 in
        let (exit_lbl, st5) = fresh_label "exit" st4 in
        let (_, st6) = emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] st5 in
        let (_, st7) = new_block then_lbl st6 in
        let (then_op, st8) = lower_value compile_expr cenv ty then_e st7 in
        let (_, st9) = emit_inst ASSIGN [then_op] [result_var] st8 in
        let (_, st10) = emit_inst JMP [Label exit_lbl] [] st9 in
        let (_, st11) = new_block else_lbl st10 in
        let (else_op, st12) = lower_value compile_expr cenv ty else_e st11 in
        let (_, st13) = emit_inst ASSIGN [else_op] [result_var] st12 in
        let (_, st14) = emit_inst JMP [Label exit_lbl] [] st13 in
        let (_, st15) = new_block exit_lbl st14 in
        (StackValue ret_ty (Var result_var), st15))
   | Builtin _ bi args =>
       compile_builtin_dispatch cenv ret_ty ty bi args st
   | TypeBuiltin _ tb tbt_ret_ty args =>
       compile_type_builtin_dispatch cenv ret_ty ty tb tbt_ret_ty args st
   | Subscript _ base_e idx_e =>
       compile_subscript compile_expr cenv ret_ty ty base_e idx_e st
   | Attribute _ base_e fld_name =>
       compile_attribute compile_expr cenv ret_ty ty base_e fld_name st
   | StructLit _ name fields =>
       (let struct_name = SND name in
        let fld_info = cenv.ce_struct_fields struct_name in
        let total_size = SUM (MAP (SND o SND) fld_info) in
                let (buf_alloc, st2) = compile_alloc_buffer total_size st in
                let buf = buf_alloc.buf_operand in
        let (_, st3) =
          compile_struct_lit compile_expr cenv ty fields buf 0 st2 in
        (LocatedValue ret_ty (base_ptr buf_alloc), st3))
   | FlagMember _ flag_nsid mem_name =>
       (let flag_name = nsid_to_string flag_nsid in
        let flag_id = cenv.ce_flag_member_id flag_name mem_name in
        (StackValue ret_ty (Lit (n2w (2 ** flag_id))), st))
   | BareGlobalName _ id =>
       (case FLOOKUP cenv.ce_vars id of
          SOME (ImmutableLoc offset) =>
            (LocatedValue ret_ty (mk_ptr (Lit (n2w offset)) LocCode), st)
        | SOME (MemLoc offset _) =>
            (LocatedValue ret_ty (mk_ptr (Lit (n2w offset)) LocMemory), st)
        | _ => let (_, st') = emit_inst INVALID [] [] st in
               (StackValue ret_ty (Lit 0w), st'))
   | TopLevelName _ nsid =>
       (let name = nsid_to_string nsid in
        case FLOOKUP cenv.ce_vars name of
          SOME (StorageLoc slot) =>
            (LocatedValue ret_ty (mk_ptr (Lit slot) LocStorage), st)
        | SOME (TransientLoc slot) =>
            (LocatedValue ret_ty (mk_ptr (Lit slot) LocTransient), st)
        | SOME (ImmutableLoc offset) =>
            (LocatedValue ret_ty (mk_ptr (Lit (n2w offset)) LocCode), st)
        | _ => let (_, st') = emit_inst INVALID [] [] st in
               (StackValue ret_ty (Lit 0w), st'))
   | Call _ target args default_ret =>
       compile_call compile_expr cenv ret_ty ty target args default_ret st
   | Pop _ target =>
       (* Returns LocatedValue with element location. unwrap_value handles loading. *)
       (let target_op = compile_target_base cenv target in
        let (loc, arr_name) = (case target of
            NameTarget id => (infer_array_location cenv (Name ARB id), id)
          | TopLevelNameTarget nsid =>
              (infer_array_location cenv (Attribute ARB (Name ARB "self") (SND nsid)), SND nsid)
          | _ => (LocMemory, "")) in
        let ws = word_scale loc in
        let fty_opt = cenv.ce_var_type arr_name in
        let elem_ty = (case fty_opt of
            SOME (ArrayT t _) => t
          | _ => BaseT (IntT 256)) in
        let elem_size = elem_size_in_location cenv loc elem_ty in
        let load_opc = (case loc of
           LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD) in
        let store_opc = (case loc of
           LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE) in
        let (elem_ptr, st1) =
          compile_dynarray_pop target_op ws elem_size load_opc store_opc st in
        (LocatedValue ret_ty (mk_ptr elem_ptr loc), st1))) ∧

  compile_builtin_dispatch cenv ret_ty ty bi args st =
    (case bi of
       Bop op =>
         (let e1 = HD args in let e2 = HD (TL args) in
          (* Use operand type for bounds, not threading ty.
             Python: node.left._metadata["type"] *)
          let op_ty = expr_type e1 in
          let rhs_ty = expr_type e2 in
          (* Array membership: In/NotIn on arrays.
             List literals: unroll to equality chain.
             Variable arrays: loop with early break.
             Flag types: use bitwise AND (handled by compile_compare below).
             Mirrors Python: expr.py lower_Compare In/NotIn dispatch *)
          if (op = In ∨ op = NotIn) ∧ is_ArrayT rhs_ty then
            let is_in = (op = In) in
            let (needle, st1) = lower_value compile_expr cenv op_ty e1 st in
            case e2 of
              Builtin _ (MakeArray _ _) elems =>
                (let (elem_ops, st2) =
                   compile_multi_exprs compile_expr cenv elems st1 in
                 if is_in then as_stack_val ret_ty (compile_list_membership_in needle elem_ops st2)
                 else as_stack_val ret_ty (compile_list_membership_notin needle elem_ops st2))
            | _ =>
                (* Variable array: lower to pointer, then delegate to helper *)
                let (arr_vv, st2) = compile_expr cenv rhs_ty e2 st1 in
                as_stack_val ret_ty
                  (compile_var_array_membership cenv needle arr_vv rhs_ty is_in st2)
          else if is_bytestring_type op_ty ∧ (op = Eq ∨ op = NotEq) then
            (* lower_value handles ensure_in_memory for complex types *)
            let (m1, st1) = lower_value compile_expr cenv op_ty e1 st in
            let (m2, st2) = lower_value compile_expr cenv op_ty e2 st1 in
            let (h1, st3) = compile_bytestring_hash m1 st2 in
            let (h2, st4) = compile_bytestring_hash m2 st3 in
            if op = Eq then as_stack_val ret_ty (emit_op EQ [h1; h2] st4)
            else
              let (eq_result, st5) = emit_op EQ [h1; h2] st4 in
              as_stack_val ret_ty (emit_op ISZERO [eq_result] st5)
          else
          let (v1, st1) = lower_value compile_expr cenv op_ty e1 st in
          let (v2, st2) = lower_value compile_expr cenv op_ty e2 st1 in
          as_stack_val ret_ty (compile_binop op v1 v2 op_ty st2))
     | Not =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv (BaseT BoolT) e1 st in
          as_stack_val ret_ty (emit_op ISZERO [v] st1))
     | Neg =>
         (let e1 = HD args in
          let neg_ty = expr_type e1 in
          let (v, st1) = lower_value compile_expr cenv neg_ty e1 st in
          as_stack_val ret_ty (compile_neg v neg_ty st1))
     | Invert =>
         (let e1 = HD args in
          let inv_ty = expr_type e1 in
          let (v, st1) = lower_value compile_expr cenv inv_ty e1 st in
          as_stack_val ret_ty (compile_invert v inv_ty cenv st1))
     | Env item => as_stack_val ret_ty (compile_env_var item st)
     | Acc item =>
         (let e1 = HD args in
          as_stack_val ret_ty (compile_acc compile_expr cenv e1 item st))
     | Keccak256 =>
         (let e1 = HD args in
          let arg_ty = expr_type e1 in
          if is_bytestring_type arg_ty then
            let (mem_ptr, st1) = lower_value compile_expr cenv arg_ty e1 st in
            as_stack_val ret_ty (compile_keccak256_bytes mem_ptr st1)
          else case arg_ty of
            BaseT (BytesT (Fixed m)) =>
              let (v, st1) = lower_value compile_expr cenv arg_ty e1 st in
              as_stack_val ret_ty (compile_keccak256_bytesm v m st1)
          | _ =>
              let (v, st1) = lower_value compile_expr cenv arg_ty e1 st in
              as_stack_val ret_ty (compile_keccak256_word v st1))
     | Sha256 =>
         (let e1 = HD args in
          let arg_ty = expr_type e1 in
          if is_bytestring_type arg_ty then
            let (mem_ptr, st1) = lower_value compile_expr cenv arg_ty e1 st in
            as_stack_val ret_ty (compile_sha256_bytes mem_ptr st1)
          else case arg_ty of
            BaseT (BytesT (Fixed m)) =>
              let (v, st1) = lower_value compile_expr cenv arg_ty e1 st in
              as_stack_val ret_ty (compile_sha256_bytesm v m st1)
          | _ =>
              let (v, st1) = lower_value compile_expr cenv arg_ty e1 st in
              as_stack_val ret_ty (compile_sha256_word v st1))
     | Len =>
         (let e1 = HD args in
          if is_msg_data e1 then
            as_stack_val ret_ty (compile_builtin_calldatasize st)
          else
            (* Len needs the raw ptr to read length word *)
            let (vv, st1) = compile_expr cenv ty e1 st in
            let v = vv_operand vv in
            let loc = (case vv_location vv of
                         SOME l => l | NONE => LocMemory) in
            as_stack_val ret_ty (compile_builtin_len cenv.ce_is_ctor v loc st1))
     | BlockHash =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_stack_val ret_ty (compile_blockhash v st1))
     | BlobHash =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_stack_val ret_ty (compile_blobhash v st1))
     | AddMod =>
         (let a = HD args in let b = EL 1 args in let c = EL 2 args in
          let (va, st1) = lower_value compile_expr cenv ty a st in
          let (vb, st2) = lower_value compile_expr cenv ty b st1 in
          let (vc, st3) = lower_value compile_expr cenv ty c st2 in
          as_stack_val ret_ty (compile_addmod va vb vc st3))
     | MulMod =>
         (let a = HD args in let b = EL 1 args in let c = EL 2 args in
          let (va, st1) = lower_value compile_expr cenv ty a st in
          let (vb, st2) = lower_value compile_expr cenv ty b st1 in
          let (vc, st3) = lower_value compile_expr cenv ty c st2 in
          as_stack_val ret_ty (compile_mulmod va vb vc st3))
     | Isqrt =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_stack_val ret_ty (compile_isqrt v st1))
     | Ceil =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_stack_val ret_ty (compile_ceil v 10000000000 st1))
     | Floor =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_stack_val ret_ty (compile_floor v 10000000000 st1))
     | PowMod256 =>
         (let e1 = HD args in let e2 = EL 1 args in
          let (v1, st1) = lower_value compile_expr cenv ty e1 st in
          let (v2, st2) = lower_value compile_expr cenv ty e2 st1 in
          as_stack_val ret_ty (compile_pow_mod256 v1 v2 st2))
     | ECRecover =>
         (let e_hash = HD args in let e_v = EL 1 args in
          let e_r = EL 2 args in let e_s = EL 3 args in
          let (vh, st1) = lower_value compile_expr cenv ty e_hash st in
          let (vv, st2) = lower_value compile_expr cenv ty e_v st1 in
          let (vr, st3) = lower_value compile_expr cenv ty e_r st2 in
          let (vs', st4) = lower_value compile_expr cenv ty e_s st3 in
          as_stack_val ret_ty (compile_ecrecover vh vv vr vs' st4))
     | ECAdd =>
         (let e_p1 = HD args in let e_p2 = EL 1 args in
          let p1_ty = expr_type e_p1 in let p2_ty = expr_type e_p2 in
          let (p1_vv, st1) = compile_expr cenv p1_ty e_p1 st in
          let (p1, st1a) = unwrap_value cenv p1_vv st1 in
          let (p2_vv, st2) = compile_expr cenv p2_ty e_p2 st1a in
          let (p2, st2a) = unwrap_value cenv p2_vv st2 in
          let (x1, st3) = emit_op MLOAD [p1] st2a in
          let (y1_ptr, st4) = emit_op ADD [p1; Lit 32w] st3 in
          let (y1, st5) = emit_op MLOAD [y1_ptr] st4 in
          let (x2, st6) = emit_op MLOAD [p2] st5 in
          let (y2_ptr, st7) = emit_op ADD [p2; Lit 32w] st6 in
          let (y2, st8) = emit_op MLOAD [y2_ptr] st7 in
          as_ptr_val ret_ty LocMemory (compile_ecadd x1 y1 x2 y2 st8))
     | ECMul =>
         (let e_p = HD args in let e_s = EL 1 args in
          let p_ty = expr_type e_p in
          let (p_vv, st1) = compile_expr cenv p_ty e_p st in
          let (p, st1a) = unwrap_value cenv p_vv st1 in
          let (s, st2) = lower_value compile_expr cenv (BaseT (UintT 256)) e_s st1a in
          let (x, st3) = emit_op MLOAD [p] st2 in
          let (y_ptr, st4) = emit_op ADD [p; Lit 32w] st3 in
          let (y, st5) = emit_op MLOAD [y_ptr] st4 in
          as_ptr_val ret_ty LocMemory (compile_ecmul x y s st5))
     | Concat max_len =>
         (let arg_infos = MAP (λe.
            let ety = expr_type e in
            if is_bytestring_type ety then (T, 0:num)
            else case ety of
              BaseT (BytesT (Fixed m)) => (F, m)
            | _ => (F, 32:num)) args in
          let alloc_size = 32 + ((max_len + 31) DIV 32) * 32 in
                    let (buf_op_alloc, st2) = compile_alloc_buffer alloc_size st in
                    let buf_op = buf_op_alloc.buf_operand in
          let (data_ptr, st3) = emit_op ADD [buf_op; Lit 32w] st2 in
          let (final_offset, st4) = compile_concat compile_expr cenv args
                                      data_ptr arg_infos (Lit 0w) st3 in
          let (_, st5) = emit_void MSTORE [buf_op; final_offset] st4 in
          (LocatedValue ret_ty (base_ptr buf_op_alloc), st5))
     | Slice max_len =>
         (let src_e = HD args in let start_e = EL 1 args in let len_e = EL 2 args in
          let out_size = max_len + 32 in
          if is_msg_data src_e then
            (let (start_op, st1) = lower_value compile_expr cenv ty start_e st in
             let (len_op, st2) = lower_value compile_expr cenv ty len_e st1 in
             as_ptr_val ret_ty LocMemory (compile_slice_calldata start_op len_op out_size st2))
          else if is_self_code src_e then
            (let (start_op, st1) = lower_value compile_expr cenv ty start_e st in
             let (len_op, st2) = lower_value compile_expr cenv ty len_e st1 in
             as_ptr_val ret_ty LocMemory (compile_slice_code start_op len_op out_size st2))
          else if is_extcode src_e then
            (let addr_e = extcode_addr_expr src_e in
             let (addr_op, st1) = lower_value compile_expr cenv ty addr_e st in
             let (start_op, st2) = lower_value compile_expr cenv ty start_e st1 in
             let (len_op, st3) = lower_value compile_expr cenv ty len_e st2 in
             as_ptr_val ret_ty LocMemory (compile_slice_extcode addr_op start_op len_op out_size st3))
          else
            let src_ty = expr_type src_e in
            (* lower_value handles ensure_in_memory for bytestrings *)
            (let (src_op, st1) = lower_value compile_expr cenv src_ty src_e st in
             let (start_op, st2) = lower_value compile_expr cenv ty start_e st1 in
             let (len_op, st3) = lower_value compile_expr cenv ty len_e st2 in
             if is_bytestring_type src_ty then
               as_ptr_val ret_ty LocMemory (compile_slice_memory src_op start_op len_op out_size st3)
             else
               let m = fixed_bytes_size src_ty in
                              let (tmp_buf_alloc, st5) = compile_alloc_buffer 64 st3 in
                              let tmp_buf = tmp_buf_alloc.buf_operand in
               let (_, st6) = emit_void MSTORE [tmp_buf; Lit (n2w m)] st5 in
               let (data_ptr, st7) = emit_op ADD [tmp_buf; Lit 32w] st6 in
               let (_, st8) = emit_void MSTORE [data_ptr; src_op] st7 in
               as_ptr_val ret_ty LocMemory (compile_slice_memory tmp_buf start_op len_op out_size st8)))
     | Uint2Str max_len =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          as_ptr_val ret_ty LocMemory (compile_uint2str v max_len st1))
     | AsWeiValue denom =>
         (let e1 = HD args in
          let arg_ty = expr_type e1 in
          let (v, st1) = lower_value compile_expr cenv arg_ty e1 st in
          let multiplier = denomination_multiplier denom in
          if is_decimal_type arg_ty then
            as_stack_val ret_ty (compile_as_wei_value_decimal v multiplier (decimal_divisor arg_ty) st1)
          else
            as_stack_val ret_ty (compile_as_wei_value_int v multiplier (is_signed_type arg_ty) st1))
     | MethodId =>
         (let e1 = HD args in
          let (v, st1) = lower_value compile_expr cenv ty e1 st in
          let (hash_op, st2) = compile_keccak256_word v st1 in
          as_stack_val ret_ty (emit_op SHR [Lit 224w; hash_op] st2))
     | MakeArray elem_ty_opt bnd =>
         (let elem_sz = (case elem_ty_opt of
                           SOME et => type_memory_bytes cenv et
                         | NONE => 32) in
          let has_lw = (case bnd of Dynamic _ => T | _ => F) in
          let total_size = (if has_lw then 32 else 0) +
                           LENGTH args * elem_sz in
                    let (buf_op_alloc, st2) = compile_alloc_buffer total_size st in
                    let buf_op = buf_op_alloc.buf_operand in
          as_ptr_val ret_ty LocMemory (compile_make_array compile_expr cenv args elem_sz has_lw total_size
                             buf_op 0 st2))) ∧

  compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st =
    if F then
      compile_builtin_dispatch cenv vv_ty ty (Env TimeStamp) [] st
    else
    (case tb of
       Convert =>
         (let e1 = HD args in
          let src_ty = expr_type e1 in
          let (v, st1) = lower_value compile_expr cenv src_ty e1 st in
          case ret_ty of
            FlagT flag_name =>
              as_stack_val vv_ty (compile_type_convert v
                (ConvToFlag (cenv.ce_flag_n_members flag_name)) st1)
          | _ => as_stack_val vv_ty (compile_type_convert v
                   (mk_convert_op src_ty ret_ty) st1))
     | Empty => (StackValue vv_ty (Lit 0w), st)
     | MaxValue =>
         (let (_, hi) = type_bounds ret_ty in (StackValue vv_ty (Lit hi), st))
     | MinValue =>
         (let (lo, _) = type_bounds ret_ty in (StackValue vv_ty (Lit lo), st))
     | Epsilon => (StackValue vv_ty (Lit 1w), st)
     | Extract32 =>
         (let src_e = HD args in let offset_e = EL 1 args in
          let (src_mem, st1) = lower_value compile_expr cenv
                                 (expr_type src_e) src_e st in
          let (off_op, st2) = lower_value compile_expr cenv ty offset_e st1 in
          let (raw, st3) = compile_extract32 src_mem off_op st2 in
          let clamp = mk_extract32_clamp ret_ty in
          as_stack_val vv_ty (compile_clamp_extract32 raw clamp st3))
     | AbiEncode =>
         (let e1 = HD args in
          let src_ty = expr_type e1 in
          let enc_ty = TupleT [src_ty] in
          let enc_info = type_to_abi_enc_info cenv enc_ty in
          let maxlen = abi_size_bound (cenv_sft cenv) enc_ty in
          if is_word_type src_ty then
            (* Prim word: stage to temp memory for encoder *)
            let (v, st1) = lower_value compile_expr cenv src_ty e1 st in
            let (tmp_alloc, st2) = compile_alloc_buffer 32 st1 in
            let tmp = tmp_alloc.buf_operand in
            let (_, st3) = emit_void MSTORE [tmp; v] st2 in
            as_ptr_val vv_ty LocMemory (lower_abi_encode T NONE tmp enc_info maxlen st3)
          else
            let (src_vv, st1) = compile_expr cenv src_ty e1 st in
            let (src_op, st2) = unwrap_value cenv src_vv st1 in
            as_ptr_val vv_ty LocMemory (lower_abi_encode T NONE src_op enc_info maxlen st2))
     | AbiDecode =>
         (let e1 = HD args in
          let (data_vv, st1) = compile_expr cenv (expr_type e1) e1 st in
          let (data_op, st2) = unwrap_value cenv data_vv st1 in
          let dec_info = type_to_abi_dec_info cenv ret_ty in
          let abi_min = abi_static_size (cenv_sft cenv) ret_ty in
          let abi_max = abi_size_bound (cenv_sft cenv) ret_ty in
          let out_size = type_memory_bytes cenv ret_ty in
          as_ptr_val vv_ty LocMemory (lower_abi_decode data_op dec_info abi_min abi_max out_size st2)))
`;

val _ = Defn.save_defn compile_expr_defn;
