(*
 * Simple Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_builtin_len     — len(x) for dyn arrays/bytestrings
 *   compile_builtin_empty   — empty(T) → zero value
 *   compile_builtin_min/max — min(a,b), max(a,b) via branchless select
 *   compile_builtin_abs     — abs(x) with MIN_INT overflow check
 *   compile_zero_words    — zero out memory region word-by-word
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/simple.py
 *)

Theory builtinSimple
Ancestors
  emitHelper context compileEnv venomInst

(* ===== select (branchless ternary) ===== *)
(* cond ? a : b  =  xor(b, mul(cond, xor(a, b)))
   Mirrors Python: venom/builder.py select() *)
Definition compile_select_def:
  compile_select cond_op then_op else_op st =
    let (diff, st1) = emit_op XOR [then_op; else_op] st in
    let (scaled, st2) = emit_op MUL [cond_op; diff] st1 in
    emit_op XOR [else_op; scaled] st2
End

(* ===== len ===== *)
(* Mirrors Python: simple.py lower_len
   For dyn arrays/bytestrings: load length word from pointer.
   Special case: len(msg.data) → CALLDATASIZE *)
(* len(): load length word from the first slot at pointer.
   is_ctor needed for LocCode: ctor uses ILOAD, runtime uses DLOAD. *)
Definition compile_builtin_len_def:
  compile_builtin_len is_ctor ptr_op loc st =
    compile_ptr_load is_ctor loc ptr_op st
End

Definition compile_builtin_calldatasize_def:
  compile_builtin_calldatasize = emit_op CALLDATASIZE []
End

(* ===== empty ===== *)
(* Mirrors Python: simple.py lower_empty
   Primitive word: return Lit 0.
   Complex type: allocate buffer and zero it. *)
Definition compile_builtin_empty_prim_def:
  compile_builtin_empty_prim st = (Lit 0w : operand, st)
End

(* Zero memory region word-by-word.
   Mirrors Python: simple.py _zero_memory.
   n_words: number of 32-byte words to zero.
   Unrolled at compile time (n_words is static). *)
Definition compile_zero_words_def:
  compile_zero_words (base_op:operand) (0:num) (st:compile_state) = ((), st) ∧
  compile_zero_words base_op (SUC n) st =
    let offset = n * 32 in
    let (dst, st1) =
      (if offset = 0 then (base_op, st)
       else emit_op ADD [base_op; Lit (n2w offset)] st) in
    let (_, st2) = emit_void MSTORE [dst; Lit 0w] st1 in
    compile_zero_words base_op n st2
End

Definition compile_builtin_empty_complex_def:
  compile_builtin_empty_complex size is_bytestring st =
        let (buf_alloc, st2) = compile_alloc_buffer size st in
        let buf = buf_alloc.buf_operand in
    if is_bytestring then
      (* Bytestring/DynArray: just zero the length word (first 32 bytes).
         Length=0 means no valid data.
         Mirrors Python: simple.py lower_empty bytestring/DynArray case *)
      let (_, st3) = emit_void MSTORE [buf; Lit 0w] st2 in
      (buf, st3)
    else
      (* Other complex types (struct, sarray): zero entire buffer word-by-word.
         Mirrors Python: simple.py lower_empty → _zero_memory *)
      let n_words = (size + 31) DIV 32 in
      let (_, st3) = compile_zero_words buf n_words st2 in
      (buf, st3)
End

(* ===== min/max ===== *)
(* Mirrors Python: simple.py _lower_minmax
   Branchless select: if (a op b) then a else b *)
Definition compile_builtin_min_def:
  compile_builtin_min a b use_unsigned st =
    let (cmp, st1) =
      if use_unsigned then emit_op LT [a; b] st
      else emit_op SLT [a; b] st in
    compile_select cmp a b st1
End

Definition compile_builtin_max_def:
  compile_builtin_max a b use_unsigned st =
    let (cmp, st1) =
      if use_unsigned then emit_op GT [a; b] st
      else emit_op SGT [a; b] st in
    compile_select cmp a b st1
End

(* ===== abs ===== *)
(* Mirrors Python: simple.py lower_abs
   abs(x) for int256: negate if negative, check for MIN_INT overflow.
   abs(-2^255) overflows since 2^255 > MAX_INT256. *)
Definition compile_builtin_abs_def:
  compile_builtin_abs val_op st =
    let (neg_val, st1) = emit_op SUB [Lit 0w; val_op] st in
    (* Check MIN_INT: if val < 0 && val == neg_val, it's MIN_INT *)
    let (is_neg, st2) = emit_op SLT [val_op; Lit 0w] st1 in
    let (is_min_int, st3) = emit_op EQ [val_op; neg_val] st2 in
    let (bad, st4) = emit_op AND [is_neg; is_min_int] st3 in
    let (not_bad, st5) = emit_op ISZERO [bad] st4 in
    let (_, st6) = emit_void ASSERT [not_bad] st5 in
    (* Return neg_val if negative, else val *)
    compile_select is_neg neg_val val_op st6
End
