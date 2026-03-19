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
Libs
  monadsyntax

(* ===== select (branchless ternary) ===== *)
(* cond ? a : b  =  xor(b, mul(cond, xor(a, b)))
   Mirrors Python: venom/builder.py select() *)
Definition compile_select_def:
  compile_select cond_op then_op else_op =
    do diff <- emit_op XOR [then_op; else_op];
       scaled <- emit_op MUL [cond_op; diff];
       emit_op XOR [else_op; scaled]
    od
End

(* ===== len ===== *)
(* Mirrors Python: simple.py lower_len
   For dyn arrays/bytestrings: load length word from pointer.
   Special case: len(msg.data) → CALLDATASIZE *)
(* len(): load length word from the first slot at pointer.
   is_ctor needed for LocCode: ctor uses ILOAD, runtime uses DLOAD. *)
Definition compile_builtin_len_def:
  compile_builtin_len is_ctor ptr_op loc =
    compile_ptr_load is_ctor loc ptr_op
End

Definition compile_builtin_calldatasize_def:
  compile_builtin_calldatasize = emit_op CALLDATASIZE []
End

(* ===== empty ===== *)
(* Mirrors Python: simple.py lower_empty
   Primitive word: return Lit 0.
   Complex type: allocate buffer and zero it. *)
Definition compile_builtin_empty_prim_def:
  compile_builtin_empty_prim = comp_return (Lit 0w : operand)
End

(* Zero memory region word-by-word.
   Mirrors Python: simple.py _zero_memory.
   n_words: number of 32-byte words to zero.
   Unrolled at compile time (n_words is static). *)
Definition compile_zero_words_def:
  compile_zero_words (base_op:operand) (0:num) = return () ∧
  compile_zero_words base_op (SUC n) =
    let offset = n * 32 in
    do dst <-
         (if offset = 0 then return base_op
          else emit_op ADD [base_op; Lit (n2w offset)]);
       emit_void MSTORE [dst; Lit 0w];
       compile_zero_words base_op n
    od
End

Definition compile_builtin_empty_complex_def:
  compile_builtin_empty_complex size is_bytestring =
    do buf_alloc <- compile_alloc_buffer size;
       buf <- return buf_alloc.buf_operand;
       if is_bytestring then
         (* Bytestring/DynArray: just zero the length word (first 32 bytes).
            Length=0 means no valid data.
            Mirrors Python: simple.py lower_empty bytestring/DynArray case *)
         do emit_void MSTORE [buf; Lit 0w];
            return buf
         od
       else
         (* Other complex types (struct, sarray): zero entire buffer word-by-word.
            Mirrors Python: simple.py lower_empty → _zero_memory *)
         let n_words = (size + 31) DIV 32 in
         do compile_zero_words buf n_words;
            return buf
         od
    od
End

(* ===== min/max ===== *)
(* Mirrors Python: simple.py _lower_minmax
   Branchless select: if (a op b) then a else b *)
Definition compile_builtin_min_def:
  compile_builtin_min a b use_unsigned =
    do cmp <-
         (if use_unsigned then emit_op LT [a; b]
          else emit_op SLT [a; b]);
       compile_select cmp a b
    od
End

Definition compile_builtin_max_def:
  compile_builtin_max a b use_unsigned =
    do cmp <-
         (if use_unsigned then emit_op GT [a; b]
          else emit_op SGT [a; b]);
       compile_select cmp a b
    od
End

(* ===== abs ===== *)
(* Mirrors Python: simple.py lower_abs
   abs(x) for int256: negate if negative, check for MIN_INT overflow.
   abs(-2^255) overflows since 2^255 > MAX_INT256. *)
Definition compile_builtin_abs_def:
  compile_builtin_abs val_op =
    do neg_val <- emit_op SUB [Lit 0w; val_op];
       (* Check MIN_INT: if val < 0 && val == neg_val, it's MIN_INT *)
       is_neg <- emit_op SLT [val_op; Lit 0w];
       is_min_int <- emit_op EQ [val_op; neg_val];
       bad <- emit_op AND [is_neg; is_min_int];
       not_bad <- emit_op ISZERO [bad];
       emit_void ASSERT [not_bad];
       (* Return neg_val if negative, else val *)
       compile_select is_neg neg_val val_op
    od
End
