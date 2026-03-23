(*
 * String Manipulation Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_uint2str — convert unsigned integer to decimal string
 *
 * Algorithm (matches legacy):
 * 1. Special case: if x == 0, return "0"
 * 2. Loop: extract digits right-to-left using x % 10
 * 3. Store at buf + n_digits - i (overlapping mstores)
 * 4. Store length and return pointer
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/strings.py
 *)

Theory builtinStrings
Ancestors
  emitHelper context compileEnv venomInst
Libs
  monadsyntax

(* uint2str(x) → String[N]
   Multi-block loop: extract digits, store right-to-left.
   Returns pointer to [length][string_data] *)
Definition compile_uint2str_def:
  compile_uint2str val_op n_digits =
    let buf_size = n_digits + 64 in
    do (* Allocate output buffer: n_digits + 32 (length word) + padding *)
       buf_alloc <- compile_alloc_buffer buf_size;
       buf <- return buf_alloc.buf_operand;
       (* Mutable variables *)
       val_var <- fresh_var;
       emit_inst ASSIGN [val_op] [val_var];
       i_var <- fresh_var;
       emit_inst ASSIGN [Lit 0w] [i_var];
       result_var <- fresh_var;
       emit_inst ASSIGN [buf] [result_var];
       (* Blocks *)
       check_lbl <- fresh_label "u2s_check";
       cond_lbl <- fresh_label "u2s_cond";
       body_lbl <- fresh_label "u2s_body";
       zero_lbl <- fresh_label "u2s_zero";
       final_lbl <- fresh_label "u2s_final";
       exit_lbl <- fresh_label "u2s_exit";
       emit_inst JMP [Label check_lbl] [];
       (* Check zero *)
       new_block check_lbl;
       is_zero <- emit_op EQ [Var val_var; Lit 0w];
       emit_inst JNZ [is_zero; Label zero_lbl; Label cond_lbl] [];
       (* Loop condition *)
       new_block cond_lbl;
       done_op <- emit_op EQ [Var val_var; Lit 0w];
       emit_inst JNZ [done_op; Label final_lbl; Label body_lbl] [];
       (* Loop body: extract digit, store *)
       new_block body_lbl;
       digit <- emit_op Mod [Var val_var; Lit 10w];
       char_val <- emit_op ADD [Lit 48w; digit];
       (* pos = buf + n_digits - i *)
       buf_plus_nd <- emit_op ADD [buf; Lit (n2w n_digits)];
       pos <- emit_op SUB [buf_plus_nd; Var i_var];
       emit_void MSTORE [pos; char_val];
       (* val = val / 10, i = i + 1 *)
       new_val <- emit_op Div [Var val_var; Lit 10w];
       emit_inst ASSIGN [new_val] [val_var];
       new_i <- emit_op ADD [Var i_var; Lit 1w];
       emit_inst ASSIGN [new_i] [i_var];
       emit_inst JMP [Label cond_lbl] [];
       (* Handle zero: store "0" *)
       new_block zero_lbl;
       zd_pos <- emit_op ADD [buf; Lit (n2w n_digits)];
       emit_void MSTORE [zd_pos; Lit 48w]; (* '0' = 48 *)
       (* Use fresh ADD — buf_plus_nd from body block is not defined on this path *)
       zd_pos2 <- emit_op ADD [buf; Lit (n2w n_digits)];
       zr_ptr <- emit_op SUB [zd_pos2; Lit 1w];
       emit_void MSTORE [zr_ptr; Lit 1w]; (* length = 1 *)
       emit_inst ASSIGN [zr_ptr] [result_var];
       emit_inst JMP [Label exit_lbl] [];
       (* Finalize: nonzero path *)
       new_block final_lbl;
       (* Fresh ADD — buf_plus_nd from body doesn't statically dominate *)
       buf_nd_f <- emit_op ADD [buf; Lit (n2w n_digits)];
       nz_ptr <- emit_op SUB [buf_nd_f; Var i_var];
       emit_void MSTORE [nz_ptr; Var i_var]; (* length = i *)
       emit_inst ASSIGN [nz_ptr] [result_var];
       emit_inst JMP [Label exit_lbl] [];
       (* Exit *)
       new_block exit_lbl;
       return (Var result_var)
    od
End
