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

(* uint2str(x) → String[N]
   Multi-block loop: extract digits, store right-to-left.
   Returns pointer to [length][string_data] *)
Definition compile_uint2str_def:
  compile_uint2str val_op n_digits st =
    (* Allocate output buffer: n_digits + 32 (length word) + padding *)
    let buf_size = n_digits + 64 in
        let (buf_alloc, st2) = compile_alloc_buffer buf_size st in
        let buf = buf_alloc.buf_operand in
    (* Mutable variables *)
    let (val_var, st3) = fresh_var st2 in
    let (_, st4) = emit_inst ASSIGN [val_op] [val_var] st3 in
    let (i_var, st5) = fresh_var st4 in
    let (_, st6) = emit_inst ASSIGN [Lit 0w] [i_var] st5 in
    let (result_var, st7) = fresh_var st6 in
    let (_, st8) = emit_inst ASSIGN [buf] [result_var] st7 in
    (* Blocks *)
    let (check_lbl, st9) = fresh_label "u2s_check" st8 in
    let (cond_lbl, st10) = fresh_label "u2s_cond" st9 in
    let (body_lbl, st11) = fresh_label "u2s_body" st10 in
    let (zero_lbl, st12) = fresh_label "u2s_zero" st11 in
    let (final_lbl, st13) = fresh_label "u2s_final" st12 in
    let (exit_lbl, st14) = fresh_label "u2s_exit" st13 in
    let (_, st15) = emit_inst JMP [Label check_lbl] [] st14 in
    (* Check zero *)
    let (_, st16) = new_block check_lbl st15 in
    let (is_zero, st17) = emit_op EQ [Var val_var; Lit 0w] st16 in
    let (_, st18) = emit_inst JNZ [is_zero; Label zero_lbl; Label cond_lbl] [] st17 in
    (* Loop condition *)
    let (_, st19) = new_block cond_lbl st18 in
    let (done_op, st20) = emit_op EQ [Var val_var; Lit 0w] st19 in
    let (_, st21) = emit_inst JNZ [done_op; Label final_lbl; Label body_lbl] [] st20 in
    (* Loop body: extract digit, store *)
    let (_, st22) = new_block body_lbl st21 in
    let (digit, st23) = emit_op Mod [Var val_var; Lit 10w] st22 in
    let (char_val, st24) = emit_op ADD [Lit 48w; digit] st23 in
    (* pos = buf + n_digits - i *)
    let (buf_plus_nd, st25) = emit_op ADD [buf; Lit (n2w n_digits)] st24 in
    let (pos, st26) = emit_op SUB [buf_plus_nd; Var i_var] st25 in
    let (_, st27) = emit_void MSTORE [pos; char_val] st26 in
    (* val = val / 10, i = i + 1 *)
    let (new_val, st28) = emit_op Div [Var val_var; Lit 10w] st27 in
    let (_, st29) = emit_inst ASSIGN [new_val] [val_var] st28 in
    let (new_i, st30) = emit_op ADD [Var i_var; Lit 1w] st29 in
    let (_, st31) = emit_inst ASSIGN [new_i] [i_var] st30 in
    let (_, st32) = emit_inst JMP [Label cond_lbl] [] st31 in
    (* Handle zero: store "0" *)
    let (_, st33) = new_block zero_lbl st32 in
    let (zd_pos, st34) = emit_op ADD [buf; Lit (n2w n_digits)] st33 in
    let (_, st35) = emit_void MSTORE [zd_pos; Lit 48w] st34 in (* '0' = 48 *)
    (* Use fresh ADD — buf_plus_nd from body block is not defined on this path *)
    let (zd_pos2, st35a) = emit_op ADD [buf; Lit (n2w n_digits)] st35 in
    let (zr_ptr, st36) = emit_op SUB [zd_pos2; Lit 1w] st35a in
    let (_, st37) = emit_void MSTORE [zr_ptr; Lit 1w] st36 in (* length = 1 *)
    let (_, st38) = emit_inst ASSIGN [zr_ptr] [result_var] st37 in
    let (_, st39) = emit_inst JMP [Label exit_lbl] [] st38 in
    (* Finalize: nonzero path *)
    let (_, st40) = new_block final_lbl st39 in
    (* Fresh ADD — buf_plus_nd from body doesn't statically dominate *)
    let (buf_nd_f, st40a) = emit_op ADD [buf; Lit (n2w n_digits)] st40 in
    let (nz_ptr, st41) = emit_op SUB [buf_nd_f; Var i_var] st40a in
    let (_, st42) = emit_void MSTORE [nz_ptr; Var i_var] st41 in (* length = i *)
    let (_, st43) = emit_inst ASSIGN [nz_ptr] [result_var] st42 in
    let (_, st44) = emit_inst JMP [Label exit_lbl] [] st43 in
    (* Exit *)
    let (_, st45) = new_block exit_lbl st44 in
    (Var result_var, st45)
End
