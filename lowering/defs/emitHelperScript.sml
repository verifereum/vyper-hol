(*
 * Emission helpers for compile_state monad.
 * Extracted from exprLowering to break circular dependency
 * with builtin theory files.
 *
 * TOP-LEVEL:
 *   emit_op   — emit instruction with fresh output variable
 *   emit_void — emit instruction with no output
 *   emit_inst — emit instruction with explicit outputs
 *   emit_jmp_if_not_terminated — conditional JMP to target
 *)

Theory emitHelper
Ancestors
  compileEnv venomInst

(* Emit instruction with fresh output variable, return the output as operand *)
Definition emit_op_def:
  emit_op opc ops st =
    let (id, st1) = fresh_id st in
    let (out, st2) = fresh_var st1 in
    let (_, st3) = emit (mk_inst id opc ops [out]) st2 in
    (Var out, st3)
End

(* Emit instruction with no output *)
Definition emit_void_def:
  emit_void opc ops st =
    let (id, st1) = fresh_id st in
    emit (mk_inst id opc ops []) st1
End

(* Emit instruction with explicit output list *)
Definition emit_inst_def:
  emit_inst opc ops outs st =
    let (id, st1) = fresh_id st in
    emit (mk_inst id opc ops outs) st1
End

(* Allocate n fresh variable names, returning them as a list *)
Definition fresh_vars_def:
  fresh_vars (0:num) (st:compile_state) = ([] : string list, st) ∧
  fresh_vars (SUC n) st =
    let (v, st1) = fresh_var st in
    let (vs, st2) = fresh_vars n st1 in
    (v :: vs, st2)
End

(* Emit instruction with n fresh outputs, return outputs as operand list.
   Used for multi-return INVOKE. *)
Definition emit_multi_op_def:
  emit_multi_op opc ops n st =
    let (outs, st1) = fresh_vars n st in
    let (_, st2) = emit_inst opc ops outs st1 in
    (MAP Var outs, st2)
End

(* Emit JMP to target only if current block is not already terminated.
   Mirrors Python: if not bb.is_terminated: bb.append_instruction("jmp", target)
   Used after if/else branches and loop bodies to avoid malformed basic blocks. *)
Definition emit_jmp_if_not_terminated_def:
  emit_jmp_if_not_terminated target_lbl (cs:compile_state) =
    if block_is_terminated cs then ((), cs)
    else emit_inst JMP [Label target_lbl] [] cs
End
