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
Libs
  monadsyntax

(* Emit instruction with fresh output variable, return the output as operand *)
Definition emit_op_def:
  emit_op opc ops =
    do id <- fresh_id;
       out <- fresh_var;
       emit (mk_inst id opc ops [out]);
       return (Var out)
    od
End

(* Emit instruction with no output *)
Definition emit_void_def:
  emit_void opc ops =
    do id <- fresh_id;
       emit (mk_inst id opc ops [])
    od
End

(* Emit instruction with explicit output list *)
Definition emit_inst_def:
  emit_inst opc ops outs =
    do id <- fresh_id;
       emit (mk_inst id opc ops outs)
    od
End

(* Allocate n fresh variable names, returning them as a list *)
Definition fresh_vars_def:
  fresh_vars (0:num) = return ([] : string list) ∧
  fresh_vars (SUC n) =
    do v <- fresh_var;
       vs <- fresh_vars n;
       return (v :: vs)
    od
End

(* Emit instruction with n fresh outputs, return outputs as operand list.
   Used for multi-return INVOKE. *)
Definition emit_multi_op_def:
  emit_multi_op opc ops n =
    do outs <- fresh_vars n;
       emit_inst opc ops outs;
       return (MAP Var outs)
    od
End

(* Emit JMP to target only if current block is not already terminated.
   Mirrors Python: if not bb.is_terminated: bb.append_instruction("jmp", target)
   Used after if/else branches and loop bodies to avoid malformed basic blocks. *)
Definition emit_jmp_if_not_terminated_def:
  emit_jmp_if_not_terminated target_lbl =
    do cs <- comp_get;
       if block_is_terminated cs then return ()
       else emit_inst JMP [Label target_lbl] []
    od
End
