(* Shared predicates for the checked initializer and its execution. *)
structure runtimeDefaultRejectSyntaxLib =
struct
open HolKernel boolLib bossLib
open listTheory venomInstTheory compileEnvTheory vyperASTTheory vyperContextTheory

val default_opcode = ``\opc. ~MEM opc
  [REVERT; INVALID; ASSERT_UNREACHABLE; SSTORE; TSTORE; LOG; SELFDESTRUCT;
   STOP; RETURN; SINK; RET; RETFMP; DRET; INVOKE; RETURNDATACOPY;
   CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]``;

val checked_default_expr = ``\ce e. case e of
    TopLevelName _ nsid =>
      ~(?offset. FLOOKUP ce.ce_module_vars nsid = SOME (ImmutableLoc offset))
  | Builtin _ bi args => bi = Sha256 \/ ~builtin_args_length_ok bi (LENGTH args)
  | TypeBuiltin _ tb _ args => ~type_builtin_args_length_ok tb (LENGTH args)
  | _ => F``;
end
