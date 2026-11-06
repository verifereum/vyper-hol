(* TOP-LEVEL: operand and memory frames for replaying generated instructions.
   These equalities allow already-defined SSA outputs to be overwritten in
   loop iterations while keeping operands outside the written names intact. *)
Theory ssaOperandFrame
Ancestors
  venomState venomInst venomExecSemantics emitHelperProps compileEnv

Theorem eval_operand_update_var_avoids:
  !arg_op name value ss.
    arg_op <> Var name ==>
    eval_operand arg_op (update_var name value ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >> simp[eval_operand_def, lookup_var_update_var]
QED

Theorem eval_operand_mstore_eq:
  !arg_op offset value ss.
    eval_operand arg_op (mstore offset value ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >> simp[eval_operand_def]
QED

Theorem eval_operand_mcopy_eq:
  !arg_op dst src count ss.
    eval_operand arg_op (mcopy dst src count ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >>
  simp[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem mload_update_var:
  !offset name value ss.
    mload offset (update_var name value ss) = mload offset ss
Proof
  simp[mload_def, update_var_def]
QED

Theorem update_var_reset_vars:
  !name value vars ss.
    (update_var name value ss) with vs_vars := vars = ss with vs_vars := vars
Proof
  simp[update_var_def]
QED

Theorem mstore_vars:
  !offset value ss. (mstore offset value ss).vs_vars = ss.vs_vars
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem mcopy_vars:
  !dst src count ss. (mcopy dst src count ss).vs_vars = ss.vs_vars
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem mstore_update_var:
  !offset value name word ss.
    mstore offset value (update_var name word ss) =
      update_var name word (mstore offset value ss)
Proof
  simp[mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem mcopy_update_var:
  !dst src count name word ss.
    mcopy dst src count (update_var name word ss) =
      update_var name word (mcopy dst src count ss)
Proof
  simp[mcopy_def, update_var_def, read_memory_def, write_memory_with_expansion_def]
QED

Theorem mstore_reset_vars:
  !offset value vars ss.
    mstore offset value (ss with vs_vars := vars) =
      (mstore offset value ss) with vs_vars := vars
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem mcopy_reset_vars:
  !dst src count vars ss.
    mcopy dst src count (ss with vs_vars := vars) =
      (mcopy dst src count ss) with vs_vars := vars
Proof
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def]
QED
