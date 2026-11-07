Theory bodyPtrStructLitOwnershipModuleEntry
Ancestors bodyPtrStructLitOwnershipModuleParams loweringShapeProps

(* Internal-entry interface audit.
   The following ShapeProps interfaces are local, not exported:
   - compile_internal_param_decls_shape: shape_step T with pre T, post
     EVERY (\(name,is_stack,op). plain_operand st op) (FST result).
   - internal_cenv_install_shape: static cenv, optional plain return buffer,
     and retpc_operand pc imply shape for the installed PtrVar return PC
     and converted return-buffer slot.
   - materialize_internal_params_shape: cenv_shape_ok and EVERY captured
     operand plain imply cenv_shape_ok of the returned environment and
     preservation of ce_return_pc. Its Finalise is [local].
   - compile_internal_imm_alloc_shape: conditional fixed-region allocation
     returns NONE or a plain immutable base.
   - internal_installed_body_suffix_shape: installed cenv shape and a
     return-PC operand, with supported-body exclusion, close the suffix.

   compile_internal_function_shape is exported, but its post is T; it
   does not expose the state/environment immediately before compile_stmts.
   That call uses cenv2 with ce_imm_alloca := imm_opt and
   ce_alloca_locals := T, after materialization, temporary return-region
   allocation, and optional nonreentrant lock.

   The attempted materialization ownership/shape join cannot reference
   materialize_internal_params_shape from this theory. New task-owned
   shape interfaces are needed; non-owned ShapeProps is not modified.
   This audit is not a certificate for internal entry or module ownership. *)
