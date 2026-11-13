(* Complete raw-unit correspondence retains all non-block metadata. *)
Theory gasShadowUnit
Ancestors
  gasShadowState venomInst venomCompilerTypes list

Definition gas_shadow_function_def:
  gas_shadow_function f g <=>
    (g with fn_blocks := f.fn_blocks) = f /\
    LIST_REL gas_shadow_block f.fn_blocks g.fn_blocks
End

Definition gas_shadow_context_def:
  gas_shadow_context c d <=>
    (d with ctx_functions := c.ctx_functions) = c /\
    LIST_REL gas_shadow_function c.ctx_functions d.ctx_functions
End

Definition gas_shadow_unit_def:
  gas_shadow_unit u v <=>
    u.cu_data_segment = v.cu_data_segment /\
    gas_shadow_context u.cu_context v.cu_context
End
