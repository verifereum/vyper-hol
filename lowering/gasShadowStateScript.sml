(* Proof-only correspondence of original and shadow compiler states. *)
Theory gasShadowState
Ancestors
  compileEnv emitHelper venomInst list pair

Definition gas_shadow_inst_def:
  gas_shadow_inst i j <=>
    j = i \/
    (i.inst_opcode = GAS /\ j = i with inst_opcode := GASPRICE)
End

Definition gas_shadow_block_def:
  gas_shadow_block bb shadow <=>
    bb.bb_label = shadow.bb_label /\
    LIST_REL gas_shadow_inst bb.bb_instructions shadow.bb_instructions
End

Definition gas_shadow_state_def:
  gas_shadow_state s t <=>
    s.cs_next_var = t.cs_next_var /\
    s.cs_next_label = t.cs_next_label /\
    s.cs_next_id = t.cs_next_id /\
    s.cs_current_bb = t.cs_current_bb /\
    s.cs_data_sections = t.cs_data_sections /\
    LIST_REL gas_shadow_inst s.cs_current_insts t.cs_current_insts /\
    LIST_REL gas_shadow_block s.cs_blocks t.cs_blocks
End

Definition gas_shadow_compiles_def:
  gas_shadow_compiles (f : 'a compiler) g <=>
    !s t. gas_shadow_state s t ==>
      FST (f s) = FST (g t) /\
      gas_shadow_state (SND (f s)) (SND (g t))
End

Theorem gas_shadow_state_refl:
  gas_shadow_state s s
Proof
  simp[gas_shadow_state_def, LIST_REL_refl, gas_shadow_block_def,
       gas_shadow_inst_def]
QED

Theorem gas_shadow_compiles_return:
  gas_shadow_compiles (comp_return x) (comp_return x)
Proof
  simp[gas_shadow_compiles_def, comp_return_def]
QED

Theorem gas_shadow_compiles_bind:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) ==>
  gas_shadow_compiles (comp_bind f h) (comp_bind g k)
Proof
  rw[gas_shadow_compiles_def] >>
  qpat_x_assum `!s t. gas_shadow_state s t ==> _`
    (qspecl_then [`s`, `t`] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `!x s t. _`
    (qspecl_then [`FST (f s)`, `SND (f s)`, `SND (g t)`] mp_tac) >>
  asm_rewrite_tac [] >>
  Cases_on `f s` >> Cases_on `g t` >> gvs[comp_bind_def]
QED

Theorem gas_shadow_compiles_fresh_var:
  gas_shadow_compiles fresh_var fresh_var
Proof
  rw[gas_shadow_compiles_def, fresh_var_def, gas_shadow_state_def]
QED

Theorem gas_shadow_compiles_fresh_id:
  gas_shadow_compiles fresh_id fresh_id
Proof
  rw[gas_shadow_compiles_def, fresh_id_def, gas_shadow_state_def]
QED

Theorem gas_shadow_compiles_fresh_label:
  gas_shadow_compiles (fresh_label suffix) (fresh_label suffix)
Proof
  rw[gas_shadow_compiles_def, fresh_label_def, gas_shadow_state_def]
QED

Theorem gas_shadow_compiles_emit:
  gas_shadow_inst i j ==>
  gas_shadow_compiles (emit i) (emit j)
Proof
  rw[gas_shadow_compiles_def, emit_def, gas_shadow_state_def,
     LIST_REL_APPEND]
QED

Theorem gas_shadow_compiles_new_block:
  gas_shadow_compiles (new_block label) (new_block label)
Proof
  rw[gas_shadow_compiles_def, new_block_def, gas_shadow_state_def,
     gas_shadow_block_def]
QED

Theorem gas_shadow_compiles_emit_op:
  (opc' = opc \/ (opc = GAS /\ opc' = GASPRICE)) ==>
  gas_shadow_compiles (emit_op opc ops) (emit_op opc' ops)
Proof
  rw[gas_shadow_compiles_def, emit_op_def, comp_ignore_bind_def,
     comp_bind_def, comp_return_def,
     fresh_id_def, fresh_var_def, emit_def, gas_shadow_state_def,
     LIST_REL_APPEND, gas_shadow_inst_def, mk_inst_def]
QED

Theorem gas_shadow_compiles_emit_inst:
  gas_shadow_compiles (emit_inst opc ops outs) (emit_inst opc ops outs)
Proof
  rw[gas_shadow_compiles_def, emit_inst_def, comp_ignore_bind_def,
     comp_bind_def, comp_return_def,
     fresh_id_def, emit_def, gas_shadow_state_def,
     LIST_REL_APPEND, gas_shadow_inst_def]
QED

Theorem gas_shadow_compiles_emit_void:
  gas_shadow_compiles (emit_void opc ops) (emit_void opc ops)
Proof
  rw[gas_shadow_compiles_def, emit_void_def, comp_ignore_bind_def,
     comp_bind_def, comp_return_def,
     fresh_id_def, emit_def, gas_shadow_state_def,
     LIST_REL_APPEND, gas_shadow_inst_def]
QED
