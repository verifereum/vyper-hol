Theory deploySymSrcBlockFrame
Ancestors
  deploySymSrcHistory runtimeSymSrcInterfaces compileEnv emitHelper context
  loweringShapeDefs list venomInst

Definition deploy_blocks_frame_def:
  deploy_blocks_frame m <=>
    !s B x t. m s = (x,t) ==>
      m (s with cs_blocks := s.cs_blocks ++ B) =
        (x,t with cs_blocks := t.cs_blocks ++ B)
End

Theorem deploy_blocks_frame_return[simp]:
  deploy_blocks_frame (comp_return x)
Proof
  simp[deploy_blocks_frame_def, comp_return_def]
QED

Theorem deploy_blocks_frame_bind:
  deploy_blocks_frame m /\ (!x. deploy_blocks_frame (k x)) ==>
  deploy_blocks_frame (comp_bind m k)
Proof
  simp[deploy_blocks_frame_def, comp_bind_def] >>
  rpt strip_tac >> Cases_on `m s` >> gvs[] >>
  qpat_x_assum `!s B x t. m s = _ ==> _` drule >>
  disch_then (qspec_then `B` assume_tac) >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem deploy_blocks_frame_ignore_bind:
  deploy_blocks_frame m /\ deploy_blocks_frame n ==>
  deploy_blocks_frame (comp_ignore_bind m n)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >>
  irule deploy_blocks_frame_bind >> simp[]
QED

Theorem deploy_blocks_frame_emit[simp]:
  deploy_blocks_frame (emit i)
Proof
  simp[deploy_blocks_frame_def, emit_def]
QED

Theorem deploy_blocks_frame_new_block[simp]:
  deploy_blocks_frame (new_block l)
Proof
  simp[deploy_blocks_frame_def, new_block_def]
QED

Theorem deploy_blocks_terminated[simp]:
  block_is_terminated (s with cs_blocks := B) = block_is_terminated s
Proof
  simp[block_is_terminated_def]
QED

Theorem deploy_blocks_frame_fresh_var[simp]:
  deploy_blocks_frame fresh_var
Proof
  simp[deploy_blocks_frame_def, fresh_var_def]
QED

Theorem deploy_blocks_frame_fresh_id[simp]:
  deploy_blocks_frame fresh_id
Proof
  simp[deploy_blocks_frame_def, fresh_id_def]
QED

Theorem deploy_blocks_frame_fresh_label[simp]:
  deploy_blocks_frame (fresh_label suffix)
Proof
  simp[deploy_blocks_frame_def, fresh_label_def]
QED

Theorem deploy_blocks_frame_emit_inst[simp]:
  deploy_blocks_frame (emit_inst opc ops outs)
Proof
  simp[emit_inst_def] >> irule deploy_blocks_frame_bind >> simp[]
QED

Theorem deploy_blocks_frame_emit_op[simp]:
  deploy_blocks_frame (emit_op opc ops)
Proof
  simp[emit_op_def] >> irule deploy_blocks_frame_bind >> simp[] >>
  gen_tac >> irule deploy_blocks_frame_bind >> simp[] >>
  gen_tac >> irule deploy_blocks_frame_ignore_bind >> simp[]
QED

Theorem deploy_blocks_frame_emit_void[simp]:
  deploy_blocks_frame (emit_void opc ops)
Proof
  simp[emit_void_def] >> irule deploy_blocks_frame_bind >> simp[]
QED

Theorem deploy_blocks_frame_alloc_buffer[simp]:
  deploy_blocks_frame (compile_alloc_buffer n)
Proof
  simp[compile_alloc_buffer_def] >> irule deploy_blocks_frame_bind >> simp[]
QED

Theorem deploy_blocks_frame_transfer:
  deploy_blocks_frame m /\ s.cs_blocks = [] /\ m s = (x,t) /\
  EVERY runtime_sym_inst (state_insts t) /\
  EVERY (\bb. EVERY deploy_sym_inst bb.bb_instructions) B ==>
  EVERY deploy_sym_inst (state_insts (SND (m (s with cs_blocks := B))))
Proof
  rpt strip_tac >>
  `m (s with cs_blocks := B) = (x,t with cs_blocks := t.cs_blocks ++ B)` by
    metis_tac[deploy_blocks_frame_def, APPEND] >>
  simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
       EVERY_APPEND, EVERY_FLAT, EVERY_MAP] >>
  fs[state_insts_def, all_blocks_def, EVERY_APPEND, EVERY_FLAT,
     EVERY_MAP, EVERY_MEM, MEM_REVERSE, MEM_FLAT, MEM_MAP] >>
  metis_tac[runtime_sym_inst_deploy]
QED

Theorem deploy_blocks_frame_jmp_if_not_terminated[simp]:
  deploy_blocks_frame (emit_jmp_if_not_terminated l)
Proof
  simp[deploy_blocks_frame_def, emit_jmp_if_not_terminated_def,
       comp_bind_def, comp_get_def] >>
  rpt strip_tac >> Cases_on `block_is_terminated s` >>
  gvs[comp_return_def] >>
  metis_tac[deploy_blocks_frame_def, deploy_blocks_frame_emit_inst]
QED
