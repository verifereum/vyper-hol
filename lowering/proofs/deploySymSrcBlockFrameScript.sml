Theory deploySymSrcBlockFrame
Ancestors
  symbolicSourceCompilerFrame
  deploySymSrcHistory runtimeSymSrcInterfaces compileEnv emitHelper context
  loweringShapeDefs list venomInst

Definition deploy_blocks_frame_def:
  deploy_blocks_frame m <=>
    !s B x t. m s = (x,t) ==>
      m (s with cs_blocks := s.cs_blocks ++ B) =
        (x,t with cs_blocks := t.cs_blocks ++ B)
End

Theorem symbolic_frame_deploy:
  symbolic_frame (\blocks s t. t = s with cs_blocks := s.cs_blocks ++ blocks) m <=>
  deploy_blocks_frame m
Proof
  simp[symbolic_frame_def, deploy_blocks_frame_def] >>
  eq_tac >> strip_tac >> rpt gen_tac
  >- (strip_tac >> first_x_assum (qspecl_then [`s`,`B`] mp_tac) >>
      simp[] >> Cases_on `m (s with cs_blocks := s.cs_blocks ++ B)` >> simp[]) >>
  Cases_on `m s` >>
  first_x_assum drule_all >> simp[]
QED

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks` (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem deploy_blocks_frame_return[simp]:
  deploy_blocks_frame (comp_return x)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_return)
QED

Theorem deploy_blocks_frame_bind:
  deploy_blocks_frame m /\ (!x. deploy_blocks_frame (k x)) ==>
  deploy_blocks_frame (comp_bind m k)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_bind)
QED

Theorem deploy_blocks_frame_ignore_bind:
  deploy_blocks_frame m /\ deploy_blocks_frame n ==>
  deploy_blocks_frame (comp_ignore_bind m n)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_ignore_bind)
QED

Theorem deploy_blocks_frame_emit[simp]:
  deploy_blocks_frame (emit i)
Proof
  apply_symbolic_frame symbolic_frame_emit >> simp[]
QED

Theorem deploy_blocks_frame_new_block[simp]:
  deploy_blocks_frame (new_block l)
Proof
  apply_symbolic_frame symbolic_frame_new_block >> simp[]
QED

Theorem deploy_blocks_terminated[simp]:
  block_is_terminated (s with cs_blocks := B) = block_is_terminated s
Proof
  simp[block_is_terminated_def]
QED

Theorem deploy_blocks_frame_fresh_var[simp]:
  deploy_blocks_frame fresh_var
Proof
  apply_symbolic_frame symbolic_frame_fresh_var >> simp[]
QED

Theorem deploy_blocks_frame_fresh_id[simp]:
  deploy_blocks_frame fresh_id
Proof
  apply_symbolic_frame symbolic_frame_fresh_id >> simp[]
QED

Theorem deploy_blocks_frame_fresh_label[simp]:
  deploy_blocks_frame (fresh_label suffix)
Proof
  apply_symbolic_frame symbolic_frame_fresh_label >> simp[]
QED

Theorem deploy_blocks_frame_emit_inst[simp]:
  deploy_blocks_frame (emit_inst opc ops outs)
Proof
  apply_symbolic_frame symbolic_frame_emit_inst >> simp[]
QED

Theorem deploy_blocks_frame_emit_op[simp]:
  deploy_blocks_frame (emit_op opc ops)
Proof
  apply_symbolic_frame symbolic_frame_emit_op >> simp[]
QED

Theorem deploy_blocks_frame_emit_void[simp]:
  deploy_blocks_frame (emit_void opc ops)
Proof
  apply_symbolic_frame symbolic_frame_emit_void >> simp[]
QED

Theorem deploy_blocks_frame_alloc_buffer[simp]:
  deploy_blocks_frame (compile_alloc_buffer n)
Proof
  apply_symbolic_frame symbolic_frame_alloc_buffer >> simp[]
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
  apply_symbolic_frame symbolic_frame_jmp_if_not_terminated >> simp[]
QED
