Theory exprSimAbiEncodeNoBlockSafety
Ancestors
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext exprLoweringProps compileEnv
  emitHelperProps context list rich_list sorting venomInst fragExec exprSimAbiGasBridge

Definition enc_straight_action_def:
  enc_straight_action m <=>
    !a x b. m a = (x,b) ==>
      entry_shape a b /\
      (b.cs_blocks = a.cs_blocks ==>
        EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
          (frag_code a b))
End

Theorem enc_entry_blocks_length[local]:
  entry_shape a b ==> LENGTH a.cs_blocks <= LENGTH b.cs_blocks
Proof
  rw[entry_shape_def] >> simp[]
QED

Theorem enc_entry_equal_length[local]:
  entry_shape a b /\ LENGTH a.cs_blocks = LENGTH b.cs_blocks ==>
  b.cs_blocks = a.cs_blocks
Proof
  rw[entry_shape_def] >> gvs[]
QED

Theorem enc_straight_action_return:
  enc_straight_action (comp_return x)
Proof
  simp[enc_straight_action_def, comp_return_def, entry_shape_refl,
       frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem enc_straight_action_bind:
  enc_straight_action m /\ (!x. enc_straight_action (f x)) ==>
  enc_straight_action (comp_bind m f)
Proof
  rw[enc_straight_action_def, comp_bind_def] >>
  Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- metis_tac[entry_shape_trans] >>
  `LENGTH a.cs_blocks <= LENGTH r.cs_blocks /\
   LENGTH r.cs_blocks <= LENGTH b.cs_blocks` by
    metis_tac[enc_entry_blocks_length] >>
  `r.cs_blocks = a.cs_blocks /\ b.cs_blocks = r.cs_blocks` by
    (conj_tac >> irule enc_entry_equal_length >> simp[] >> gvs[] >> decide_tac) >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >> simp[]
QED

Theorem enc_straight_action_ignore_bind:
  enc_straight_action m /\ enc_straight_action n ==>
  enc_straight_action (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, enc_straight_action_bind]
QED

Theorem enc_straight_action_code:
  code_action (\opc. opc <> INVOKE /\ ~is_terminator opc) m ==>
  enc_straight_action m
Proof
  rw[code_action_def, code_step_def, enc_straight_action_def] >> metis_tac[]
QED

Theorem enc_straight_action_fresh_var:
  enc_straight_action fresh_var
Proof
  irule enc_straight_action_code >> simp[code_action_fresh_var]
QED

Theorem enc_straight_action_fresh_label:
  enc_straight_action (fresh_label suffix)
Proof
  irule enc_straight_action_code >> simp[code_action_fresh_label]
QED

Theorem enc_straight_action_emit_inst:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_inst opc ops outs)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_inst]
QED

Theorem enc_straight_action_emit_op:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_op opc ops)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_op]
QED

Theorem enc_straight_action_emit_void:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_void opc ops)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_void]
QED

Theorem enc_straight_action_alloc_buffer:
  enc_straight_action (compile_alloc_buffer sz)
Proof
  irule enc_straight_action_code >> simp[code_action_alloc_buffer, is_terminator_def]
QED

Theorem enc_straight_action_new_block:
  enc_straight_action (new_block l)
Proof
  irule enc_straight_action_code >> simp[code_action_new_block]
QED
