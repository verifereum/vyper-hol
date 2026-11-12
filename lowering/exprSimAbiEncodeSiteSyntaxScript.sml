(* Compiler-only certificate for the encoder's 32-byte scratch sites. *)
Theory exprSimAbiEncodeSiteSyntax
Ancestors
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousFacts
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge fragExec
  exprLoweringProps compileEnv context emitHelper venomInst list sorting arithmetic

Definition site_step_def:
  site_step a b <=>
    entry_shape a b /\
    a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id /\
    (!k. a.cs_next_id <= k /\ k < b.cs_next_id ==>
      ?i. MEM i (frag_code a b) /\ i.inst_id = k) /\
    (!i. MEM i (frag_code a b) /\ i.inst_opcode = ALLOCA ==>
      ?n. a.cs_next_var <= n /\ n < b.cs_next_var /\
        i.inst_operands = [Lit 32w] /\
        i.inst_outputs = [STRING #"%" (toString n)])
End

Definition site_action_def:
  site_action m <=> !a x b. m a = (x,b) ==> site_step a b
End

Theorem site_step_counters:
  site_step a b ==> a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  simp[site_step_def]
QED

Theorem site_step_coverage:
  site_step a b /\ a.cs_next_id <= k /\ k < b.cs_next_id ==>
  ?i. MEM i (frag_code a b) /\ i.inst_id = k
Proof
  metis_tac[site_step_def]
QED

Theorem site_step_alloca:
  site_step a b /\ MEM i (frag_code a b) /\ i.inst_opcode = ALLOCA ==>
  ?n. a.cs_next_var <= n /\ n < b.cs_next_var /\
    i.inst_operands = [Lit 32w] /\
    i.inst_outputs = [STRING #"%" (toString n)]
Proof
  metis_tac[site_step_def]
QED

Theorem site_step_refl:
  site_step a a
Proof
  simp[site_step_def, entry_shape_refl, frag_code_def,
    emitted_blocks_def, emitted_insts_def]
QED

Theorem site_step_trans:
  site_step a b /\ site_step b c ==> site_step a c
Proof
  strip_tac >>
  `entry_shape a b /\ entry_shape b c` by fs[site_step_def] >>
  drule_all frag_code_compose_perm >> strip_tac >>
  `!i. MEM i (frag_code a c) <=>
    MEM i (frag_code a b) \/ MEM i (frag_code b c)` by
    metis_tac[PERM_MEM_EQ, MEM_APPEND] >>
  fs[site_step_def] >>
  conj_tac >- metis_tac[entry_shape_trans] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `k < b.cs_next_id`
      >- metis_tac[] >>
      `b.cs_next_id <= k` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM i (frag_code a b) \/ MEM i (frag_code b c)` by metis_tac[] >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem site_action_return:
  site_action (comp_return x)
Proof
  simp[site_action_def, comp_return_def, site_step_refl]
QED

Theorem site_action_bind:
  site_action m /\ (!x. site_action (f x)) ==> site_action (comp_bind m f)
Proof
  simp[site_action_def, comp_bind_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> metis_tac[site_step_trans]
QED

Theorem site_action_ignore_bind:
  site_action m /\ site_action n ==> site_action (comp_ignore_bind m n)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >>
  irule site_action_bind >> simp[]
QED

Theorem site_action_fresh_var:
  site_action fresh_var
Proof
  rw[site_action_def, fresh_var_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem site_action_fresh_label:
  !suffix. site_action (fresh_label suffix)
Proof
  rw[site_action_def, fresh_label_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem site_action_new_block:
  !l. site_action (new_block l)
Proof
  rw[site_action_def, new_block_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def] >>
  disj2_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]
QED

Theorem site_action_emit_inst:
  !opc ops outs. opc <> ALLOCA ==> site_action (emit_inst opc ops outs)
Proof
  rw[site_action_def, emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem site_action_emit_void:
  !opc ops. opc <> ALLOCA ==> site_action (emit_void opc ops)
Proof
  simp[emit_void_def, GSYM emit_inst_def, site_action_emit_inst]
QED

Theorem site_action_emit_op:
  !opc ops. opc <> ALLOCA ==> site_action (emit_op opc ops)
Proof
  rw[site_action_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem site_action_alloc_buffer32:
  site_action (compile_alloc_buffer 32)
Proof
  rw[site_action_def, compile_alloc_buffer_def, emit_op_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_id_def, fresh_var_def, emit_def] >>
  simp[site_step_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED
