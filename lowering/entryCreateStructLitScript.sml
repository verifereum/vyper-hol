(* The selected phases of an installed StructLit expression. *)
Theory entryCreateStructLit
Ancestors
  entryCreateAdminSequence entryCreateCompositeFocus entryCreateFocusSpec
  bodyFullStructLit abiBuiltinAllocation createSizePrefixReplay
  emitHelperProps exprLoweringProps fragExec compileEnv venomInst venomState
  venomExecSemantics arithmetic

Theorem structlit_emit_site[local]:
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb f /\
  ~MEM opc [INVOKE; GAS; CREATE; CREATE2] /\ ~is_terminator opc /\
  create_operand_at sa s /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id opc args
    [STRING #"%" (toString sa.cs_next_var)]) s = OK raw ==>
  create_operand_full_scope sa sb E C f s []
    (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  create_operand_cut sa sb E C f tops cx st0 source (es,s)
Proof
  simp[] >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule loweringShapeRulesTheory.emit_op_facts >> simp[]) >>
  conj_tac >- (irule create_admin_sequence_scope >>
    fs[abiEncoderPropsTheory.frag_ids_def, mk_inst_def, run_inst_seq_def]) >>
  irule create_admin_sequence_cut >> simp[mk_inst_def]
QED

(* The base interpreter and the joint pointer witness use the same raw
   allocation endpoint; only the instruction index is advanced here. *)
Theorem structlit_alloc_site:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sm) s = OK raw /\
  t = raw with vs_inst_idx := LENGTH sm.cs_current_insts ==>
  create_operand_full_scope sa sm E ctx func s [] (OK t) /\
  create_operand_cut sa sm E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> irule structlit_emit_site >>
  simp[] >> qexistsl_tac [`[Lit (n2w n)]`, `buf.buf_operand`, `ALLOCA`] >>
  fs[is_terminator_def, run_inst_seq_def, AllCaseEqs()]
QED

(* ADD is after the child's VV exit and before unwrap. The concrete base
   endpoint is the update chosen in structlit_child_add_full. *)
Theorem structlit_add_site:
  emit_op ADD [Var root; Lit (n2w off)] sa = (Var dst,sb) /\
  fn_has_code sa sb f /\ create_operand_at sa s /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\
  t = (update_var dst (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  create_operand_full_scope sa sb E C f s [] (OK t) /\
  create_operand_cut sa sb E C f tops cx st0 source (es,s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    fs[create_operand_at_def] >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  qpat_x_assum `SUC _ = _` SUBST1_TAC >>
  irule structlit_emit_site >> simp[] >>
  qexistsl_tac [`[Var root; Lit (n2w off)]`, `Var dst`, `ADD`] >>
  fs[is_terminator_def, mk_inst_def, step_inst_base_opcode_eqs,
     exec_pure2_def, eval_operand_def]
QED
