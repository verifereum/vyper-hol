(* Static ownership of emitted IDs and caller branch destinations. *)
Theory createSizeCutCode
Ancestors
  exprSimAbiDecodeSiteCoverage exprSimAbiGasBridge externalEntryShape
  abiEncoderProps fragExec exprLoweringProps emitHelperProps emitHelper
  compileEnv venomInst venomExecSemantics venomExecProofs venomState list rich_list
  pred_set pair arithmetic ASCIInumbers

(* The selector/condition is not a destination. Other terminators cannot
   return OK, and a returning INVOKE is not a caller branch. *)
Definition create_cut_targets_def:
  create_cut_targets opc ops =
    if opc = JMP then
      (case ops of [Label l] => [l] | _ => [])
    else if opc = JNZ then
      (case ops of [c; Label l; Label r] => [l;r] | _ => [])
    else if opc = DJMP then
      (case ops of c::ls => (case extract_labels ls of
                              SOME labels => labels | NONE => [])
                 | [] => [])
    else []
End

Theorem create_cut_targets_sound:
  is_terminator i.inst_opcode /\ step_inst_base i s = OK t ==>
  MEM t.vs_current_bb (create_cut_targets i.inst_opcode i.inst_operands)
Proof
  strip_tac >> drule_all step_inst_base_ok_terminator_jump >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, create_cut_targets_def, AllCaseEqs(),
      jump_to_def] >> metis_tac[MEM_EL]
QED

Definition create_cut_code_def:
  create_cut_code exits a b <=>
    cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\
    !i. MEM i (frag_code a b) ==>
      i.inst_id IN frag_ids a b /\
      !l. MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
          l IN exits UNION set (added_labels a b)
End

Theorem create_cut_code_jump:
  create_cut_code exits a b /\ MEM i (frag_code a b) /\
  is_terminator i.inst_opcode /\ step_inst_base i s = OK t ==>
  t.vs_current_bb IN exits UNION set (added_labels a b)
Proof
  simp[create_cut_code_def] >> metis_tac[create_cut_targets_sound]
QED

Theorem create_cut_code_join:
  create_cut_code exits a b /\ create_cut_code exits b c ==>
  create_cut_code exits a c
Proof
  rpt strip_tac >> fs[create_cut_code_def] >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  drule_all abi_decode_frag_code_compose >>
  drule_all added_labels_trans >>
  fs[frag_ids_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem create_cut_code_close:
  create_cut_code pending a b /\
  pending SUBSET exits UNION set (added_labels a b) ==>
  create_cut_code exits a b
Proof
  simp[create_cut_code_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem create_cut_code_empty:
  cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\ frag_code a b = [] ==>
  create_cut_code exits a b
Proof
  simp[create_cut_code_def]
QED

Theorem create_cut_code_refl[simp]:
  create_cut_code exits a a
Proof
  irule create_cut_code_empty >>
  simp[cs_extends_refl, frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem create_cut_code_return[simp]:
  create_cut_code exits a (SND (comp_return x a))
Proof
  simp[comp_return_def]
QED

Theorem create_cut_code_get[simp]:
  create_cut_code exits a (SND (comp_get a))
Proof
  simp[comp_get_def]
QED

Theorem create_cut_code_bind:
  create_cut_code exits a (SND (m a)) /\
  create_cut_code exits (SND (m a)) (SND (k (FST (m a)) (SND (m a)))) ==>
  create_cut_code exits a (SND (comp_bind m k a))
Proof
  Cases_on `m a` >> simp[comp_bind_def] >>
  metis_tac[create_cut_code_join]
QED

Theorem create_cut_code_ignore_bind:
  create_cut_code exits a (SND (m a)) /\
  create_cut_code exits (SND (m a)) (SND (k (SND (m a)))) ==>
  create_cut_code exits a (SND (comp_ignore_bind m k a))
Proof
  Cases_on `m a` >> simp[comp_ignore_bind_def, comp_bind_def] >>
  metis_tac[create_cut_code_join]
QED

Theorem create_cut_code_new_block[simp]:
  create_cut_code exits a (SND (new_block l a))
Proof
  `cs_extends a (SND (new_block l a))` by
    (Cases_on `new_block l a` >> simp[] >> metis_tac[cs_extends_new_block]) >>
  irule create_cut_code_empty >>
  simp[new_block_def, frag_code_def, emitted_blocks_def, LENGTH_DROP]
QED

Theorem create_cut_code_fresh_label[simp]:
  create_cut_code exits a (SND (fresh_label suffix a))
Proof
  irule create_cut_code_empty >>
  simp[fresh_label_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       cs_extends_same_block]
QED

Theorem create_cut_code_fresh_var[simp]:
  create_cut_code exits a (SND (fresh_var a))
Proof
  irule create_cut_code_empty >>
  simp[fresh_var_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       cs_extends_same_block]
QED

Theorem create_cut_code_single[local]:
  cs_extends a b /\ b.cs_next_id = SUC a.cs_next_id /\
  b.cs_blocks = a.cs_blocks /\
  emitted_insts a b = [mk_inst a.cs_next_id opc ops outs] /\
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a b
Proof
  simp[create_cut_code_def, frag_code_def, emitted_blocks_def, frag_ids_def,
       mk_inst_def]
QED

Theorem create_cut_code_emit_inst:
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a (SND (emit_inst opc ops outs a))
Proof
  Cases_on `emit_inst opc ops outs a` >> rpt strip_tac >>
  Cases_on `q` >> gvs[] >> drule emitted_insts_emit_inst >> strip_tac >>
  irule create_cut_code_single >> simp[ADD1] >> metis_tac[cs_extends_emit_inst]
QED

Theorem create_cut_code_emit_op:
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a (SND (emit_op opc ops a))
Proof
  Cases_on `emit_op opc ops a` >> rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  irule create_cut_code_single >> simp[ADD1, cs_extends_same_block] >>
  metis_tac[]
QED

Theorem create_cut_code_emit_void:
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a (SND (emit_void opc ops a))
Proof
  simp[emit_void_def, emit_inst_def] >> metis_tac[REWRITE_RULE [emit_inst_def]
      create_cut_code_emit_inst]
QED

Theorem create_cut_code_fresh_vars[simp]:
  !n a. create_cut_code exits a (SND (fresh_vars n a))
Proof
  Induct >> simp[fresh_vars_def] >> rpt gen_tac >>
  irule create_cut_code_bind >> simp[] >>
  irule create_cut_code_bind >> simp[]
QED

Theorem create_cut_code_emit_multi_op:
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a (SND (emit_multi_op opc ops n a))
Proof
  strip_tac >> simp[emit_multi_op_def] >> irule create_cut_code_bind >> simp[] >>
  irule create_cut_code_ignore_bind >> simp[create_cut_code_emit_inst]
QED
