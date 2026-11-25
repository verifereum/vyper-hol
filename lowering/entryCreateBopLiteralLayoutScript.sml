(* Layout and confined execution certificates for literal membership suffixes. *)
Theory entryCreateBopLiteralLayout
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  createSizeBuiltinBodyCode bodyPtrBopInLiteralRun
  exprLoweringProps compileEnv venomInst venomState list rich_list

Theorem literal_member_suffix_inventory[local]:
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  create_cut_code {} sm sb /\
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO])
    (emitted_insts sm sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  create_cut_code {} sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\
             MEM i.inst_opcode [EQ; OR; AND; ISZERO])
    (emitted_insts sm sb)
Proof
  strip_tac >> fs[same_blocks_def] >>
  `frag_code sm sb = emitted_insts sm sb` by
    fs[exprSimAbiGasBridgeTheory.frag_code_def, fragExecTheory.emitted_blocks_def] >>
  fs[createSizeCutCodeTheory.create_cut_code_def, EVERY_MEM] >> metis_tac[]
QED

Theorem literal_member_suffix_layout:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  create_cut_code {} sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\
             MEM i.inst_opcode [EQ; OR; AND; ISZERO])
    (emitted_insts sm sb)
Proof
  strip_tac >> irule literal_member_suffix_inventory >> gvs[]
  >- (drule literal_in_code >> strip_tac >>
      mp_tac (Q.INST [`exits` |-> `{}`, `a` |-> `sm`]
        (cj 1 builtin_list_membership_code)) >> fs[])
  >- (drule literal_notin_code >> strip_tac >>
      mp_tac (Q.INST [`exits` |-> `{}`, `a` |-> `sm`]
        (cj 2 builtin_list_membership_code)) >> fs[])
QED

Theorem literal_member_suffix_scope:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  fn_has_code sm sb func /\ create_operand_at sm s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sm sb) s = OK u ==>
  create_operand_full_scope sm sb E C func s []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_member_suffix_layout >> strip_tac >>
  irule create_admin_sequence_scope >> fs[EVERY_MEM] >>
  rpt strip_tac >> res_tac >> gvs[is_terminator_def]
QED

Theorem literal_member_suffix_cut:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  fn_has_code sm sb func /\ create_operand_at sm s ==>
  create_operand_cut sm sb E C func tops cx st0 source (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_member_suffix_layout >> strip_tac >>
  irule create_admin_sequence_cut >> fs[EVERY_MEM] >>
  rpt strip_tac >> res_tac >> gvs[is_terminator_def]
QED
