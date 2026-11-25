(* The caller scope of an installed straight-line administrative slice. *)
Theory entryCreateAdminSequence
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreateStmtCases
  entryCreateCompletedCut createSizePrefixReplay createMarkedPath
  fragExec fragGasSeq fragGasSeqAbort fragGasOrigin exprLoweringProps instIdxIndep
  venomExecSemantics venomInstProps venomState venomInst
  list rich_list relation arithmetic

Theorem admin_sequence_edge[local]:
  ~s.vs_halted /\ ~create_operand_at sb s /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids sa sb /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK v ==>
  create_expr_prefix sa sb E C f s [] (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `gas_path_edge C f s 0 (OK (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all tuple_straight_line_edge >> simp[]) >>
  drule gas_path_edge_zero_origin >> strip_tac >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  fs[create_marked_edge_def, create_prefix_step_def, create_operand_at_def] >>
  metis_tac[]
QED

(* The base interpreter retains its PC at each step; the confined native
   path instead advances at every fetch, so reindex the recursive run. The
   enclosing exit is excluded at each source PC, not at the endpoint. *)
Theorem create_admin_sequence_prefix_run:
  !is s u bb.
    ~s.vs_halted /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
    (!j. j < LENGTH is ==>
         (s.vs_current_bb,s.vs_inst_idx+j) <>
         (sb.cs_current_bb,LENGTH sb.cs_current_insts)) /\
    EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) is /\
    run_inst_seq is s = OK u ==>
    create_expr_prefix sa sb E C f s []
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH is) /\
    u.vs_current_bb = s.vs_current_bb
Proof
  Induct_on `is`
  >- (simp[run_inst_seq_def] >> simp[venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK v` >>
  `~create_operand_at sb s` by
    (simp_tac bool_ss [create_operand_at_def, DE_MORGAN_THM, GSYM IMP_DISJ_THM] >>
     qpat_assum `!j. j < SUC _ ==> _` (qspec_then `0`
       (ACCEPT_TAC o SIMP_RULE bool_ss [ADD_CLAUSES, DECIDE ``!n:num. 0 < SUC n``]))) >>
  drule_all admin_sequence_edge >> strip_tac >>
  `step_inst 0 C h s = OK v` by simp[step_inst_non_invoke] >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_preserves_halted] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq is t = OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `t`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `!s u bb. _` (qspecl_then
    [`t`,`u with vs_inst_idx := SUC s.vs_inst_idx`,`bb`] mp_tac) >>
  impl_tac
  >- (simp[Abbr `t`] >> rpt strip_tac >>
      qpat_assum `!j. j < SUC _ ==> _`
        (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >>
      simp[ADD_CLAUSES]) >>
  strip_tac >> fs[Abbr `t`, ADD_CLAUSES] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_expr_prefix_append)) >>
  qexists_tac `v with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Theorem create_admin_sequence_scope:
  fn_has_code sa sb f /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  create_operand_full_scope sa sb E C f s []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND, create_operand_at_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    fs[create_operand_at_def] >>
  `!j. j < LENGTH (emitted_insts sa sb) ==>
       (s.vs_current_bb,s.vs_inst_idx+j) <> (sb.cs_current_bb,LENGTH sb.cs_current_insts)` by
    (qpat_assum `_ + _ = LENGTH sb.cs_current_insts` (SUBST1_TAC o SYM) >>
     simp[] >> decide_tac) >>
  drule_all create_admin_sequence_prefix_run >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED

(* Any completed edge from this fetch advances one slot, independently
   of the existence of a successful run of the rest of the slice. *)
Theorem admin_sequence_step_pc[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ create_prefix_step sa sb E C f s ms t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  simp[create_prefix_step_def, gas_origin_edge_def, exit_result_def] >>
  strip_tac >> gvs[]
  >- (drule_all step_preserves_control_flow >> simp[]) >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
  gvs[exit_result_def]
QED

Definition admin_sequence_cursor_def:
  admin_sequence_cursor sa sb v <=>
    v.vs_current_bb = sa.cs_current_bb /\
    LENGTH sa.cs_current_insts <= v.vs_inst_idx /\
    v.vs_inst_idx <= LENGTH sb.cs_current_insts
End

Theorem admin_sequence_visit_inventory[local]:
  fn_has_code sa sb f /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ is /\
  EVERY (\i. ~is_terminator i.inst_opcode) is /\
  create_operand_at sa s /\ create_expr_prefix sa sb E C f s ms u /\
  create_operand_fetch sa sb f u i ==>
  MEM i is
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH sb.cs_current_insts = LENGTH is + LENGTH sa.cs_current_insts` by
    simp[ADD_COMM] >>
  `!v. v.vs_current_bb = sa.cs_current_bb /\
       LENGTH sa.cs_current_insts <= v.vs_inst_idx /\
       v.vs_inst_idx < LENGTH sb.cs_current_insts ==>
       ?j. j < LENGTH is /\
         get_instruction bb v.vs_inst_idx = SOME (EL j is)` by
    (rpt strip_tac >> qabbrev_tac `j = v.vs_inst_idx - LENGTH sa.cs_current_insts` >>
     `LENGTH sa.cs_current_insts + j = v.vs_inst_idx /\ j < LENGTH is` by
       (gvs[Abbr `j`] >> decide_tac) >>
     qexists_tac `j` >>
     qpat_assum `!k. _ ==> get_instruction bb _ = _` (qspec_then `j` assume_tac) >>
     metis_tac[]) >>
  `admin_sequence_cursor sa sb s` by fs[admin_sequence_cursor_def, create_operand_at_def] >>
  `admin_sequence_cursor sa sb u` by
    (irule RTC_lifts_invariants >>
     qexists_tac `\p q. ?chunk. create_prefix_step sa sb E C f p chunk q` >>
     qexists_tac `s` >> simp[] >> reverse conj_tac
     >- (drule create_expr_prefix_rtc_project >> disch_then irule >> metis_tac[]) >>
     simp[admin_sequence_cursor_def, PULL_EXISTS] >> rpt strip_tac >>
     rename1 `create_prefix_step sa sb E C f p chunk q` >>
     `~create_operand_at sb p` by fs[create_prefix_step_def, create_operand_at_def] >>
     `p.vs_inst_idx < LENGTH sb.cs_current_insts` by (gvs[create_operand_at_def] >> decide_tac) >>
     qpat_assum `!v. _ ==> ?j. _` (qspec_then `p` drule_all) >> strip_tac >>
     `~is_terminator (EL j is).inst_opcode` by fs[EVERY_EL] >>
     `lookup_block p.vs_current_bb f.fn_blocks = SOME bb` by simp[] >>
     drule_all admin_sequence_step_pc >> simp[] >> decide_tac) >>
  `u.vs_inst_idx < LENGTH sb.cs_current_insts` by
    (gvs[admin_sequence_cursor_def, create_operand_fetch_def, create_operand_at_def] >> decide_tac) >>
  fs[admin_sequence_cursor_def] >>
  qpat_assum `!v. _ ==> ?j. _` (qspec_then `u` drule_all) >> strip_tac >>
  gvs[create_operand_fetch_def] >> irule EL_MEM >> simp[]
QED

Theorem create_admin_sequence_cut:
  fn_has_code sa sb f /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb) /\ create_operand_at sa s ==>
  create_operand_cut sa sb E C f tops cx st0 source (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule create_interior_visit_cases >> strip_tac
  >- (drule_all admin_sequence_visit_inventory >> strip_tac >>
      gvs[] >> irule create_cut_noncreate_visit >> fs[EVERY_MEM]) >>
  drule_all admin_sequence_visit_inventory >> strip_tac >> gvs[EVERY_MEM]
QED
