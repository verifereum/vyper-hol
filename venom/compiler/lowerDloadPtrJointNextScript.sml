(* Actual singleton boundary advancement, independent of instruction semantics. *)
Theory lowerDloadPtrJointNext
Ancestors
  lowerDloadPtrJointEntry lowerDloadPtrOrdinary lowerDloadPtrScalar lowerDloadPtrRel
  lowerDloadPtrAggregate lowerDloadPtrCall ptrDiscipline
  o1ContractLowerDload lowerDloadDefs venomExecSemantics venomInst
  contextCodegenRel venomExecProofs list rich_list

Theorem dload_insts_supply_at_prefix[local]:
  !xs n q ys q' ps u.
    lower_dload_insts_supply q xs = (ys,q') /\
    n <= LENGTH xs /\
    lower_dload_insts_supply q (TAKE n xs) = (ps,u) /\
    LENGTH ps < LENGTH ys ==>
    n < LENGTH xs /\
    ?emitted after. lower_dload_inst_supply u (EL n xs) = (emitted,after) /\
      emitted <> [] /\ HD emitted = EL (LENGTH ps) ys
Proof
  Induct >- simp[lower_dload_insts_supply_def] >>
  Cases_on `n` >> rpt gen_tac
  >- (simp[lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
      `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
      Cases_on `out` >> gvs[]) >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  simp[EL_APPEND_EQN]
QED

Theorem dload_blocks_supply_el:
  !bs n q cs q'. lower_dload_blocks_supply q bs = (cs,q') /\ n < LENGTH bs ==>
  ?u. n < LENGTH cs /\ lower_dload_block_supply
    (SND (lower_dload_blocks_supply q (TAKE n bs))) (EL n bs) = (EL n cs,u)
Proof
  Induct >- simp[] >> Cases_on `n` >> rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> strip_tac
  >- gvs[lower_dload_blocks_supply_def] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  Cases_on `lower_dload_blocks_supply s1 (TAKE n' bs)` >> gvs[]
QED

Theorem dload_insts_supply_prefix_emission:
  !xs n q ps u i emitted after.
    n < LENGTH xs /\ i = EL n xs /\
    lower_dload_insts_supply q (TAKE n xs) = (ps,u) /\
    lower_dload_inst_supply u i = (emitted,after) ==>
    lower_dload_insts_supply q (TAKE (SUC n) xs) = (ps ++ emitted,after)
Proof
  Induct >- simp[] >> Cases_on `n` >> rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac
  >- gvs[lower_dload_insts_supply_def] >>
  gvs[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def, APPEND_ASSOC]
QED

Theorem dload_insts_supply_prefix_suc[local]:
  !xs n q ps u i after.
    n < LENGTH xs /\ i = EL n xs /\
    lower_dload_insts_supply q (TAKE n xs) = (ps,u) /\
    lower_dload_inst_supply u i = ([i],after) ==>
    lower_dload_insts_supply q (TAKE (SUC n) xs) = (ps ++ [i],after)
Proof
  metis_tac[dload_insts_supply_prefix_emission]
QED

Theorem dload_active_at_block[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\ MEM bb g.fn_blocks /\
  bb.bb_label = t.vs_current_bb /\ active_inst g j t ==>
  t.vs_inst_idx < LENGTH bb.bb_instructions /\ j = EL t.vs_inst_idx bb.bb_instructions
Proof
  simp[active_inst_def] >> strip_tac >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  gvs[]
QED

Theorem dload_control_emission_next_fields:
  !q f g s t i xs s1 tN j.
    dload_control_match q f g s t i xs 0 /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\
    tN.vs_current_bb = t.vs_current_bb /\ tN.vs_prev_bb = t.vs_prev_bb /\
    tN.vs_inst_idx = t.vs_inst_idx + LENGTH xs /\
    active_inst g j tN ==>
    ?i' emitted'.
      dload_control_match q f g
        (s1 with vs_inst_idx := SUC s.vs_inst_idx) tN i' emitted' 0 /\
      j = HD emitted'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_control_match_def] >> strip_tac >>
  `?aq. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,aq)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_supply_el >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply bs _ = (gb,_)` >>
  `gb.bb_label = (EL bi f.fn_blocks).bb_label /\
   ?aq. lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
      (gb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `tN.vs_inst_idx < LENGTH gb.bb_instructions /\
   j = EL tN.vs_inst_idx gb.bb_instructions` by
    (drule dload_active_at_block >>
     disch_then (qspecl_then [`tN`,`j`,`gb`] mp_tac) >>
     simp[Abbr `gb`, EL_MEM]) >>
  `lower_dload_insts_supply bs (TAKE (SUC s.vs_inst_idx)
       (EL bi f.fn_blocks).bb_instructions) = (before ++ xs,after)` by
    (irule dload_insts_supply_prefix_emission >> simp[] >> metis_tac[]) >>
  `SUC s.vs_inst_idx <= LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  `LENGTH (before ++ xs) < LENGTH gb.bb_instructions` by simp[] >>
  qpat_x_assum `lower_dload_insts_supply _ (TAKE s.vs_inst_idx _) = _` kall_tac >>
  drule_all dload_insts_supply_at_prefix >> strip_tac >>
  `j = HD emitted` by gvs[] >>
  `0 < LENGTH emitted` by (Cases_on `emitted` >> gvs[]) >>
  qexistsl [`EL (SUC s.vs_inst_idx) (EL bi f.fn_blocks).bb_instructions`,`emitted`] >>
  simp[] >> qexistsl [`bi`,`before ++ xs`,`after`,`after'`] >>
  simp[Abbr `bs`] >>
  simp[active_inst_def] >> conj_tac
  >- (qexists_tac `EL bi f.fn_blocks` >> simp[EL_MEM]) >>
  qexists_tac `gb` >> simp[EL_MEM, Abbr `gb`]
QED

Theorem dload_control_singleton_next_fields:
  !q f g s t i s1 t1 j.
    dload_control_match q f g s t i [i] 0 /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\
    t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    t1.vs_inst_idx = t.vs_inst_idx /\
    active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
    ?i' emitted'.
      dload_control_match q f g
        (s1 with vs_inst_idx := SUC s.vs_inst_idx)
        (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
      j = HD emitted'
Proof
  rpt gen_tac >> strip_tac >>
  irule dload_control_emission_next_fields >>
  simp[] >> qexistsl [`i`,`t`,`[i]`] >> simp[arithmeticTheory.ADD1]
QED

Theorem dload_control_singleton_next:
  !q f g s t i s1 t1 j.
    dload_control_match q f g s t i [i] 0 /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
    s1 = s with vs_vars := s1.vs_vars /\
    t1 = t with vs_vars := t1.vs_vars /\
    active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
    ?i' emitted'.
      dload_control_match q f g
        (s1 with vs_inst_idx := SUC s.vs_inst_idx)
        (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
      j = HD emitted'
Proof
  rpt gen_tac >> strip_tac >>
  irule dload_control_singleton_next_fields >>
  simp[] >> gvs[venomStateTheory.venom_state_component_equality] >>
  metis_tac[]
QED

Theorem dload_actual_assign_next:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g i t /\
  dload_control_match q f g s t i [i] 0 /\ i.inst_opcode = ASSIGN /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN {v | ?ci. MEM ci (fn_insts f) /\
           (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)} ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    (!v. v IN {v | ?ci. MEM ci (fn_insts f) /\
           (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)} ==>
       (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
        lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >> simp[dload_equal_environment_def, venomStateTheory.venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
      v IN {v | ?ci. MEM ci (fn_insts f) /\
         (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)}` by
    (simp[] >> metis_tac[]) >>
  drule_all dload_boundary_core_assign_index >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  drule_all dload_control_singleton_next >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_next >> simp[is_terminator_def] >>
  `active_inst f i' (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
  simp[dload_control_match_def] >> metis_tac[]
QED

(* Constructor audit: dload_actual_assign_next is the ASSIGN boundary branch
   of the intended induction on target frame_reachable.  Entry is supplied by
   dload_actual_joint_entry.  This branch derives source success, successor
   activity and reachability; none is assumed at the successor.  Allocation
   frames fs, saved callers cs/ds, and Ws are retained unchanged.  Separate
   saved-layout, supply, live-function-index and runtime scratch certificates
   remain predecessor obligations: variable-only execution and index advance
   do not produce them.  Other opcodes, expansion prefixes, block transfers,
   calls, returns and forwarding remain open; this is not a full simulation. *)

Theorem dload_singleton_reachable_next_fields:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s1 /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?i' emitted'.
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted'
Proof
  strip_tac >>
  drule_all dload_control_singleton_next_fields >> strip_tac >>
  qexistsl [`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_next >> simp[] >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
  simp[dload_control_match_def] >> metis_tac[]
QED

Theorem dload_singleton_reachable_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s1 /\
  s1 = s with vs_vars := s1.vs_vars /\
  t1 = t with vs_vars := t1.vs_vars /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?i' emitted'.
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted'
Proof
  strip_tac >> irule dload_singleton_reachable_next_fields >>
  simp[] >> gvs[venomStateTheory.venom_state_component_equality] >>
  metis_tac[]
QED

Theorem dload_actual_scalar_next:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g i t /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> ~retpc_var f v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN {v | ?ci. MEM ci (fn_insts f) /\
           (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)} ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    (!v. v IN {v | ?ci. MEM ci (fn_insts f) /\
           (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)} ==>
       (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
        lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venomStateTheory.venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
      v IN {v | ~retpc_var f v} /\
      v IN {v | ?ci. MEM ci (fn_insts f) /\
         (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)}` by
    (simp[] >> metis_tac[]) >>
  drule_all dload_boundary_core_scalar_index >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[]
QED

(* Scalar audit: safety, provenance support and operand tracking are explicit
   predecessor premises, not yet producers from the final induction.  Source
   success and successor control/reachability are conclusions.  Saved layouts,
   runtime scratch-domain identity and live-index coupling remain external;
   this ordinary family does not establish allocation or call/return closure. *)
