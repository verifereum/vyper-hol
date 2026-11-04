(* Actual singleton boundary advancement, independent of instruction semantics. *)
Theory lowerDloadPtrJointNext
Ancestors
  lowerDloadPtrJointEntry lowerDloadPtrOrdinary lowerDloadPtrRel
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

Theorem dload_blocks_supply_el[local]:
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

Theorem dload_insts_supply_prefix_suc[local]:
  !xs n q ps u i after.
    n < LENGTH xs /\ i = EL n xs /\
    lower_dload_insts_supply q (TAKE n xs) = (ps,u) /\
    lower_dload_inst_supply u i = ([i],after) ==>
    lower_dload_insts_supply q (TAKE (SUC n) xs) = (ps ++ [i],after)
Proof
  Induct >- simp[] >> Cases_on `n` >> rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac
  >- gvs[lower_dload_insts_supply_def] >>
  gvs[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def, APPEND_ASSOC]
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
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
   t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb` by
    (gvs[venomStateTheory.venom_state_component_equality]) >>
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
  `SUC t.vs_inst_idx < LENGTH gb.bb_instructions /\
   j = EL (SUC t.vs_inst_idx) gb.bb_instructions` by
    (drule dload_active_at_block >>
     disch_then (qspecl_then [`t1 with vs_inst_idx := SUC t.vs_inst_idx`,`j`,`gb`] mp_tac) >>
     simp[Abbr `gb`, EL_MEM]) >>
  `lower_dload_insts_supply bs (TAKE (SUC s.vs_inst_idx)
       (EL bi f.fn_blocks).bb_instructions) = (before ++ [i],after)` by
    (irule dload_insts_supply_prefix_suc >> simp[] >> metis_tac[]) >>
  `SUC s.vs_inst_idx <= LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  `LENGTH (before ++ [i]) < LENGTH gb.bb_instructions` by simp[] >>
  qpat_x_assum `lower_dload_insts_supply _ (TAKE s.vs_inst_idx _) = _` kall_tac >>
  drule_all dload_insts_supply_at_prefix >> strip_tac >>
  `j = HD emitted` by gvs[arithmeticTheory.ADD1] >>
  `0 < LENGTH emitted` by (Cases_on `emitted` >> gvs[]) >>
  qexistsl [`EL (SUC s.vs_inst_idx) (EL bi f.fn_blocks).bb_instructions`,`emitted`] >>
  simp[] >> qexistsl [`bi`,`before ++ [i]`,`after`,`after'`] >>
  simp[Abbr `bs`, arithmeticTheory.ADD1] >>
  simp[active_inst_def] >> conj_tac
  >- (qexists_tac `EL bi f.fn_blocks` >> simp[EL_MEM, GSYM arithmeticTheory.ADD1]) >>
  qexists_tac `gb` >> simp[EL_MEM, Abbr `gb`, GSYM arithmeticTheory.ADD1]
QED
