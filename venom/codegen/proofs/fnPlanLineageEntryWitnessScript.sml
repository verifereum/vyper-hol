Theory fnPlanLineageEntryWitness
Ancestors
  venomExecProofs venomWf list relation
  simplifyCfgPhiRepair removeUnusedSsaProofs

Theorem is_fn_path_first_entry:
  !path lbl.
  is_fn_path fn path /\ MEM lbl path /\ HD path <> lbl ==>
  ?pre. is_fn_path fn pre /\ pre <> [] /\ HD pre = HD path /\
    ~MEM lbl pre /\ fn_cfg_edge fn (LAST pre) lbl
Proof
  Induct >- simp[] >> rpt gen_tac >>
  namedCases_on `path` ["", "next rest"]
  >- (strip_tac >> gvs[]) >>
  simp[is_fn_path_def] >> disch_tac >>
  Cases_on `next = lbl`
  >- (qexists_tac `[h]` >> gvs[is_fn_path_def]) >>
  gvs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `h::pre` >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem fn_reachable_first_entry_predecessor:
  fn_reachable fn lbl /\ fn_entry_label fn = SOME entry /\ lbl <> entry ==>
  ?p. fn_cfg_edge fn p lbl /\ fn_reachable fn p /\ ~fn_dominates fn lbl p
Proof
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM lbl path` by
    (Cases_on `path` >- gvs[] >> metis_tac[rich_listTheory.MEM_LAST]) >>
  `HD path <> lbl` by gvs[] >>
  drule_all is_fn_path_first_entry >> strip_tac >>
  qexists_tac `LAST pre` >> simp[] >>
  conj_tac
  >- (drule_all is_fn_path_rtc >> gvs[]) >>
  simp[fn_dominates_def] >> disj2_tac >>
  qexists_tac `pre` >> gvs[]
QED

Theorem def_available_non_dominating_no_kill:
  ssa_form fn /\ MEM bb fn.fn_blocks /\
  ~fn_dominates fn bb.bb_label pb.bb_label /\
  def_available_at fn pb use_pos v ==>
  EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  gvs[def_available_at_def] >>
  `ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP (\i. i.inst_outputs) b.bb_instructions))
     fn.fn_blocks))` by
    (gvs[ssa_form_def, venomInstTheory.fn_insts_def, fn_insts_blocks_flat,
         MAP_FLAT, rich_listTheory.FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`bb`, `def_bb`, `v`] mp_tac) >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
