Theory lowerDloadConfiguredSelection
Ancestors
  lowerDloadControlPosition lowerDloadDefs venomInst list

Theorem lower_dload_blocks_supply_selected_prefix:
  !bs a gs b lbl gb.
    lower_dload_blocks_supply a bs = (gs,b) /\
    lookup_block lbl gs = SOME gb ==>
    ?pre bb post gp gt a0 a1.
      bs = pre ++ bb::post /\ gs = gp ++ gb::gt /\
      lower_dload_blocks_supply a pre = (gp,a0) /\
      lower_dload_block_supply a0 bb = (gb,a1) /\
      lower_dload_blocks_supply a1 post = (gt,b) /\
      bb.bb_label = lbl /\
      EVERY (\x. x.bb_label <> lbl) pre /\
      EVERY (\x. x.bb_label <> lbl) gp /\
      lookup_block lbl bs = SOME bb
Proof
  Induct >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def] >> strip_tac >> gvs[] >>
  `q.bb_label = h.bb_label` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, FIND_thm] >>
      qexistsl_tac [`[]`, `bs`, `[]`, `q'`, `a`, `r`] >>
      simp[lower_dload_blocks_supply_def]) >>
  gvs[lookup_block_def, FIND_thm] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`h::pre`, `bb`, `post`, `q::gp`, `gt`, `a0`, `a1`] >>
  simp[lower_dload_blocks_supply_def]
QED
