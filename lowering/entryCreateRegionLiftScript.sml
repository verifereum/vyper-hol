(* Left-to-outer embeddings only need separation on the visited left region. *)
Theory entryCreateRegionLift
Ancestors
  entryCreateFocusSpec entryCreatePathScope
  entryCreateOperandReplay entryCreateCompletedCut createSizeCutRegion
  createSizePrefixReplay createMarkedPath abiEncoderProps fragExec
  bodySim createSizeCutCode relation pair list arithmetic

Theorem marked_rtc_lift_on_region[local]:
  (!u ms v. Inv u /\ E u ms v ==> Inv v /\ A u ms v) ==>
  !x y. RTC (create_marked_edge E) x y ==> Inv (FST x) ==>
        Inv (FST y) /\ RTC (create_marked_edge A) x y
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  simp[FORALL_PROD, create_marked_edge_def, PULL_EXISTS] >>
  metis_tac[RTC_RULES_RIGHT1, create_marked_edge_def]
QED

Theorem create_left_prefix_lift_at:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\ create_cut_region a m s /\
  m.cs_next_id <= b.cs_next_id /\
  (!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u) /\
  create_expr_prefix a m explicit ctx fn s ms t ==>
  create_expr_prefix a b explicit ctx fn s ms t
Proof
  simp[create_expr_prefix_marked, create_operand_at_def] >> strip_tac >>
  `!u marks v. create_cut_region a m u /\ create_prefix_step a m explicit ctx fn u marks v ==>
    create_cut_region a m v /\ create_prefix_step a b explicit ctx fn u marks v` by
    (rpt gen_tac >> simp[create_prefix_step_def] >> strip_tac >>
     conj_tac
     >- metis_tac[operand_cut_region_edge] >>
     rename1 `get_instruction bb u.vs_inst_idx = SOME i` >>
     `i.inst_id IN frag_ids a b` by fs[frag_ids_def] >>
     metis_tac[]) >>
  drule marked_rtc_lift_on_region >> disch_then drule >> simp[]
QED

Theorem create_left_terminal_lift_at:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\ create_cut_region a m s /\
  m.cs_next_id <= b.cs_next_id /\
  (!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u) /\
  exit_result r /\ create_operand_full_scope a m explicit ctx fn s ms r ==>
  create_operand_full_scope a b explicit ctx fn s ms r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def, exit_result_def] >>
  strip_tac >>
  rename1 `create_expr_prefix a m explicit ctx fn s left stop` >>
  `create_cut_region a m stop` by metis_tac[create_expr_prefix_cut_region] >>
  `create_expr_prefix a b explicit ctx fn s left stop` by
    metis_tac[create_left_prefix_lift_at] >>
  metis_tac[create_operand_at_def]
QED

Theorem create_left_focus_lift_at:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\ create_cut_region a m s /\
  m.cs_next_id <= b.cs_next_id /\
  (!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u) /\
  create_operand_focus_scope a m explicit ctx fn s ms ==>
  create_operand_focus_scope a b explicit ctx fn s ms
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix a m explicit ctx fn s left stop` >>
  `create_expr_prefix a b explicit ctx fn s left stop` by
    metis_tac[create_left_prefix_lift_at] >>
  qexistsl [`left`,`stop`,`pending`] >> simp[] >>
  `create_cut_region a m stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> conj_tac >- metis_tac[create_operand_at_def] >>
  rpt strip_tac >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED
