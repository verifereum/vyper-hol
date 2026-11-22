(* Recover a straight-line run from adjacent observed compiler cuts. *)
Theory createSizeIndexedRun
Ancestors
  createSizeStraightPrefix createSizePrefixReplay createExprSizeExitDefs
  abiEncoderProps compileEnv fragExec fragGasOrigin exprLoweringProps venomState venomInst
  venomExecSemantics context relation arithmetic list rich_list

Theorem create_prefix_band_rtc[local]:
  lo <= a.cs_next_id /\ b.cs_next_id <= hi /\
  create_expr_prefix a b explicit ctx fn u marks v ==>
  RTC (\p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ lo <= i.inst_id /\ i.inst_id < hi /\
    gas_origin_edge F explicit ctx fn p ms (OK q)) u v
Proof
  strip_tac >> drule_then irule create_expr_prefix_rtc_project >>
  simp[create_prefix_step_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> fs[frag_ids_def] >> decide_tac
QED

Theorem indexed_rtc_join[local]:
  !n k (obs : num -> 'a) R.
    (!i. k <= i /\ i < k+n ==> RTC R (obs i) (obs (SUC i))) ==>
    RTC R (obs k) (obs (k+n))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `RTC R (obs k) (obs (k+n))` by
    (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `RTC R (obs (k+n)) (obs (SUC (k+n)))` by
    (first_x_assum irule >> decide_tac) >>
  simp[ADD_CLAUSES] >> metis_tac[RTC_TRANS]
QED

Theorem create_indexed_straight_run:
  i <= k /\
  (!j. i <= j /\ j < k ==>
    a.cs_next_id <= (C j).cs_next_id /\ (C (SUC j)).cs_next_id <= b.cs_next_id /\
    create_expr_prefix (C j) (C (SUC j)) explicit ctx fn
      (Obs j) (marks j) (Obs (SUC j))) /\
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  (Obs i).vs_current_bb = a.cs_current_bb /\
  (Obs i).vs_inst_idx = LENGTH a.cs_current_insts /\
  (Obs k).vs_current_bb = b.cs_current_bb /\
  (Obs k).vs_inst_idx = LENGTH b.cs_current_insts /\
  EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
    (emitted_insts a b) /\
  lookup_block (Obs k).vs_current_bb fn.fn_blocks = SOME end_bb /\
  get_instruction end_bb (Obs k).vs_inst_idx = SOME inst /\ b.cs_next_id <= inst.inst_id ==>
  run_inst_seq (emitted_insts a b) (Obs i) =
    OK ((Obs k) with vs_inst_idx := (Obs i).vs_inst_idx)
Proof
  strip_tac >>
  qabbrev_tac `R = \p q. ?bb x ms.
    lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME x /\ a.cs_next_id <= x.inst_id /\
    x.inst_id < b.cs_next_id /\ gas_origin_edge F explicit ctx fn p ms (OK q)` >>
  `RTC R (Obs i) (Obs k)` by
    (`i + (k-i) = k` by decide_tac >>
     qspecl_then [`k-i`,`i`,`Obs`,`R`] mp_tac indexed_rtc_join >>
     qpat_assum `i+(k-i) = k` (pure_rewrite_tac o single) >>
     simp_tac bool_ss [Abbr `R`] >>
     disch_then irule >> qx_gen_tac `j` >> strip_tac >>
     qpat_assum `!r. i <= r /\ r < k ==> _` (qspec_then `j` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     irule create_prefix_band_rtc >> goal_assum (drule_at Any) >> simp[]) >>
  irule create_straight_prefix_run >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `fn_has_code a b fn` (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  qexistsl_tac [`R`,`end_bb`,`ctx`,`explicit`,`fn`] >>
  `end_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  `lookup_block a.cs_current_bb fn.fn_blocks = SOME end_bb` by metis_tac[] >>
  `isPREFIX (emitted_insts a b) (DROP (LENGTH a.cs_current_insts) end_bb.bb_instructions)` by
    (qpat_assum `b.cs_current_insts ≼ bb.bb_instructions`
       (qx_choose_then `rest` assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     qpat_assum `end_bb = bb` (pure_rewrite_tac o single) >>
     qpat_assum `bb.bb_instructions = _` (pure_rewrite_tac o single) >>
     qpat_assum `b.cs_current_insts = _` (pure_rewrite_tac o single) >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND,IS_PREFIX_APPEND] >>
     qexists_tac `rest` >> REFL_TAC) >>
  `!u v. u.vs_current_bb = (Obs k).vs_current_bb /\
    u.vs_inst_idx = (Obs k).vs_inst_idx ==> ~R u v` by
    (simp[Abbr `R`] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >- (simp[Abbr `R`, PULL_EXISTS] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `(Obs i).vs_current_bb = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `(Obs i).vs_inst_idx = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
