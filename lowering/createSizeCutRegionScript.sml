(* Instruction ownership up to a compiler cut, with closed block ends
   admitted as dead positions. The lower bound belongs to the first block
   occurrence only, not to every occurrence of its label. *)
Theory createSizeCutRegion
Ancestors
  createSizeCutCode createSizeEdgePC externalEntryShape loweringShapeDefs
  exprSimAbiGasBridge exprLoweringProps fragExec fragGasOrigin compileEnv
  venomExecProofs venomExecSemantics venomInst venomState list rich_list pred_set

Definition create_cut_region_def:
  create_cut_region a m s <=>
    (s.vs_current_bb = m.cs_current_bb /\
     s.vs_inst_idx <= LENGTH m.cs_current_insts /\
     (emitted_blocks a m = [] ==> LENGTH a.cs_current_insts <= s.vs_inst_idx)) \/
    (emitted_blocks a m <> [] /\
     s.vs_current_bb = (LAST (emitted_blocks a m)).bb_label /\
     LENGTH a.cs_current_insts <= s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH (LAST (emitted_blocks a m)).bb_instructions) \/
    (?bb. MEM bb (FRONT (emitted_blocks a m)) /\
          s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx <= LENGTH bb.bb_instructions)
End

Theorem create_cut_span_layout[local]:
  cs_extends a m ==>
  if emitted_blocks a m = [] then
    m.cs_current_bb = a.cs_current_bb /\
    isPREFIX a.cs_current_insts m.cs_current_insts /\ added_labels a m = []
  else
    (LAST (emitted_blocks a m)).bb_label = a.cs_current_bb /\
    isPREFIX a.cs_current_insts (LAST (emitted_blocks a m)).bb_instructions /\
    added_labels a m =
      MAP (\bb. bb.bb_label) (REVERSE (FRONT (emitted_blocks a m))) ++ [m.cs_current_bb]
Proof
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks a m = new` by metis_tac[emitted_blocks_append] >>
  Cases_on `new = []` >> gvs[]
  >- simp[added_labels_def, all_blocks_def] >>
  `m.cs_blocks = FRONT (emitted_blocks a m) ++ LAST (emitted_blocks a m) :: a.cs_blocks` by
    (qpat_assum `m.cs_blocks = _` SUBST1_TAC >>
     simp[GSYM APPEND, listTheory.APPEND_ASSOC, APPEND_FRONT_LAST]) >>
  simp[added_labels_def, all_blocks_def] >> pop_assum SUBST1_TAC >>
  simp[REVERSE_APPEND, DROP_LENGTH_APPEND, LENGTH_MAP, DROP_APPEND, MAP_REVERSE,
       DROP_LENGTH_TOO_LONG, GSYM listTheory.APPEND_ASSOC,
       DECIDE ``x - (y + x) = 0n``]
QED

Theorem create_cut_start[local]:
  cs_extends a m /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==> create_cut_region a m s
Proof
  strip_tac >> drule create_cut_span_layout >>
  Cases_on `emitted_blocks a m = []` >> simp[create_cut_region_def] >>
  metis_tac[IS_PREFIX_LENGTH]
QED

Theorem create_cut_fetch_mem[local]:
  fn_has_code a m fn /\ create_cut_region a m s /\
  (s.vs_current_bb <> m.cs_current_bb \/ s.vs_inst_idx <> LENGTH m.cs_current_insts) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  MEM i (frag_code a m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `create_cut_region _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_cut_region_def])
  >- (fs[fn_has_code_def] >> gvs[] >>
      `s.vs_inst_idx < LENGTH m.cs_current_insts` by decide_tac >>
      `i = EL s.vs_inst_idx m.cs_current_insts` by
        (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[is_prefix_el]) >>
      Cases_on `emitted_blocks a m = []`
      >- (gvs[frag_code_def, emitted_insts_def, MEM_DROP] >>
          qexists_tac `s.vs_inst_idx - LENGTH a.cs_current_insts` >> simp[]) >>
      simp[frag_code_def, NULL_EQ, EL_MEM])
  >- (fs[fn_has_code_def] >>
      `MEM (LAST (emitted_blocks a m)) (emitted_blocks a m)` by
        simp[MEM_LAST_NOT_NIL] >>
      gvs[frag_code_def, NULL_EQ, get_instruction_def, AllCaseEqs(), MEM_DROP] >>
      disj1_tac >> disj1_tac >>
      qexists_tac `s.vs_inst_idx - LENGTH a.cs_current_insts` >> simp[]) >>
  rename1 `MEM b (FRONT (emitted_blocks a m))` >>
  `emitted_blocks a m <> []` by (strip_tac >> gvs[FRONT_DEF]) >>
  `MEM b (emitted_blocks a m)` by metis_tac[MEM_FRONT_NOT_NIL] >>
  fs[fn_has_code_def] >>
  gvs[frag_code_def, NULL_EQ, get_instruction_def, AllCaseEqs(), MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem create_cut_fallthrough[local]:
  fn_has_code a m fn /\ create_cut_region a m u /\
  (u.vs_current_bb <> m.cs_current_bb \/ u.vs_inst_idx <> LENGTH m.cs_current_insts) /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  v.vs_current_bb = u.vs_current_bb /\ v.vs_inst_idx = SUC u.vs_inst_idx ==>
  create_cut_region a m v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `create_cut_region _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_cut_region_def]) >>
  rewrite_tac[create_cut_region_def]
  >- (disj1_tac >> fs[] >> strip_tac >> fs[] >> decide_tac)
  >- (disj2_tac >> disj1_tac >> fs[fn_has_code_def] >>
      `MEM (LAST (emitted_blocks a m)) (emitted_blocks a m)` by simp[MEM_LAST_NOT_NIL] >>
      gvs[get_instruction_def, AllCaseEqs()]) >>
  rename1 `MEM b (FRONT (emitted_blocks a m))` >>
  `emitted_blocks a m <> []` by (strip_tac >> gvs[FRONT_DEF]) >>
  `MEM b (emitted_blocks a m)` by metis_tac[MEM_FRONT_NOT_NIL] >>
  disj2_tac >> disj2_tac >> qexists_tac `b` >>
  fs[fn_has_code_def] >> gvs[get_instruction_def, AllCaseEqs()]
QED

Theorem create_cut_jump_entry[local]:
  cs_extends a m /\ fn_has_code a m fn /\
  MEM v.vs_current_bb (added_labels a m) /\
  (MEM m.cs_current_bb (added_labels a m) ==>
   !target. lookup_block m.cs_current_bb fn.fn_blocks = SOME target ==>
            phi_prefix_length target.bb_instructions <= LENGTH m.cs_current_insts) /\
  (v.vs_inst_idx = 0 \/
   ?target. lookup_block v.vs_current_bb fn.fn_blocks = SOME target /\
            v.vs_inst_idx = phi_prefix_length target.bb_instructions) ==>
  create_cut_region a m v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emitted_blocks a m = []`
  >- (drule create_cut_span_layout >> simp[] >> strip_tac >> gvs[]) >>
  drule create_cut_span_layout >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `v.vs_current_bb = m.cs_current_bb`
  >- (rewrite_tac[create_cut_region_def] >> disj1_tac >>
      `MEM m.cs_current_bb (added_labels a m)` by metis_tac[] >>
      simp[] >> metis_tac[DECIDE ``0 <= n``]) >>
  `?b. MEM b (FRONT (emitted_blocks a m)) /\ v.vs_current_bb = b.bb_label` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `MEM b (emitted_blocks a m)` by metis_tac[MEM_FRONT_NOT_NIL] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME b` by
    (qpat_x_assum `fn_has_code _ _ _`
       (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
     qpat_assum `!bb. MEM bb (emitted_blocks a m) ==> _`
       (qspec_then `b` mp_tac) >> simp[]) >>
  rewrite_tac[create_cut_region_def] >> disj2_tac >> disj2_tac >> qexists_tac `b` >>
  simp[] >> qpat_x_assum `v.vs_inst_idx = 0 \/ _` mp_tac >>
  simp[] >> strip_tac >> simp[phi_prefix_length_le]
QED

Theorem create_cut_region_rules:
  create_cut_code {} a m /\ fn_has_code a m fn ==>
  (!s. s.vs_current_bb = a.cs_current_bb /\
       s.vs_inst_idx = LENGTH a.cs_current_insts ==> create_cut_region a m s) /\
  (!u bb i. create_cut_region a m u /\
       (u.vs_current_bb <> m.cs_current_bb \/ u.vs_inst_idx <> LENGTH m.cs_current_insts) /\
       lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb u.vs_inst_idx = SOME i ==>
       MEM i (frag_code a m) /\ i.inst_id IN frag_ids a m) /\
  ((MEM m.cs_current_bb (added_labels a m) ==>
    !target. lookup_block m.cs_current_bb fn.fn_blocks = SOME target ==>
             phi_prefix_length target.bb_instructions <= LENGTH m.cs_current_insts) ==>
   !u bb i explicit ctx ms v. create_cut_region a m u /\
       (u.vs_current_bb <> m.cs_current_bb \/ u.vs_inst_idx <> LENGTH m.cs_current_insts) /\
       lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb u.vs_inst_idx = SOME i /\
       gas_origin_edge F explicit ctx fn u ms (OK v) ==> create_cut_region a m v)
Proof
  strip_tac >>
  `cs_extends a m` by fs[create_cut_code_def] >>
  conj_tac >- metis_tac[create_cut_start] >>
  conj_tac >- metis_tac[create_cut_fetch_mem, create_cut_code_def] >>
  disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_ok_edge_pc >> disch_then (DISJ_CASES_THEN2 strip_assume_tac mp_tac)
  >- metis_tac[create_cut_fallthrough] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))) >>
  `MEM i (frag_code a m)` by metis_tac[create_cut_fetch_mem] >>
  `MEM v.vs_current_bb (added_labels a m)` by
    (drule_all create_cut_code_jump >> simp[]) >>
  qpat_x_assum `v.vs_current_bb = t.vs_current_bb` kall_tac >>
  irule create_cut_jump_entry >> simp[] >> qexists_tac `fn` >> simp[]
QED
