(* Successful block-entry alignment for the joint relation. *)
Theory o1LowerDloadJointEntry
Ancestors
  o1LowerDloadJointRelation o1ContractLowerDload contextCodegenRel
  lowerDloadDefs venomExecSemantics venomExecProps irSupply list
  o1PassContract venomWf venomInst unitMemInv unitTransformDefs

Theorem ld_supply_nonphi_head[local]:
  lower_dload_inst_supply u inst = (xs,v) /\ inst.inst_opcode <> PHI ==>
  xs <> [] /\ (HD xs).inst_opcode <> PHI
Proof
  strip_tac >> drule lower_dload_inst_supply_nonempty >> strip_tac >> simp[] >>
  strip_tac >>
  `MEM (HD xs) xs` by (Cases_on `xs` >> gvs[]) >>
  `HD xs = inst` by (irule lower_dload_inst_supply_control >> metis_tac[]) >>
  gvs[]
QED

Theorem ld_supply_phi_boundary:
  !u xs v. lower_dload_insts_supply u ins = (xs,v) ==>
    eval_phis s xs = eval_phis s ins /\
    phi_prefix_length xs = phi_prefix_length ins /\
    lower_dload_insts_supply u (TAKE (phi_prefix_length ins) ins) =
      (TAKE (phi_prefix_length ins) ins,u)
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def, eval_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply u h = ([h],u)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      gvs[eval_phis_def, phi_prefix_length_def,
           Once lower_dload_insts_supply_def]) >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all ld_supply_nonphi_head >> strip_tac >>
  Cases_on `out` >> gvs[eval_phis_def, phi_prefix_length_def,
                           lower_dload_insts_supply_def]
QED

Theorem ld_supply_block_index:
  !u bs v k. lower_dload_blocks_supply u bbs = (bs,v) /\
    k < LENGTH bbs ==>
    ?pre u1 bb' u2.
      lower_dload_blocks_supply u (TAKE k bbs) = (pre,u1) /\
      lower_dload_block_supply u1 (EL k bbs) = (bb',u2) /\
      k < LENGTH bs /\ EL k bs = bb'
Proof
  Induct_on `bbs`
  >- simp[] >>
  rpt gen_tac >> Cases_on `k`
  >- (simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      qexistsl [`[]`,`u`,`s1`] >>
      simp[lower_dload_blocks_supply_def]) >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexistsl [`bb'::pre`,`u1`,`u2`] >>
  gvs[Once lower_dload_blocks_supply_def]
QED

Theorem ld_supply_successful_entry:
  ir_supply_covers_fn u fn /\
  lower_dload_function_supply u fn = (fn',u') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  enters_block fn s s1 /\ active_inst fn inst s1 ==>
  enters_block fn' s s1 /\ ld_joint_control u fn fn' s1 s1
Proof
  strip_tac >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    (drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `?k. k < LENGTH fn.fn_blocks /\ bb = EL k fn.fn_blocks` by
    metis_tac[MEM_EL] >>
  qpat_assum `lower_dload_function_supply u fn = _`
    (mp_tac o REWRITE_RULE [lower_dload_function_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >>
  drule_all ld_supply_block_index >> strip_tac >>
  qpat_assum `lower_dload_block_supply u1 _ = _`
    (mp_tac o REWRITE_RULE [lower_dload_block_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >>
  drule ld_supply_phi_boundary >> strip_tac >>
  `MAP (\b. b.bb_label) bbs = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[lower_dload_blocks_supply_labels] >>
  `bb'.bb_label = bb.bb_label` by
    (qpat_assum `_ with bb_instructions := _ = bb'` (SUBST1_TAC o SYM) >>
     gvs[]) >>
  `MEM bb' bbs` by (simp[Once MEM_EL] >> qexists_tac `k` >> simp[]) >>
  `lookup_block s.vs_current_bb bbs = SOME bb'` by
    (irule MEM_lookup_block >> simp[] >> metis_tac[]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (qpat_x_assum `active_inst fn inst s1` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> gvs[]) >>
     gvs[]) >>
  conj_tac
  >- (qexistsl [`bb'`,`s_phi`] >>
      qpat_assum `_ with bb_instructions := _ = bb'` (SUBST1_TAC o SYM) >>
      gvs[]) >>
  simp[ld_joint_control_def] >>
  qexistsl [`k`,`pre`,`u1`,`u2`,
            `TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,`u1`] >>
  gvs[] >> simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem ld_joint_entry:
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ ptr_discipline lo C vs /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  ir_supply_covers_fn u fn /\
  lower_dload_function_supply u fn = (fn',u') /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s1 /\
  active_inst fn inst s1 ==>
  enters_block fn'
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s1 /\
  ld_joint_boundary vs C C' lo D [] [] FEMPTY entry_taint fn inst s1 s1
    1 0 [] FEMPTY [] FEMPTY FEMPTY FEMPTY []
Proof
  (* P4a in progress *) cheat
QED
