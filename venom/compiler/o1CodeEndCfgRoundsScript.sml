(* Conditional round transport: the collapse observation premise is discharged
   by the independent collapse publication at the CFG join. *)
Theory o1CodeEndCfgRounds
Ancestors
  o1CodeEndCfgCleanup simplifyCfgRoundSemantics simplifyCfgGeneratedSubst
  simplifyCfgStaticInterface simplifyCfgCollapseSemantics simplifyCfgDefs
  simplifyCfgControl o1PassLift venomWf venomInst

Theorem o1_code_end_round_reach_back:
  (!f lm visited lbl. scfg_normalized f ==>
    !C s0 j t.
      fn_entry_state f s0 /\
      frame_reach C (FST (collapse_dfs f lm visited lbl)) s0 j t /\
      j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
      ?s. frame_reach C f s0 j s /\ scfg_payload s t) ==>
  !fn C s0 j t.
    scfg_static fn /\ fn_entry_state fn s0 /\
    frame_reach C (FST (simplify_cfg_round_with_labels fn)) s0 j t /\
    j.inst_opcode <> ASSIGN /\ j.inst_opcode <> PHI /\
    ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fn_entry_label fn`
  >- fs[fn_entry_state_def] >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks fn)` >>
  `scfg_collapse_contract fn clean` by metis_tac[scfg_cleanup_contract] >>
  `scfg_normalized clean` by fs[scfg_collapse_contract_def] >>
  `fn_entry_state clean s0` by
    fs[fn_entry_state_def, scfg_collapse_contract_def] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `scfg_collapse_contract clean q` by
    metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `ALL_DISTINCT (fn_labels clean)` by
    fs[scfg_normalized_def, scfg_static_def, wf_function_def, fn_labels_def] >>
  `subst_block_labels_fn r0 q = q` by
    metis_tac[scfg_collapse_subst_identity] >>
  `frame_reach C (fix_all_phis (remove_unreachable_blocks q)) s0 j t` by
    (Cases_on `r0 = []` >>
     gvs[simplify_cfg_round_with_labels_def, Abbr `clean`]) >>
  `scfg_static q /\ fn_entry_state q s0` by
    metis_tac[scfg_normalized_static, scfg_collapse_contract_def,
              fn_entry_state_def] >>
  `frame_reach C q s0 j t` by
    (irule o1_code_end_cleanup_reach_back >> fs[scfg_static_def]) >>
  `?s. frame_reach C clean s0 j s /\ scfg_payload s t` by
    (first_x_assum irule >> simp[] >> metis_tac[pairTheory.FST]) >>
  qexists `s` >> simp[] >>
  irule o1_code_end_cleanup_reach_back >> fs[scfg_static_def, Abbr `clean`]
QED

Theorem o1_code_end_iter_reach_back:
  (!f lm visited lbl. scfg_normalized f ==>
    !C s0 j t.
      fn_entry_state f s0 /\
      frame_reach C (FST (collapse_dfs f lm visited lbl)) s0 j t /\
      j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
      ?s. frame_reach C f s0 j s /\ scfg_payload s t) ==>
  !n fn C s0 j t.
    scfg_static fn /\ fn_entry_state fn s0 /\
    frame_reach C (FST (simplify_cfg_iter_with_labels n fn)) s0 j t /\
    j.inst_opcode <> ASSIGN /\ j.inst_opcode <> PHI /\
    ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t
Proof
  disch_tac >> Induct
  >- (simp[simplify_cfg_iter_with_labels_def] >> metis_tac[scfg_payload_refl]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  Cases_on `q.fn_blocks = fn.fn_blocks`
  >- (gvs[simplify_cfg_iter_with_labels_def] >>
      metis_tac[scfg_payload_refl]) >>
  `scfg_collapse_contract fn q` by
    metis_tac[scfg_round_contract, pairTheory.FST] >>
  `scfg_static q /\ fn_entry_state q s0` by
    metis_tac[scfg_collapse_contract_def, scfg_normalized_static,
              fn_entry_state_def] >>
  `frame_reach C (FST (simplify_cfg_iter_with_labels n q)) s0 j t` by
    (Cases_on `simplify_cfg_iter_with_labels n q` >>
     gvs[simplify_cfg_iter_with_labels_def]) >>
  `?u. frame_reach C q s0 j u /\ scfg_payload u t` by
    (first_x_assum irule >> simp[]) >>
  `?s. frame_reach C fn s0 j s /\ scfg_payload s u` by
    (irule o1_code_end_round_reach_back >> simp[] >>
     metis_tac[pairTheory.FST]) >>
  metis_tac[scfg_payload_trans]
QED
