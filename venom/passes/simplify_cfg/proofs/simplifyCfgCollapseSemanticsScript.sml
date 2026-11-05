(* Composition of the validated elementary collapse contracts. *)
Theory simplifyCfgCollapseSemantics
Ancestors
  simplifyCfgBypassWrapper simplifyCfgBypassSemantics
  simplifyCfgBypassClosure simplifyCfgBypassPrecondition simplifyCfgMergeGlobalRuns
  simplifyCfgMergeSemantics simplifyCfgMergeClosure simplifyCfgMergePaths
  simplifyCfgLabelProps simplifyCfgStaticInterface simplifyCfgSimTools
  simplifyCfgDefs cfgTransform list rich_list

Definition scfg_collapse_contract_def:
  scfg_collapse_contract fn fn' <=>
    scfg_normalized fn' /\ fn_entry_label fn' = fn_entry_label fn /\
    fn_bisim fn fn' /\ !C L. frame_sim L C C fn fn'
End

Theorem scfg_collapse_contract_refl:
  scfg_normalized fn ==> scfg_collapse_contract fn fn
Proof
  simp[scfg_collapse_contract_def, fn_bisim_refl] >> strip_tac >>
  rpt gen_tac >> irule frame_sim_ctx_bisim >>
  metis_tac[ctx_bisim_refl, scfg_normalized_static, scfg_static_inst_wf]
QED

Theorem scfg_collapse_contract_trans:
  scfg_collapse_contract f g /\ scfg_collapse_contract g h ==>
  scfg_collapse_contract f h
Proof
  simp[scfg_collapse_contract_def] >> rpt strip_tac >>
  metis_tac[fn_bisim_trans, frame_sim_trans]
QED

Theorem scfg_collapse_chain:
  scfg_chain_hyp fn a b ==> scfg_collapse_contract fn (scfg_chain fn a b)
Proof
  simp[scfg_collapse_contract_def] >>
  metis_tac[scfg_chain_normalized, scfg_chain_entry_eq,
            scfg_chain_fn_bisim, scfg_chain_frame_sim]
QED

Theorem scfg_collapse_bypass:
  scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  scfg_collapse_contract fn fn'
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- (gvs[] >> irule scfg_collapse_contract_refl >> simp[]) >>
  simp[scfg_collapse_contract_def] >>
  metis_tac[scfg_bypass_normalized, scfg_bypass_entry_eq,
            scfg_bypass_fn_bisim, scfg_bypass_frame_sim, ctx_bisim_refl]
QED

Theorem scfg_collapse_joint:
  (!fn lm visited lbl. scfg_normalized fn ==>
    scfg_collapse_contract fn (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs. scfg_normalized fn ==>
    scfg_collapse_contract fn (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume scfg_collapse_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- simp[scfg_collapse_contract_refl] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  namedCases_on `bb_succs bb` ["", "s1 rest"]
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, scfg_collapse_contract_refl] >>
      gvs[try_bypass_def]) >>
  namedCases_on `rest` ["", "s2 rest2"]
  >- (Cases_on `lookup_block s1 fn.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> simp[scfg_collapse_contract_refl]) >>
      rename1 `lookup_block s1 fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- suspend "merge" >>
      Cases_on `MEM lbl visited`
      >- simp[scfg_collapse_contract_refl] >> gvs[]) >>
  suspend "bypass"
QED

Resume scfg_collapse_joint[merge]:
  gvs[] >>
  `next_bb.bb_label = s1` by metis_tac[lookup_block_member_label] >>
  `scfg_chain_hyp fn bb next_bb` by
    (simp[scfg_chain_hyp_def] >> metis_tac[]) >>
  drule scfg_collapse_chain >> strip_tac >>
  gvs[GSYM scfg_chain_def] >>
  irule scfg_collapse_contract_trans >>
  qexists_tac `scfg_chain fn bb next_bb` >>
  simp[] >> first_x_assum irule >>
  fs[scfg_collapse_contract_def]
QED

Resume scfg_collapse_joint[bypass]:
  Cases_on `try_bypass fn lm bb (s1::s2::rest2)` >> PairCases_on `r` >>
  `scfg_collapse_contract fn q` by
    (irule scfg_collapse_bypass >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  Cases_on `r1` >> gvs[]
  >- metis_tac[scfg_collapse_contract_trans] >>
  Cases_on `MEM bb.bb_label visited` >> gvs[] >>
  metis_tac[scfg_collapse_contract_trans]
QED

Resume scfg_collapse_joint[nil]:
  simp[collapse_dfs_def, scfg_collapse_contract_refl]
QED

Resume scfg_collapse_joint[succs]:
  rpt strip_tac >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm visited lbl` >> PairCases_on `r` >>
  gvs[] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  metis_tac[scfg_collapse_contract_trans]
QED

Finalise scfg_collapse_joint

Theorem scfg_collapse_normalized:
  scfg_normalized fn /\ collapse_dfs fn lm visited lbl = (fn',lm',vis') ==>
  scfg_normalized fn'
Proof
  metis_tac[scfg_collapse_joint, scfg_collapse_contract_def, pairTheory.FST]
QED

Theorem scfg_collapse_entry:
  scfg_normalized fn /\ collapse_dfs fn lm visited lbl = (fn',lm',vis') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  metis_tac[scfg_collapse_joint, scfg_collapse_contract_def, pairTheory.FST]
QED

Theorem scfg_collapse_fn_bisim:
  scfg_normalized fn /\ collapse_dfs fn lm visited lbl = (fn',lm',vis') ==>
  fn_bisim fn fn'
Proof
  metis_tac[scfg_collapse_joint, scfg_collapse_contract_def, pairTheory.FST]
QED

Theorem scfg_collapse_frame_sim_same:
  scfg_normalized fn /\ collapse_dfs fn lm visited lbl = (fn',lm',vis') ==>
  frame_sim L C C fn fn'
Proof
  metis_tac[scfg_collapse_joint, scfg_collapse_contract_def, pairTheory.FST]
QED
