(* Candidate-list lifting of the guarded bypass contracts. *)
Theory simplifyCfgBypassWrapper
Ancestors
  simplifyCfgBypassSemantics simplifyCfgBypassPrecondition
  simplifyCfgBypassClosure simplifyCfgStaticInterface simplifyCfgSimTools
  simplifyCfgDefs cfgTransform list rich_list

Theorem scfg_try_bypass_choice:
  !candidates fn lm bb fn' lm' changed.
    scfg_normalized fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    try_bypass fn lm bb candidates = (fn',lm',changed) ==>
    fn' = fn \/ ?b. scfg_bypass_hyp fn bb b fn'
Proof
  Induct_on `candidates`
  >- simp[try_bypass_def] >>
  rpt gen_tac >> simp[Once try_bypass_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  disj2_tac >> rename1 `can_bypass_jump fn bb b` >>
  qexists_tac `b` >> simp[scfg_bypass_hyp_def] >>
  `LENGTH (bb_succs b) = 1` by
    gvs[can_bypass_jump_def, num_succs_def] >>
  Cases_on `bb_succs b` >> gvs[] >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_try_bypass_fn_bisim:
  scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  fn_bisim fn fn'
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- gvs[fn_bisim_refl] >>
  metis_tac[scfg_bypass_fn_bisim]
QED

Theorem scfg_try_bypass_frame_sim:
  ctx_bisim C C' /\ scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  frame_sim L C C' fn fn'
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- (gvs[] >> irule frame_sim_ctx_bisim >>
      metis_tac[scfg_normalized_static, scfg_static_inst_wf]) >>
  metis_tac[scfg_bypass_frame_sim]
QED

Theorem scfg_try_bypass_normalized:
  scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  scfg_normalized fn'
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- gvs[] >> metis_tac[scfg_bypass_normalized]
QED
