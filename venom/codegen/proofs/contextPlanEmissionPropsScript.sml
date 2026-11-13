(* Predicate preservation through block, function and context planning.
   All instruction and administrative facts are supplied at the boundary. *)
Theory contextPlanEmissionProps
Ancestors stackPlanGen stackPlanOps stackPlanTypes venomInst
  livenessAnalysis dfgDefs cfgDefs list rich_list

Theorem generate_block_insts_plan_preserves:
  (!inst live halting term cur ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
      SOME (ops, ps') /\ Q inst ==> EVERY P ops) ==>
  !insts i ps ops ps'.
    generate_block_insts_plan liveness dfg cfg fn bb_label halting
      n_params block_len i insts ps = SOME (ops, ps') /\
    EVERY Q insts ==> EVERY P ops
Proof
  strip_tac >> Induct >> simp[generate_block_insts_plan_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[EVERY_APPEND]
QED

Theorem generate_block_plan_preserves:
  (!inst live halting term cur ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
      SOME (ops, ps') /\ Q inst ==> EVERY P ops) /\
  (!ps ops ps'. prepare_params_plan liveness fn ps = (ops, ps') ==>
    EVERY P ops) /\
  (!ps ops ps'. clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    EVERY P ops) /\ P (SOLabel bb.bb_label) ==>
  !ps ops ps'.
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
    EVERY Q bb.bb_instructions ==> EVERY P ops
Proof
  strip_tac >> rpt gen_tac >> simp[generate_block_plan_def] >> pairarg_tac >>
  `EVERY P param_ops` by (gvs[AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >> qpat_x_assum `_ = (param_ops, ps1)` kall_tac >> pairarg_tac >>
  `EVERY P clean_ops` by (gvs[AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >> qpat_x_assum `_ = (clean_ops, ps2)` kall_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY Q (non_param_insts bb)` by
    (gvs[non_param_insts_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  drule generate_block_insts_plan_preserves >> disch_then drule >> simp[]
QED

Theorem lookup_block_insts_every:
  !bbs. EVERY Q (fn_insts_blocks bbs) /\ lookup_block lbl bbs = SOME bb ==>
    EVERY Q bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[lookup_block_def]
QED

Definition block_plan_preserves_def:
  block_plan_preserves P liveness dfg cfg fn <=>
    !lbl bb ps ops ps'. lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
      EVERY P ops
End

Theorem block_plan_preserves_elim[local]:
  block_plan_preserves P liveness dfg cfg fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
  EVERY P ops
Proof
  simp[block_plan_preserves_def] >> metis_tac[]
QED

Theorem fn_plan_aux_preserves_opaque[local]:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') /\
    block_plan_preserves P liveness dfg cfg fn ==> EVERY P ops) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') /\
    block_plan_preserves P liveness dfg cfg fn ==> EVERY P ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[])
  >- (rpt gen_tac >> strip_tac >>
      simp[NoAsms, Once generate_fn_plan_aux_def] >>
      Cases_on `MEM lbl visited`
      >- (qpat_assum `MEM lbl visited` (fn th => rewrite_tac[th]) >>
          metis_tac[]) >>
      qpat_assum `~MEM lbl visited` (fn th => rewrite_tac[th]) >>
      Cases_on `lookup_block lbl fn.fn_blocks`
      >- (qpat_assum `_ = NONE` (fn th => rewrite_tac[th]) >>
          fs[NoAsms] >> metis_tac[]) >>
      simp[NoAsms, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
      gvs[] >>
      `EVERY P block_ops` by (irule block_plan_preserves_elim >> metis_tac[]) >>
      simp[EVERY_APPEND] >> conj_tac >> metis_tac[])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[])
  >> rpt gen_tac >> strip_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[EVERY_APPEND]
QED

Theorem fn_plan_aux_preserves:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') /\
    (!lbl bb ps ops ps'. lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
      EVERY P ops) ==> EVERY P ops) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') /\
    (!lbl bb ps ops ps'. lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
      EVERY P ops) ==> EVERY P ops)
Proof
  metis_tac[fn_plan_aux_preserves_opaque, block_plan_preserves_def]
QED

Theorem generate_fn_plan_with_cleanup_preserves:
  (!lbl bb ps ops ps'. lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) (dfg_build_function fn)
      (cfg_analyze fn) fn bb ps = SOME (ops, ps') ==> EVERY P ops) ==>
  !ch growth spill_base lbl_ctr ops ps.
    generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr =
      SOME (ops, ps) ==> EVERY P ops
Proof
  simp[generate_fn_plan_with_cleanup_def,
       generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[cj 1 fn_plan_aux_preserves]
QED

Theorem generate_context_regions_preserves:
  !fns acc acc'.
    generate_context_regions gen fns acc = SOME acc' /\
    (!fn sb lc ops ps. MEM fn fns /\ gen fn sb lc = SOME (ops, ps) ==>
      EVERY P ops) /\
    EVERY (\r. EVERY P r.sr_plan) acc.cpa_regions ==>
    EVERY (\r. EVERY P r.sr_plan) acc'.cpa_regions
Proof
  Induct >> simp[generate_context_regions_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum drule >> impl_tac
  >- (simp[EVERY_SNOC] >> metis_tac[]) >> simp[]
QED

Theorem generate_context_plan_preserves:
  (!fn ch growth sb lc ops ps. MEM fn ctx.ctx_functions /\
    generate_fn_plan_with_cleanup ch growth fn sb lc = SOME (ops, ps) ==>
    EVERY P ops) /\ EVERY P revert_postamble /\
  generate_context_plan ctx = SOME cp ==> EVERY P (context_plan_ops cp)
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >> strip_tac >>
  `EVERY (\r. EVERY P r.sr_plan) acc.cpa_regions` by
    (drule generate_context_regions_preserves >>
     disch_then (qspec_then `P` mp_tac) >> impl_tac
     >- (simp[] >> metis_tac[]) >> simp[]) >>
  gvs[context_plan_ops_def, finish_context_plan_def, EVERY_FLAT, EVERY_MAP]
QED

Theorem generate_context_plan_insts_preserves:
  (!liveness (dfg : dfg_analysis) (cfg : cfg_analysis) fn inst live halting term cur ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
      SOME (ops, ps') /\ Q inst ==> EVERY P ops) /\
  (!liveness fn ps ops ps'.
    prepare_params_plan liveness fn ps = (ops, ps') ==> EVERY P ops) /\
  (!liveness cfg fn bb ps ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==> EVERY P ops) /\
  (!lbl. P (SOLabel lbl)) /\ EVERY P revert_postamble /\
  EVERY (\fn. EVERY Q (fn_insts fn)) ctx.ctx_functions /\
  generate_context_plan ctx = SOME cp ==> EVERY P (context_plan_ops cp)
Proof
  strip_tac >> irule generate_context_plan_preserves >>
  reverse conj_tac >- simp[] >>
  qexists_tac `ctx` >> simp[] >> rpt strip_tac >>
  drule_at Any generate_fn_plan_with_cleanup_preserves >>
  disch_then irule >> rpt strip_tac >>
  drule_at Any generate_block_plan_preserves >>
  disch_then (qspecl_then [`Q`, `P`] mp_tac) >> simp[] >>
  `EVERY Q (fn_insts fn)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  gvs[fn_insts_def] >> drule_at Any lookup_block_insts_every >>
  disch_then assume_tac >> impl_tac
  >- (rpt conj_tac >> rpt strip_tac >> metis_tac[]) >> simp[]
QED
