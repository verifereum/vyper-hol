Theory fnPlanPlaceDfsBlock
Ancestors
  fnPlanLineage stackPlanGen venomExecProps stackOpSim
  list rich_list arithmetic

Theorem generate_context_regions_length:
  !fns acc acc'.
    generate_context_regions gen fns acc = SOME acc' ==>
    LENGTH acc'.cpa_regions = LENGTH acc.cpa_regions + LENGTH fns
Proof
  Induct_on `fns` >- simp[generate_context_regions_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_context_regions _ (_::_) _ = _` mp_tac >>
  simp[Once generate_context_regions_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum drule >> simp[LENGTH_SNOC]
QED

Theorem generate_context_plan_with_regions_length:
  !gen ctx cp. generate_context_plan_with gen ctx = SOME cp ==>
  LENGTH cp.cp_regions = LENGTH ctx.ctx_functions
Proof
  rpt gen_tac >> simp[generate_context_plan_with_def, AllCaseEqs()] >>
  strip_tac >> gvs[finish_context_plan_def] >>
  drule generate_context_regions_length >> simp[]
QED

Theorem generate_context_plan_regions_length:
  !ctx cp. generate_context_plan ctx = SOME cp ==>
  LENGTH cp.cp_regions = LENGTH ctx.ctx_functions
Proof
  simp[generate_context_plan_def] >>
  metis_tac[generate_context_plan_with_regions_length]
QED

Theorem generate_block_plan_leading_label:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps') ==>
  ?tail. ops = SOLabel lbl :: tail
Proof
  strip_tac >> drule lookup_block_label >> strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
QED
