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

Theorem dfs_calls_entry_exists:
  !lv dfg cfg fn ps0.
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    ?entry. fn_entry_label fn = SOME entry) /\
  (!saved spilled succs visited ps.
    dfs_succs_call lv dfg cfg fn ps0 saved spilled succs visited ps ==>
    ?entry. fn_entry_label fn = SOME entry)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt strip_tac >> metis_tac[]
QED

Theorem dfs_calls_contained:
  !lv dfg cfg fn ps0.
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    !entry root_ops root_vis root_ps.
      fn_entry_label fn = SOME entry /\
      generate_fn_plan_aux lv dfg cfg fn [entry] [] ps0 =
        SOME (root_ops, root_vis, root_ps) ==>
      ?ops vis' ps' pre post.
        generate_fn_plan_aux lv dfg cfg fn wl visited ps =
          SOME (ops, vis', ps') /\
        root_ops = pre ++ ops ++ post) /\
  (!saved spilled succs visited ps.
    dfs_succs_call lv dfg cfg fn ps0 saved spilled succs visited ps ==>
    !entry root_ops root_vis root_ps.
      fn_entry_label fn = SOME entry /\
      generate_fn_plan_aux lv dfg cfg fn [entry] [] ps0 =
        SOME (root_ops, root_vis, root_ps) ==>
      ?ops vis' ps' pre post.
        generate_succs_plan lv dfg cfg fn saved spilled succs visited ps =
          SOME (ops, vis', ps') /\
        root_ops = pre ++ ops ++ post)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qexistsl_tac [`[]`, `[]`] >> simp[])
  >- suspend "visited"
  >- suspend "missing"
  >- suspend "succs"
  >- suspend "rest"
  >- suspend "branch"
  >> suspend "sibling"
QED

Resume dfs_calls_contained[visited]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def] >> strip_tac >>
  metis_tac[]
QED

Resume dfs_calls_contained[missing]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def] >> strip_tac >>
  metis_tac[]
QED

Resume dfs_calls_contained[succs]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`pre ++ block_ops`, `rest_ops ++ post`] >> simp[APPEND_ASSOC]
QED

Resume dfs_calls_contained[rest]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`pre ++ block_ops ++ succ_ops`, `post`] >> simp[APPEND_ASSOC]
QED
Resume dfs_calls_contained[branch]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`pre`, `rest_ops ++ post`] >> simp[APPEND_ASSOC]
QED
Resume dfs_calls_contained[sibling]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`pre ++ s_ops`, `post`] >> simp[APPEND_ASSOC]
QED
Finalise dfs_calls_contained

Theorem dfs_block_plan_contained:
  !lv dfg cfg ch growth fn base ctr fn_ops ps_end lbl ps bb block_ops ps_after.
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
      SOME (fn_ops, ps_end) /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth base ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops, ps_after) ==>
    ?pre post. fn_ops = pre ++ block_ops ++ post
Proof
  rpt gen_tac >> strip_tac >>
  gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_entry_exists) >> strip_tac >>
  qpat_x_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`
    mp_tac >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule (cj 1 dfs_calls_contained) >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`pre`, `succ_ops ++ rest_ops ++ post`] >> simp[APPEND_ASSOC]
QED
