Theory fnPlanPlaceDfsBlock
Ancestors
  fnPlanLineage stackPlanGen venomExecProps stackOpSim asmSem codegen asmToBytecodeProofs codegenEncodingWf
  list rich_list arithmetic fnPlanPlaceRevertPostamble fnPlanPlaceFnRegion

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

Theorem lookup_block_plan_leading_label:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps') ==>
  ?tail. ops = SOLabel lbl :: tail
Proof
  strip_tac >> drule lookup_block_label >>
  drule generate_block_plan_leading_label >> rpt strip_tac >> gvs[]
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

Theorem codegen_assembly_symbols_ok:
  codegen_assembly rpolicy unit = SOME prog ==> asm_symbols_ok prog
Proof
  simp[codegen_assembly_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem codegen_region_subplan_contained:
  !cp rpolicy unit prog r pre_ops block_ops post_ops.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    MEM r cp.cp_regions /\
    r.sr_plan = pre_ops ++ block_ops ++ post_ops ==>
    ?pre post. prog = pre ++ execute_plan cp.cp_initial_fmp block_ops ++ post
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
  simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >>
  gvs[context_plan_ops_def, MAP_APPEND, FLAT_APPEND, execute_plan_append] >>
  qmatch_goalsub_abbrev_tac `execute_plan fmp block_ops` >>
  qexistsl_tac
    [`execute_plan fmp (FLAT (MAP (\r. r.sr_plan) l1)) ++ execute_plan fmp pre_ops`,
     `execute_plan fmp post_ops ++
      execute_plan fmp (FLAT (MAP (\r. r.sr_plan) l2)) ++
      execute_plan fmp revert_postamble ++ data_segment_asm unit.cu_data_segment ++
      [AsmDataHeader "code_end"]`] >> simp[APPEND_ASSOC]
QED

Theorem distinct_flat_map_index:
  !xs i j x.
    ALL_DISTINCT (FLAT (MAP f xs)) /\ i < LENGTH xs /\ j < LENGTH xs /\
    MEM x (f (EL i xs)) /\ MEM x (f (EL j xs)) ==> i = j
Proof
  Induct_on `xs` >- simp[] >>
  Cases_on `i` >> Cases_on `j` >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[MEM_EL]
QED

Theorem asm_symbols_ok_label_index:
  !prog k l.
    asm_symbols_ok prog /\ k < LENGTH prog /\ EL k prog = AsmLabel l ==>
    ?off. FLOOKUP (SND (compute_label_offsets prog)) l = SOME off /\
          off < dimword (:256) /\
          FLOOKUP (build_offset_to_pc prog) off = SOME k
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP asm_defined_symbols prog))` by
    metis_tac[asm_symbols_ok_distinct] >>
  `!j. k < j /\ j < LENGTH prog ==>
       EL j prog <> AsmLabel l /\
       (!l'. EL j prog = AsmDataHeader l' ==> l' <> l)` by
    (rpt strip_tac >>
     `MEM l (asm_defined_symbols (EL k prog))` by simp[asm_defined_symbols_def] >>
     `MEM l (asm_defined_symbols (EL j prog))` by gvs[asm_defined_symbols_def] >>
     `k = j` by metis_tac[distinct_flat_map_index] >> decide_tac) >>
  `FLOOKUP (SND (compute_label_offsets prog)) l =
     SOME (asm_pc_to_offset prog k)` by
    (irule label_offset_consistent_proof >> metis_tac[]) >>
  qexists_tac `asm_pc_to_offset prog k` >> simp[] >>
  conj_tac
  >- (drule (cj 2 compute_label_offsets_bound) >> strip_tac >>
      gvs[asm_symbols_ok_def, wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac)
  >> irule offset_to_pc_inverse_proof >> simp[symbolResolveTheory.asm_inst_size_def]
QED


Theorem asm_slice_internal_labels:
  !prog pre code post.
    asm_symbols_ok prog /\ prog = pre ++ code ++ post ==>
    !l j. j < LENGTH code /\ EL j code = AsmLabel l ==>
    ?off. FLOOKUP (SND (compute_label_offsets prog)) l = SOME off /\
          off < dimword (:256) /\
          FLOOKUP (build_offset_to_pc prog) off = SOME (LENGTH pre + j)
Proof
  rpt strip_tac >> irule asm_symbols_ok_label_index >>
  simp[EL_APPEND]
QED
