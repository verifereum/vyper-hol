Theory loadElimStaticPointClosure
Ancestors
  loadElimStaticPhiClosure loadElimPrependIndex loadElimDefs
  analysisSimDefs analysisSimProofsBase passSimulationProps venomWf venomInst venomExecSemantics
  list indexedLists rich_list venomExecProofs passSimulationDefs arithmetic

Theorem le_prepend_earlier_definition:
  le_configured_context ctx /\ n < LENGTH bb.bb_instructions /\
  phi_prefix_length bb.bb_instructions <= n /\ i < n ==>
  ?k. k < n + LENGTH (phis_for_block actions bb.bb_label) /\
    EL k (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions =
    load_elim_inst ctx actions (df_at NONE result bb.bb_label i)
      (EL i bb.bb_instructions)
Proof
  strip_tac >>
  Cases_on `i < phi_prefix_length bb.bb_instructions`
  >- (qexists `i` >>
      simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
        flat_mapi_singleton, le_actual_mapi_phi_length, LENGTH_TAKE,
        LENGTH_MAPi, phi_prefix_length_le, arithmeticTheory.MIN_DEF,
        EL_APPEND_EQN, EL_TAKE, EL_MAPi]) >>
  qexists `i + LENGTH (phis_for_block actions bb.bb_label)` >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
    flat_mapi_singleton, le_actual_mapi_phi_length, LENGTH_TAKE, LENGTH_DROP,
    LENGTH_MAPi, phi_prefix_length_le, arithmeticTheory.MIN_DEF,
    EL_APPEND_EQN, EL_DROP, EL_MAPi]
QED

Theorem le_round_point_available:
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  phi_prefix_length bb.bb_instructions <= n /\
  def_available_at fn bb (SOME (EL n bb.bb_instructions)) v ==>
  def_available_at (load_elim_one ctx (cfg_analyze fn) fn)
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb)
    (SOME (load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
      (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) bb.bb_label n) (EL n bb.bb_instructions))) v
Proof
  strip_tac >>
  qabbrev_tac `actions = collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn` >>
  qabbrev_tac `tr = analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend actions) (\ll inst. [load_elim_inst ctx actions ll inst])` >>
  `!b. (tr b).bb_label = b.bb_label` by
    simp[Abbr `tr`, analysis_block_transform_prepend_def] >>
  `!b. MEM b fn.fn_blocks ==> MEM (tr b)
    (load_elim_one ctx (cfg_analyze fn) fn).fn_blocks` by
    (simp[load_elim_one_def, analysis_function_transform_prepend_def,
      function_map_transform_def, MEM_MAP, Abbr `actions`, Abbr `tr`] >>
     metis_tac[]) >>
  fs[def_available_at_def] >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `j = n` by (irule inst_ids_el_eq >> qexistsl [`bb`, `fn`] >>
        gvs[wf_function_def]) >> gvs[] >> rename1 `i < n` >>
      drule_all le_prepend_earlier_definition >>
      disch_then (qspecl_then [`load_analyze ctx fn`, `actions`] strip_assume_tac) >>
      `get_instruction (tr bb) (n + LENGTH (phis_for_block actions bb.bb_label)) =
       SOME (load_elim_inst ctx actions (df_at NONE (load_analyze ctx fn)
         bb.bb_label n) (EL n bb.bb_instructions))` by
        (simp[Abbr `tr`] >> irule le_actual_prepend_get_instruction >>
         simp[get_instruction_def]) >>
      `MEM v (load_elim_inst ctx actions (df_at NONE (load_analyze ctx fn)
        bb.bb_label i) (EL i bb.bb_instructions)).inst_outputs` by
        (simp[le_configured_outputs_retained] >>
         metis_tac[fn_inst_wf_def, EVERY_MEM, MEM_EL, le_configured_outputs_retained]) >>
      qexistsl [`tr bb`, `EL k (tr bb).bb_instructions`] >>
      gvs[get_instruction_def] >>
      conj_tac >- metis_tac[MEM_EL, LESS_TRANS] >>
      conj_tac >- simp[le_round_dominates] >>
      qexistsl [`k`, `n + LENGTH (phis_for_block actions bb.bb_label)`] >> simp[]) >>
  `EVERY inst_wf def_bb.bb_instructions` by
    metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  drule_all le_prepend_definition_retained >>
  disch_then (qspecl_then [`load_analyze ctx fn`, `actions`] strip_assume_tac) >>
  qexistsl [`tr def_bb`, `j`] >>
  simp[le_round_dominates] >> conj_tac >- gvs[Abbr `tr`] >>
  strip_tac >>
  `def_bb.bb_label = bb.bb_label` by metis_tac[] >>
  metis_tac[same_label_same_block]
QED

Theorem le_prepend_generated_index:
  le_configured_context ctx /\ MEM phi (phis_for_block actions bb.bb_label) ==>
  ?k. phi_prefix_length bb.bb_instructions <= k /\
    k < phi_prefix_length bb.bb_instructions + LENGTH (phis_for_block actions bb.bb_label) /\
    k < LENGTH (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions /\
    EL k (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions = phi
Proof
  strip_tac >>
  `?i. i < LENGTH (phis_for_block actions bb.bb_label) /\
    EL i (phis_for_block actions bb.bb_label) = phi` by metis_tac[MEM_EL] >>
  qexists `phi_prefix_length bb.bb_instructions + i` >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
    flat_mapi_singleton, le_actual_mapi_phi_length, LENGTH_TAKE, LENGTH_DROP,
    LENGTH_MAPi, phi_prefix_length_le, arithmeticTheory.MIN_DEF,
    EL_APPEND_EQN]
QED

Theorem le_round_generated_output_available:
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  MEM jb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  MEM phi (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn) jb.bb_label) /\
  MEM v phi.inst_outputs /\ fn_dominates fn jb.bb_label bb.bb_label /\
  n < LENGTH bb.bb_instructions /\ phi_prefix_length bb.bb_instructions <= n ==>
  def_available_at (load_elim_one ctx (cfg_analyze fn) fn)
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb)
    (SOME (load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
      (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) bb.bb_label n) (EL n bb.bb_instructions))) v
Proof
  strip_tac >>
  qabbrev_tac `actions = collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn` >>
  qabbrev_tac `tr = analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend actions) (\ll inst. [load_elim_inst ctx actions ll inst])` >>
  `!b. (tr b).bb_label = b.bb_label` by
    simp[Abbr `tr`, analysis_block_transform_prepend_def] >>
  `MEM (tr jb) (load_elim_one ctx (cfg_analyze fn) fn).fn_blocks` by
    (simp[load_elim_one_def, analysis_function_transform_prepend_def,
      function_map_transform_def, MEM_MAP, Abbr `actions`, Abbr `tr`] >>
     metis_tac[]) >>
  drule_all le_prepend_generated_index >>
  disch_then (qspec_then `load_analyze ctx fn` strip_assume_tac) >>
  simp[def_available_at_def] >> qexistsl [`tr jb`, `phi`] >> simp[] >>
  conj_tac >- metis_tac[MEM_EL] >>
  conj_tac >- simp[le_round_dominates] >>
  strip_tac >>
  `jb.bb_label = bb.bb_label` by metis_tac[] >>
  `jb = bb` by metis_tac[same_label_same_block] >> gvs[] >>
  `get_instruction (tr bb) (n + LENGTH (phis_for_block actions bb.bb_label)) =
   SOME (load_elim_inst ctx actions (df_at NONE (load_analyze ctx fn)
     bb.bb_label n) (EL n bb.bb_instructions))` by
    (simp[Abbr `tr`] >> irule le_actual_prepend_get_instruction >>
     simp[get_instruction_def]) >>
  gvs[get_instruction_def] >>
  qexistsl [`k`, `n + LENGTH (phis_for_block actions bb.bb_label)`] >> simp[]
QED
