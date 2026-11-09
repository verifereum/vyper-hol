Theory loadElimReachedNormalize
Ancestors
  loadElimNormalizeHelpers loadElimNormalizeAvailability loadElimLastWriter
  loadElimAssignSemantics loadElimTemporalStability analysisSimProofsBase
  loadElimOccurrence simplifyCfgLabelProps
  dfgDefs dfgAnalysisProps venomWf venomState venomInst venomExecProofs finite_map list

Theorem le_occ_available_assign_equality[local]:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  i.inst_opcode <> PHI /\ def_available_at fn bb (SOME i) v /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  di.inst_opcode = ASSIGN /\ di.inst_operands = [src] /\ di.inst_outputs = [v] ==>
  lookup_var v s = eval_operand src s
Proof
  strip_tac >> drule_all le_occ_available_last_writer >> strip_tac >>
  `MEM v di.inst_outputs` by simp[] >>
  drule_all le_occ_writer_static_unique >>
  namedCases_on `e` ["eb n k u t", "eb u t"] >> simp[] >> strip_tac
  >- (fs[le_occ_post_def] >>
      `step_inst k C di u = OK t` by fs[le_occ_valid_def] >>
      drule_all le_step_assign_result >> strip_tac >>
      Cases_on `src`
      >- gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
      >- (rename1 `di.inst_operands = [Var x]` >>
          `lookup_var x s = lookup_var x t` by
            (rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
             ` (EL n eb.bb_instructions).inst_opcode = ASSIGN /\
               (EL n eb.bb_instructions).inst_operands = [Var x] /\
               (EL n eb.bb_instructions).inst_outputs = [v]` by simp[] >>
             drule_all le_occ_assign_source_lookup >> simp[]) >>
          gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
          Cases_on `x = v` >> gvs[]) >>
      `eval_operand (Label s') t = eval_operand (Label s') s` by
        (rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
         drule le_occ_prefix_suffix_label >> simp[le_occ_post_def]) >>
      gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  mp_tac (Q.SPEC `eb.bb_instructions` phi_prefix_all_phi) >>
  simp[EVERY_MEM] >> disch_then (qspec_then `di` mp_tac) >> simp[]
QED

Theorem le_occ_available_chain_valid:
  !dfg visited op.
  dfg = dfg_build_function fn /\ wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ i.inst_opcode <> PHI /\
  (!v. op = Var v ==> def_available_at fn bb (SOME i) v) ==>
  le_chain_valid dfg visited op s
Proof
  recInduct normalize_operand_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      Cases_on `MEM v visited` >- gvs[Once le_chain_valid_def] >>
      Cases_on `FLOOKUP dfg.dfg_defs v` >- gvs[Once le_chain_valid_def] >>
      rename1 `FLOOKUP dfg.dfg_defs v = SOME di` >>
      reverse (Cases_on `di.inst_opcode = ASSIGN`)
      >- gvs[Once le_chain_valid_def] >>
      Cases_on `di.inst_operands` >- gvs[Once le_chain_valid_def] >>
      Cases_on `t` >> gvs[Once le_chain_valid_def] >>
      `dfg_get_def (dfg_build_function fn) v = SOME di` by simp[dfg_get_def_def] >>
      drule dfg_build_function_correct >> strip_tac >>
      `?db. MEM db fn.fn_blocks /\ MEM di db.bb_instructions` by
        (gvs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
      `inst_wf di` by metis_tac[fn_inst_wf_def] >>
      `di.inst_outputs = [v]` by
        (fs[inst_wf_def] >> Cases_on `di.inst_outputs` >> gvs[] >>
         Cases_on `t` >> gvs[]) >>
      conj_tac
      >- (irule le_occ_available_assign_equality >> metis_tac[]) >>
      first_x_assum irule >> rpt strip_tac >> gvs[] >>
      `def_available_at fn db (SOME di) v'` by
        (gvs[wf_ssa_def, def_dominates_uses_def] >>
         first_x_assum drule_all >> simp[]) >>
      irule le_available_via_definition >> gvs[wf_ssa_def] >>
      qexistsl [`db`, `di`, `v`] >> simp[])
  >- simp[le_chain_valid_def]
  >- simp[le_chain_valid_def]
QED

Theorem le_occ_available_normalize_eval:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ i.inst_opcode <> PHI /\
  (!v. op = Var v ==> def_available_at fn bb (SOME i) v) ==>
  eval_operand (normalize_operand (dfg_build_function fn) visited op) s =
  eval_operand op s
Proof
  strip_tac >> irule le_chain_valid_eval >>
  irule le_occ_available_chain_valid >> metis_tac[]
QED

Theorem le_frame_use_chain_valid:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  frame_reach C fn s0 i s /\ i.inst_opcode <> PHI /\ MEM op i.inst_operands ==>
  le_chain_valid (dfg_build_function fn) visited op s
Proof
  strip_tac >> drule_all le_occ_prefix_annotate >> strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_inst_lookup >> strip_tac >>
  `MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  `!v. op = Var v ==> def_available_at fn bb (SOME i) v` by
    (rpt strip_tac >> gvs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  metis_tac[le_occ_available_chain_valid]
QED

Theorem le_frame_use_normalize_eval:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  frame_reach C fn s0 i s /\ i.inst_opcode <> PHI /\ MEM op i.inst_operands ==>
  eval_operand (normalize_operand (dfg_build_function fn) visited op) s =
  eval_operand op s
Proof
  strip_tac >> irule le_chain_valid_eval >>
  irule le_frame_use_chain_valid >> metis_tac[]
QED
