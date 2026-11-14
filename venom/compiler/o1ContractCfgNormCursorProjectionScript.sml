Theory o1ContractCfgNormCursorProjection
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNorm cfgNormSupplySim cfgNormDefs
  o1PassLift simplifyCfgSimTools venomExecSemantics venomExecProofs
  venomInst venomState venomWf unitShapeDefs unitMemInv contextCodegenRel
  stateFrame ctxLookupAgreeHelpers list rich_list pair option

Theorem cfg_norm_cursors_head_projection[local]:
  cfg_norm_cursors C
    ((s,fn,meta)::(s1,next_fn,meta1)::rounds)
    (((inst,a),pending)::((next,v),other)::cursors) ==>
  mem_corr inst a next v /\ call_corr inst a next v /\
  (inst_mem_ranges next v <> [] /\ ~in_revert_forward next_fn v ==>
    ~in_revert_forward fn a)
Proof
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[]
  >- (`fn_inst_wf fn /\ wf_function fn /\ ir_supply_covers_fn s fn /\
       ir_supply_inst_ok s` by gvs[supply_norm_inv_def] >>
      `inst_wf (EL v.vs_inst_idx bb.bb_instructions)` by
        metis_tac[active_inst_wf] >>
      `EVERY label_positions_ok bb.bb_instructions` by
        (gvs[fn_insts_def, EVERY_MEM] >> metis_tac[MEM_fn_insts_blocks]) >>
      `label_positions_ok (EL v.vs_inst_idx bb.bb_instructions)` by
        metis_tac[EVERY_EL] >>
      `mem_corr (EL v.vs_inst_idx bb.bb_instructions) a
         (EL v.vs_inst_idx
           (supply_block_image pred target split repls bb).bb_instructions) v /\
       call_corr (EL v.vs_inst_idx bb.bb_instructions) a
         (EL v.vs_inst_idx
           (supply_block_image pred target split repls bb).bb_instructions) v` by
        (irule supply_body_cursor_projection >> simp[] >> metis_tac[]) >>
      simp[] >> strip_tac >> CCONTR_TAC >> gvs[] >>
      drule_all supply_body_cursor_revert_forward >> simp[]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by gvs[supply_norm_inv_def] >>
  `MEM (EL v.vs_inst_idx split.bb_instructions).inst_opcode [ASSIGN; JMP]` by
    (drule_all supply_split_index_shape >> gvs[] >> metis_tac[]) >>
  `inst_mem_ranges (EL v.vs_inst_idx split.bb_instructions) v = []` by
    (irule supply_inst_mem_ranges_empty >> gvs[]) >>
  gvs[mem_corr_def, call_corr_def, supply_state_agree_def, execution_frame_def]
QED

Theorem cfg_norm_cursors_projection:
  !rounds C cursors s f meta t g i a pending j v.
  cfg_norm_cursors C rounds cursors /\
  HD rounds = (s,f,meta) /\ LAST rounds = (t,g,NONE) /\
  HD cursors = ((i,a),pending) /\ LAST cursors = ((j,v),NONE) ==>
  mem_corr i a j v /\ call_corr i a j v /\
  (inst_mem_ranges j v <> [] /\ ~in_revert_forward g v ==>
    ~in_revert_forward f a)
Proof
  Induct_on `rounds`
  >- (rpt strip_tac >> drule cfg_norm_cursors_lengths >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `cursors <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors` >> gvs[] >> Cases_on `rounds`
  >- (gvs[] >>
      qpat_x_assum `cfg_norm_cursors C [_] (_::_)` mp_tac >>
      simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
      rename1 `supply_norm_inv final_supply final_fn` >>
      rename1 `active_inst final_fn final_inst final_state` >>
      `fn_inst_wf final_fn` by gvs[supply_norm_inv_def] >>
      `inst_wf final_inst` by metis_tac[active_inst_wf] >>
      simp[supply_mem_corr_refl, supply_call_corr_refl]) >>
  gvs[] >>
  rename1 `cfg_norm_cursors C ((s,f,meta)::middle_round::rest)
    (((i,a),pending)::tail)` >>
  `cfg_norm_cursors C (middle_round::rest) tail` by
    metis_tac[cfg_norm_cursors_tail, NOT_CONS_NIL] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `tail` >> gvs[] >>
  rename1 `cfg_norm_cursors C ((s,f,meta)::middle_round::rest)
    (((i,a),pending)::middle_cursor::remaining)` >>
  PairCases_on `middle_round` >> PairCases_on `middle_cursor` >>
  qpat_x_assum `!C cursors s f meta i a pending j v. _`
    (qspecl_then [`C`, `((middle_cursor0,middle_cursor1),middle_cursor2)::remaining`,
      `middle_round0`, `middle_round1`, `middle_round2`,
      `middle_cursor0`, `middle_cursor1`, `middle_cursor2`, `j`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  `mem_corr i a middle_cursor0 middle_cursor1 /\
   call_corr i a middle_cursor0 middle_cursor1 /\
   (inst_mem_ranges middle_cursor0 middle_cursor1 <> [] /\
    ~in_revert_forward middle_round1 middle_cursor1 ==> ~in_revert_forward f a)` by
    (drule_all cfg_norm_cursors_head_projection >> simp[]) >>
  conj_tac >- metis_tac[mem_corr_trans] >>
  conj_tac >- metis_tac[supply_call_corr_trans] >> strip_tac >>
  `inst_mem_ranges middle_cursor0 middle_cursor1 <> []` by
    (fs[mem_corr_def] >> metis_tac[]) >>
  metis_tac[]
QED
