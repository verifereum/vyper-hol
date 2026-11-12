(* INVOKE identity at its post-restore control position. *)
Theory fmpCoverInvokeIndex
Ancestors
  fmpStageControl fmpStageControlWalk fmpLowerIndexedProps fmpLowerDefs
  fmpStageRel fmpStepRewrite venomInst venomFnInstsProofs o1PassContract
  finite_map list rich_list arithmetic

Theorem fmp_cover_walk_invoke_head[local]:
  fmp_lower_indexed infos ctx runner lbl k s rs (inst::xs) = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  inst.inst_opcode = INVOKE ==>
  (if (lbl,k) IN FDOM plan then 1 else 0) < LENGTH out /\
  (EL (if (lbl,k) IN FDOM plan then 1 else 0) out).inst_opcode = INVOKE /\
  (EL (if (lbl,k) IN FDOM plan then 1 else 0) out).inst_id = inst.inst_id
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  `?j. head = [j] /\ j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id` by
    (qpat_x_assum `fmp_lower_inst _ _ _ _ _ = _` mp_tac >>
     simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  gvs[] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST1_TAC o GSYM) >>
  simp[EL_APPEND_EQN]
QED

Theorem fmp_cover_invoke_index:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ i = EL idx bb.bb_instructions /\
  i.inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    let p = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
              (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
            (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
    in p < LENGTH bb'.bb_instructions /\ j = EL p bb'.bb_instructions /\
       j.inst_opcode = INVOKE /\ j.inst_id = i.inst_id
Proof
  rpt strip_tac >> gvs[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (qpat_x_assum `fn.fn_fmp_signature = NONE /\ _`
        (CONJUNCTS_THEN assume_tac) >> Cases_on `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
        bb.bb_label = rl ==> rp <= idx`
      >- (`idx <= LENGTH bb.bb_instructions` by decide_tac >>
          drule fmp_stage_tidx_code >> simp[] >>
          disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
          simp[] >> strip_tac >>
          `DROP idx bb.bb_instructions =
            EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
            simp[DROP_CONS_EL] >>
          qpat_x_assum `DROP idx bb.bb_instructions = _` SUBST_ALL_TAC >>
          drule_all fmp_cover_walk_invoke_head >> strip_tac >>
          rename1 `lookup_block lbl fn'.fn_blocks = SOME target` >>
          qexists `target` >> simp[] >>
          qmatch_asmsub_abbrev_tac `offset < LENGTH (DROP pos bb'.bb_instructions)` >>
          `offset + pos < LENGTH bb'.bb_instructions` by fs[LENGTH_DROP] >>
          fs[EL_DROP] >> simp[ADD_COMM]) >>
      gvs[NOT_FORALL_THM] >>
      `idx < rp` by decide_tac >>
      drule fmp_control_kept_prefix >>
      disch_then (qspec_then `rp` mp_tac) >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `idx` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `target` strip_assume_tac) >>
      `SUM (GENLIST (\j. (if (bb.bb_label,j) IN FDOM (fmp_stage_plan infos ctx fn)
          then 1 else 0) +
        (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx)
        = idx` by
        (irule fmp_control_width_one >> rpt strip_tac >>
         `j <= idx` by decide_tac >>
         qpat_x_assum `!j. j <= idx ==> _` drule >> simp[]) >>
      `~((bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
        (qpat_x_assum `!j. j <= idx ==> _` (qspec_then `idx` mp_tac) >> simp[]) >>
      qexists `target` >> simp[fmp_stage_tidx_def]) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  drule_all fmp_control_unlowered_no_raw >> strip_tac >>
  `!j. j < idx ==> (EL j bb.bb_instructions).inst_opcode <> DALLOCA` by
    (rpt strip_tac >>
     gvs[no_raw_fmp_ops_def, fn_insts_def, fn_insts_blocks_def,
         MEM_FLAT, MEM_MAP, is_raw_fmp_opcode_def] >>
     `j < LENGTH bb.bb_instructions` by decide_tac >>
     `MEM (EL j bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
       (irule mem_fn_insts_blocks >> qexists `bb` >> simp[EL_MEM]) >>
     first_x_assum drule >> simp[is_raw_fmp_opcode_def]) >>
  `SUM (GENLIST (\j. (if (lbl,j) IN FDOM (FEMPTY:fmp_reclaim_plan) then 1 else 0) +
    (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx) = idx` by
    (irule fmp_control_width_one >> simp[]) >>
  qexists `bb` >> simp[fmp_stage_tidx_def] >> gvs[]
QED
