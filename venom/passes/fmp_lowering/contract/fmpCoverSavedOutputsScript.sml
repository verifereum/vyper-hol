(* Saved call outputs: separate control identity from actual nonpublication. *)
Theory fmpCoverSavedOutputs
Ancestors
  fmpCoverObservedPublish fmpCoverInvokeOrigin fmpStageRel fmpLowerProps
  fmpStepLayout fmpLowerDefs
  o1PassContract ptrDiscipline concretizePtrOwnerPath
  o1ContractSimplifyCfgSrcFrame lowerDloadPtrRawReachable
  contextCodegenRel venomExecSemantics venomWf venomInst
  mem2varProofs venomFnInstsProofs finite_map list

Theorem fmp_cover_saved_outputs:
  (!infos ctx runner fn fn' lbl bb idx i.
    fmp_stage_lowered infos ctx runner fn fn' /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\ i = EL idx bb.bb_instructions /\
    i.inst_opcode = INVOKE ==>
    ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
      let p = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
                (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
              (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      in p < LENGTH bb'.bb_instructions /\ j = EL p bb'.bb_instructions /\
         j.inst_opcode = INVOKE /\ j.inst_id = i.inst_id) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
  active_inst fc' ivk' tc ==>
  ivk'.inst_outputs = f.cf_inst.inst_outputs
Proof
  strip_tac >>
  drule scfg_frame_reachable_functions >> simp[] >> strip_tac >>
  drule ptr_owner_frame_active >> simp[] >> strip_tac >>
  `wf_function f.cf_fn` by
    (fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[]) >>
  `ALL_DISTINCT (fn_labels f.cf_fn)` by fs[wf_function_def] >>
  `?bb. lookup_block f.cf_state.vs_current_bb f.cf_fn.fn_blocks = SOME bb /\
        get_instruction bb f.cf_state.vs_inst_idx = SOME f.cf_inst` by
    metis_tac[active_inst_block_lookup] >>
  `?infos ctx runner.
     fmp_stage_lowered infos ctx runner f.cf_fn fc' /\
     tc.vs_current_bb = f.cf_state.vs_current_bb /\
     tc.vs_inst_idx =
       fmp_stage_tidx (fmp_stage_plan infos ctx f.cf_fn)
         (fmp_stage_root infos ctx f.cf_fn) f.cf_state.vs_current_bb
         bb.bb_instructions f.cf_state.vs_inst_idx +
       (if (f.cf_state.vs_current_bb,f.cf_state.vs_inst_idx) IN
             FDOM (fmp_stage_plan infos ctx f.cf_fn) then 1 else 0)` by
    (fs[fmp_stage_rel_def, fmp_saved_rel_def, fmp_frame_rel_def] >>
     metis_tac[]) >>
  `f.cf_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   f.cf_inst = EL f.cf_state.vs_inst_idx bb.bb_instructions` by
    fs[get_instruction_def] >>
  first_x_assum (drule_at (Pat `fmp_stage_lowered _ _ _ _ _`)) >>
  disch_then drule_all >> simp[] >> strip_tac >>
  `ALL_DISTINCT (fn_labels fc')` by
    (`?sp sp'. fmp_lower_function ctx sp f.cf_fn = SOME (fc',sp')` by
       (fs[fmp_stage_lowered_def, fmp_lower_function_def] >> metis_tac[]) >>
     drule fmp_lower_function_preserves_labels >> simp[]) >>
  `get_instruction bb' tc.vs_inst_idx = SOME ivk'` by
    (drule_all active_inst_block_lookup >> strip_tac >> gvs[]) >>
  `ivk'.inst_opcode = INVOKE /\ ivk'.inst_id = f.cf_inst.inst_id` by
    (fs[get_instruction_def, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  drule_all fmp_cover_actual_nonpublish >> strip_tac >>
  `MEM ivk' (fn_insts fc')` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  drule_all fmp_cover_invoke_origin >> strip_tac >>
  `MEM f.cf_inst (fn_insts f.cf_fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `i = f.cf_inst` by metis_tac[wf_fn_inst_id_inj] >>
  gvs[]
QED
