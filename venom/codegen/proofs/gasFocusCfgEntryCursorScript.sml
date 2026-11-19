Theory gasFocusCfgEntryCursor
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNorm o1PassContract o1PassLift
  cfgNormDefs frameJointTransition contextCodegenRel venomExecSemantics
  venomInst venomState venomWf list option finite_map

(* Select the normalization schedules before the runtime root. *)
Theorem focus_cfg_entry_cursor:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions /\ o1_ctx_shape C9 ==>
  ?schedules. !base q8 nm f8 lbl.
    base.vs_vars = FEMPTY /\ ~base.vs_halted /\ joint_initial base C8 q8 /\
    C8.ctx_entry = SOME nm /\ lookup_function nm C8.ctx_functions = SOME f8 /\
    fn_entry_label f8 = SOME lbl ==>
    ?f9 current.
      ?E. E = base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
      ?i9. i9 = HD (HD f9.fn_blocks).bb_instructions /\
      ?q9. q9 = JointConfig [] [] FEMPTY entry_taint f9 i9 E [] FEMPTY []
        [OriginInitial E; OriginObserve (OriginSnapshot f9 [] FEMPTY FEMPTY i9 E)] /\
      C9.ctx_entry = SOME nm /\ lookup_function nm C9.ctx_functions = SOME f9 /\
      fn_entry_label f9 = SOME lbl /\ joint_initial base C9 q9 /\
      cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q8 q9
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) >>
  strip_tac >> drule_all cfg_norm_joint_cursors_initial >>
  disch_then (qx_choose_then `schedules` (mk_asm "cursor")) >>
  drule cfg_norm_stage_functions >> strip_tac >>
  qpat_assum `LIST_REL _ C8.ctx_functions C9.ctx_functions`
    (mp_then Any mp_tac list_rel_lookup_function) >>
  (impl_tac >- (rpt strip_tac >> metis_tac[cfg_norm_function_supply_identity])) >>
  disch_then (mk_asm "lookup") >>
  qexists `schedules` >> qx_gen_tac `root` >> rpt strip_tac >>
  asm_x "lookup" (qspec_then `nm` mp_tac) >> simp[OPTREL_def] >>
  Cases_on `lookup_function nm C9.ctx_functions` >> simp[OPTREL_def] >>
  strip_tac >> rename1 `lookup_function nm C9.ctx_functions = SOME f9` >>
  `fn_entry_label f9 = SOME lbl` by metis_tac[cfg_norm_function_supply_identity] >>
  `o1_fn_shape C9 f9` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  qmatch_goalsub_abbrev_tac `OriginInitial E` >>
  qmatch_goalsub_abbrev_tac `joint_initial root C9 q9` >>
  `enters_block f9 E E /\ active_inst f9 (HD (HD f9.fn_blocks).bb_instructions) E` by
    (Cases_on `f9.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
     rename1 `f9.fn_blocks = bb::bbs` >>
     `bb.bb_instructions <> []` by
       gvs[o1_fn_shape_def, wf_function_def, bb_well_formed_def] >>
     Cases_on `bb.bb_instructions` >>
     gvs[o1_fn_shape_def, first_block_no_phi_def] >>
     conj_tac
     >- (simp[enters_block_def, Abbr `E`] >> qexists `bb` >>
         simp[lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def]) >>
     simp[active_inst_def, Abbr `E`] >> qexists `bb` >> simp[]) >>
  `joint_initial root C9 q9` by
    (simp[Abbr `q9`, Abbr `E`] >> irule joint_initial_rules >>
     simp[] >> qexists `nm` >> simp[]) >>
  simp[] >> asm_x "cursor" (qspecl_then [`root`,`q8`,`q9`] mp_tac) >> simp[]
QED
