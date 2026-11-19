Theory gasFocusProductionPacketCursorStatic
Ancestors
  gasFocusPacketEntryCursor o1DftStageSsa o1ContractCfgNormJointCursors
  o1PassContract o1PassLift unitTransformDefs venomPassSchedule
  venomPipelineRunner venomFnScheduleRunner venomPassDispatcher fcgPruning irSupply
  dftDefs dftRunRel dftFinitePacket dftGasFromListTraceDefs lowerDloadDefs
  frameJointTrace frameJointTransition venomWf venomInst venomState finite_map list

Theorem packet_walk_entry[local]:
  (!k. k < n ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
     (stage k) (stage (SUC k))) ==>
  !k. k <= n ==> (stage k).ctx_entry = (stage 0).ctx_entry
Proof
  disch_tac >> Induct >- simp[] >> strip_tac >>
  rename1 `SUC k <= n` >>
  `k < n /\ k <= n` by decide_tac >>
  qpat_assum `!j. j < n ==> _` (qspec_then `k` mp_tac) >>
  simp[ctx_pass_stage_def]
  >> (gvs[o1PassContractTheory.ctx_pass_stage_def])
QED

Theorem packet_stage_any_view[local]:
  ctx_pass_stage rp pass view C C' ==> ctx_pass_stage rp pass any_view C C'
Proof
  simp[ctx_pass_stage_def, any_view_def, LIST_REL_EL_EQN] >>
  rpt strip_tac >>
  qpat_assum `!i. i < LENGTH _ ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem packet_root_lookup[local]:
  o1_ctx_shape C /\ C.ctx_entry = SOME nm ==>
  ?sf lbl. lookup_function nm C.ctx_functions = SOME sf /\
           fn_entry_label sf = SOME lbl
Proof
  simp[o1_ctx_shape_def, ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def] >>
  strip_tac >> Cases_on `lookup_function nm C.ctx_functions`
  >- gvs[lookup_function_not_mem] >>
  rename1 `lookup_function nm C.ctx_functions = SOME sf` >>
  drule_then assume_tac lookup_function_MEM >>
  qpat_assum `EVERY (o1_fn_shape C) _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `sf` mp_tac) >>
  simp[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
  Cases_on `sf.fn_blocks` >> simp[fn_entry_label_def, entry_block_def]
QED

(* The supplied walk fixes stages 7--9. Choose its entry and schedules before N. *)
Theorem focus_production_packet_cursor_static:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rp o1_fn_passes (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\ EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 ==>
  ?sf lbl7 schedules.
    (stage 7).ctx_entry = SOME nm /\
    ctx_pass_stage rp (CFP_Simple VP_DFT) any_view (stage 7) (stage 8) /\
    ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) any_view (stage 8) (stage 9) /\
    o1_pre 7 (stage 7) (stage 8) /\
    o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8) /\ o1_ctx_shape (stage 9) /\
    EVERY wf_ssa (stage 7).ctx_functions /\ EVERY wf_ssa (stage 8).ctx_functions /\
    lookup_function nm (stage 7).ctx_functions = SOME sf /\
    fn_entry_label sf = SOME lbl7 /\
    !N. 0 < N ==>
      ?bb bt ps xs ys rho f9 current rooted_eval.
        ?tf. tf = dft_fn sf /\
        ?E. E = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
        ?inst. inst = HD bt.bb_instructions /\
        ?i9. i9 = HD (HD f9.fn_blocks).bb_instructions /\
        ?q80. q80 = JointConfig [] [] FEMPTY entry_taint tf inst E [] FEMPTY []
              [OriginInitial E; OriginObserve (OriginSnapshot tf [] FEMPTY FEMPTY inst E)] /\
        ?q9. q9 = JointConfig [] [] FEMPTY entry_taint f9 i9 E [] FEMPTY []
              [OriginInitial E; OriginObserve (OriginSnapshot f9 [] FEMPTY FEMPTY i9 E)] /\
        ?T. T = dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) tf E /\
        ?body_entry. body_entry = (if phi_prefix_length bt.bb_instructions < LENGTH ps
                         then NONE else SOME (E,0)) /\
        ?ms. ms = (if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs else []) /\
        ?es. es = (if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) xs else []) /\
        ?ks. ks = (if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [([],1,i.inst_id)] else []) xs else []) /\
          (stage 8).ctx_entry = SOME nm /\
          lookup_function nm (stage 8).ctx_functions = SOME tf /\
          fn_entry_label tf = SOME lbl7 /\ dft_fn_rel sf tf /\
          lookup_block lbl7 sf.fn_blocks = SOME bb /\ lookup_block lbl7 tf.fn_blocks = SOME bt /\
          bb.bb_label = lbl7 /\ bt.bb_label = lbl7 /\
          bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
          joint_initial vs0 (stage 8) q80 /\ joint_trace vs0 (stage 8) q80 [] [] q80 /\
          dftGasFromListTraceDefs$trace_context N (stage 8) vs0 = T /\
          (?tail. T = (([],1,inst.inst_id),tf,inst,E)::tail) /\
          0 < LENGTH T /\ EL 0 T = (([],1,inst.inst_id),tf,inst,E) /\
          TAKE 0 T = [] /\ LENGTH (TAKE 0 T) = 0 /\
          dftGasFromListTraceDefs$trace_gas (TAKE 0 T) = [] /\
          dft_focus_packet_rel N (stage 7) (stage 8) sf tf E (0,[])
            (FEMPTY |+ ([],(sf,tf,0,E,[1],NONE,NONE)))
            (FEMPTY |+ (([],1),(bb,bt,ps,xs,ys,rho,E,0,body_entry,0,OK E,F,NONE)))
            FEMPTY (FEMPTY |+ (([],1),ms)) (FEMPTY |+ (([],1),es))
            (FEMPTY |+ (([],1),ks)) rooted_eval [] 1 q80 (FLAT ms) (FLAT es)
            E.vs_gas_readings /\
          out.po_unit.cu_context.ctx_entry = SOME nm /\
          lookup_function nm out.po_unit.cu_context.ctx_functions = SOME f9 /\
          fn_entry_label f9 = SOME lbl7 /\ joint_initial vs0 out.po_unit.cu_context q9 /\
          joint_trace vs0 out.po_unit.cu_context q9 [] [] q9 /\
          cfg_norm_joint_cursors (stage 8) out.po_unit.cu_context (schedules,current,[]) q80 q9
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) >>
  strip_tac >>
  drule packet_walk_entry >>
  disch_then (qspec_then `7` (assume_tac o SRULE [prune_unit_fcg_unreachable_fields])) >>
  `(stage 7).ctx_entry = SOME nm` by fs[prune_unit_fcg_unreachable_fields] >>
  qpat_assum `!k. k < 9 ==> _` (fn th =>
    map_every (fn k => qspec_then k
      (assume_tac o MATCH_MP packet_stage_any_view o SRULE [o1_fn_passes_def]) th)
      [`7`,`8`]) >>
  qpat_assum `!k. k <= 9 ==> _` (fn th =>
    map_every (fn k => qspec_then k (strip_assume_tac o SRULE []) th) [`7`,`8`,`9`]) >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `EVERY wf_ssa (stage 7).ctx_functions` by
    (qpat_assum `EVERY (o1_fn_row 7) _`
       (mp_tac o SRULE [EVERY_MEM, o1_fn_row_def]) >> simp[EVERY_MEM]) >>
  drule_all_then assume_tac dft_stage_wf_ssa >>
  drule_all packet_root_lookup >>
  disch_then (qx_choosel_then [`sf`,`lbl7`] strip_assume_tac) >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) focus_packet_entry_cursor) >>
  disch_then (qx_choose_then `schedules` assume_tac) >>
  qexistsl [`sf`,`lbl7`,`schedules`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `N` >> strip_tac >>
  `vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted` by fs[o1_initial_state_ok_def] >>
  qpat_x_assum `!base N nm sf lbl. _` drule_all >>
  qpat_assum `stage 9 = out.po_unit.cu_context` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms, joint_trace_def, joint_chain_def, SF CONJ_ss]
QED
