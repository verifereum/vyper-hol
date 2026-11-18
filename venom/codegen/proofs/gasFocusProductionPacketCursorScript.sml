Theory gasFocusProductionPacketCursor
Ancestors
  gasFocusPacketPipelineStages gasFocusPacketEntryCursor
  o1PipelineCorrect o1PassContract o1PassLift unitTransformDefs
  venomPassSchedule venomPipelineRunner venomFnScheduleRunner
  fcgPruning irSupply dftDefs dftFinitePacket dftGasFromListTraceDefs
  frameJointTrace frameJointTransition venomWf venomInst venomState finite_map list

(* Choose the stage family and CFG schedules before the runtime horizon. *)
Theorem focus_production_packet_cursor:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit.cu_context.ctx_entry = SOME nm /\ o1_run_state_ok vs0 ==>
  ?pre t t' stage sf lbl7 schedules.
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
        let tf = dft_fn sf;
            E = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|>;
            inst = HD bt.bb_instructions;
            i9 = HD (HD f9.fn_blocks).bb_instructions
        in
        let q80 = JointConfig [] [] FEMPTY entry_taint tf inst E [] FEMPTY []
              [OriginInitial E; OriginObserve (OriginSnapshot tf [] FEMPTY FEMPTY inst E)];
            q9 = JointConfig [] [] FEMPTY entry_taint f9 i9 E [] FEMPTY []
              [OriginInitial E; OriginObserve (OriginSnapshot f9 [] FEMPTY FEMPTY i9 E)];
            T = dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) tf E;
            body_entry = if phi_prefix_length bt.bb_instructions < LENGTH ps
                         then NONE else SOME (E,0)
        in
        let ms = if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs else [];
            es = if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) xs else [];
            ks = if IS_SOME body_entry then
                   MAP (\i. if i.inst_opcode = GAS then [([],1,i.inst_id)] else []) xs else []
        in
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
  strip_tac >> drule_all focus_packet_pipeline_stages >> strip_tac >>
  rename1 `run_pipeline_stages _ _ _ _ = SOME (pre,t)` >>
  rename1 `run_callee_first _ _ _ _ _ = SOME (_,t')` >>
  rename1 `o1_pre 7 (stage 7) (stage 8)` >>
  `MEM nm (MAP (\f. f.fn_name) (stage 7).ctx_functions)` by
    (qpat_assum `o1_ctx_shape (stage 7)`
       (strip_assume_tac o REWRITE_RULE [o1_ctx_shape_def, ctx_wf_def, ctx_has_entry_def]) >>
     gvs[ctx_fn_names_def]) >>
  `?sf. lookup_function nm (stage 7).ctx_functions = SOME sf` by
    (Cases_on `lookup_function nm (stage 7).ctx_functions` >>
     simp[] >> drule lookup_function_not_mem >> simp[]) >>
  rename1 `lookup_function nm (stage 7).ctx_functions = SOME sf` >>
  `MEM sf (stage 7).ctx_functions` by drule_then ACCEPT_TAC lookup_function_MEM >>
  `sf.fn_blocks <> []` by
    (qpat_assum `o1_ctx_shape (stage 7)`
       (strip_assume_tac o REWRITE_RULE [o1_ctx_shape_def, EVERY_MEM]) >>
     qpat_assum `!f. MEM f _ ==> o1_fn_shape _ f`
       (drule_then (strip_assume_tac o REWRITE_RULE [o1_fn_shape_def, wf_function_def, fn_has_entry_def]))) >>
  `?lbl7. fn_entry_label sf = SOME lbl7` by
    (Cases_on `sf.fn_blocks` >> fs[fn_entry_label_def, entry_block_def]) >>
  rename1 `fn_entry_label sf = SOME lbl7` >>
  drule_all focus_packet_entry_cursor >> disch_then (qx_choose_then `schedules` assume_tac) >>
  qexistsl [`pre`,`t`,`t'`,`stage`,`sf`,`lbl7`,`schedules`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `N` >> strip_tac >>
  `code_layout_valid vs0 /\ vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  qpat_x_assum `!base N nm sf lbl. _` drule_all >>
  qpat_assum `stage 9 = out.po_unit.cu_context` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms, joint_trace_def, joint_chain_def, SF CONJ_ss]
QED
