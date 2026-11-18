Theory gasFocusJointInitial
Ancestors
  gasFocusProductionPacketCursor gasFocusFalseCodegenContext
  gasFocusPlainFrameInitial gasFocusOptStaticAssembly gasFocusOptLabelFlow
  fnFrameSymbolicPrefix fnFramePrefixDriver codegenSymRel asmDataEnv asmSymSem
  codegenEntryRel asmFrameRel asmSem asmOptimizer symbolResolve
  o1PipelineCorrect o1PassContract o1PassLift unitTransformDefs
  venomPassSchedule venomPipelineRunner venomFnScheduleRunner fcgPruning irSupply
  dftDefs dftFinitePacket dftGasFromListTraceDefs o1ContractCfgNormJointCursors
  frameJointTrace frameJointTransition unitShapeDefs stackPlanGen contextCodegenRel
  venomWf venomInst venomState finite_map list pred_set words

(* Attach the applicable frame to the CFG cursor's own initial configuration. *)
Theorem focus_joint_initial:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit.cu_context.ctx_entry = SOME nm /\ o1_run_state_ok vs0 /\
  unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rp out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
     label_flow_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) es0 ==>
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
          cfg_norm_joint_cursors (stage 8) out.po_unit.cu_context (schedules,current,[]) q80 q9 /\
          (fin = K SOME ==>
             normal_frame_plan rp out.po_unit cpl prog
               (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                           vs_return_pc_token := 0w; vs_inst_idx := 0|>)
               es0 q9 (entry_asm_state vs0 es0)) /\
          (fin = asm_opt_finalizer ==>
             normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
               rp out.po_unit cpl prog vs0 es0 q9 (entry_asm_state vs0 es0)
               (sym_init (entry_asm_state vs0 es0)))
Proof
  strip_tac >>
  drule_all_then assume_tac focus_false_codegen_context >>
  drule_all focus_production_packet_cursor >>
  disch_then (qx_choosel_then [`pre`,`t`,`t'`,`stage`,`sf`,`lbl7`,`schedules`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`pre`,`t`,`t'`,`stage`,`sf`,`lbl7`,`schedules`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `N` >> strip_tac >>
  qpat_x_assum `!N. 0 < N ==> _` (qspec_then `N` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`bb`,`bt`,`ps`,`xs`,`ys`,`row_map`,`f9`,`current`,`rooted_eval`]
    (map_every assume_tac o CONJUNCTS o
      CONV_RULE (TOP_DEPTH_CONV (REWR_CONV LET_THM THENC BETA_CONV)))) >>
  qexistsl [`bb`,`bt`,`ps`,`xs`,`ys`,`row_map`,`f9`,`current`,`rooted_eval`] >>
  CONV_TAC (TOP_DEPTH_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (disch_tac >>
      `prog' = prog` by fs[combinTheory.K_THM] >>
      `(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
         entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
      `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0` by
        fs[] >>
      irule focus_plain_frame_initial >> simp[]) >>
  disch_tac >>
  qpat_assum `fin = asm_opt_finalizer ==> _` (fn th =>
    mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) >>
  drule_all_then assume_tac focus_opt_label_flow >>
  drule_all_then strip_assume_tac focus_opt_static_assembly >>
  irule normal_frame_symbolic_initial >> simp[focus_s7_symbolic_context_def]
QED
