Theory gasFocusSourceProvider
Ancestors
  gasFocusSourceStages
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic
  o1CodeEndSourceCutTransport o1ComposeSupport o1PipelineCompose simplifyCfgDefs
  makeSsaDefs o1ContractSimplifyCfg

Theorem focus_opt_c1_section[local]:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context C1 /\
  EVERY make_ssa_input_ok
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  o1_initial_state_ok V /\
  (!fn i s. raw_reachable V unit.cu_context fn i s /\ gas_cut n V s ==>
             inst_dload_in_section i s) /\
  (!fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands) ==>
  mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section) C1 V /\
  (!fn i. MEM fn C1.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn))
    unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[EVERY_MEM, unit_defs_reach_uses_def, o1_ctx_shape_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section)
    unit.cu_context V` by
    (simp[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]) >>
  gvs[o1_initial_state_ok_def] >>
  irule code_end_source_prefix_transport_upto >>
  metis_tac[init_ir_supply_inst_ok]
QED

Theorem focus_row_visit_inverse[local]:
  !xs be.
    DROP be.vs_inst_idx bt.bb_instructions = xs /\
    MEM ((a,e,i.inst_id),tf,i,t)
      (trace_block a e fuel C tf bt be) ==>
    ?pre rest. xs = pre ++ i::rest /\
      t.vs_inst_idx = be.vs_inst_idx + LENGTH pre /\
      EVERY (\x. ~is_terminator x.inst_opcode) pre /\
      FOLDR (dft_exec_cons fuel C) OK pre be = OK t
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bt.bb_instructions <= be.vs_inst_idx` by
        (gvs[GSYM LENGTH_NIL, LENGTH_DROP]) >>
      fs[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP be.vs_inst_idx bt.bb_instructions = head::xs` >>
  `be.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_assum `DROP _ _.bb_instructions = _::_`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[NoAsms, LENGTH_DROP]) >>
  `get_instruction bt be.vs_inst_idx = SOME head /\
   DROP (SUC be.vs_inst_idx) bt.bb_instructions = xs` by
    (drule DROP_BY_DROP_SUC >> simp[get_instruction_def]) >>
  drule_then assume_tac trace_block_visit >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  asm_rewrite_tac[MEM, MEM_APPEND, pairTheory.PAIR_EQ] >> strip_tac
  >- (gvs[] >> qexistsl [`[]`,`xs`] >> simp[])
  >- (`MEM (a,e,i.inst_id) (MAP FST (trace_step a e fuel C tf head be))` by
        (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      metis_tac[dftGasFromListTraceNamesTheory.trace_step_not_root]) >>
  Cases_on `step_inst fuel C head be` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  rename1 `step_inst fuel C head be = OK post` >>
  qpat_x_assum `!s. DROP _ _ = _ /\ MEM _ _ ==> _`
    (qspec_then `post with vs_inst_idx := SUC be.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`head::pre`,`rest`] >> simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

(* A child frame keeps its call site throughout the child's trace. Changing
   the selected instruction ID does not move that frame to another site. *)
Theorem focus_child_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_step P D fuel C f head s) /\
  ~MEM head.inst_id (MAP (\x. x.inst_id) (DROP post.vs_inst_idx bb.bb_instructions)) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_block P D fuel C f bb post)
Proof
  rpt strip_tac >>
  drule (REWRITE_RULE [EVERY_MEM] (cj 1 dftGasFromListTraceNamesTheory.trace_regions)) >>
  simp[] >> strip_tac >>
  `block_region P D [head.inst_id] (p,d,id')` by
    (irule dftGasFromListTraceNamesTheory.below_call_region >> simp[] >>
     qexists `head.inst_id` >> simp[]) >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >> strip_tac >>
  metis_tac[dftGasFromListTraceNamesTheory.block_regions_disjoint, MEM]
QED

Theorem focus_later_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_block P D fuel C f bb s) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_blocks P D fuel C f post)
Proof
  rpt strip_tac >>
  drule dftGasFromListTraceNamesTheory.trace_blocks_region >> simp[] >> strip_tac >>
  `later_region P D (p,d,id)` by
    fs[dftGasFromListTraceNamesTheory.later_region_def] >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >>
  metis_tac[dftGasFromListTraceNamesTheory.block_later_disjoint]
QED

Theorem focus_row_continuations[local]:
  (!P D fuel C f inst s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_step P D fuel C f inst s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions) /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_block P D fuel C f bb s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_row_continuations[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]
QED

Resume focus_row_continuations[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> qexists_tac `bb` >> qexists_tac `[]` >> simp[]) >>
  rename1 `SUC k` >>
  gvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP k (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, MEM_APPEND] >>
      Cases_on `step_inst fuel C head s` >> gvs[Abbr `tail`] >>
      rename1 `step_inst _ _ _ _ = OK post` >>
      Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
      irule focus_child_row_excludes >>
      `ALL_DISTINCT (MAP (\x. x.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))` by
        (rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
      qpat_assum `get_instruction bb s.vs_inst_idx = SOME head`
        (mp_tac o MATCH_MP dftGasFromListTraceNamesTheory.remaining_ids_step) >>
      strip_tac >> gvs[] >>
      `MEM ((p,d,i.inst_id),fn,i,t) (trace_step P D fuel C f head s)` by
        (simp[MEM_EL] >> qexists `k` >> simp[]) >>
      goal_assum $ drule_at Any >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume focus_row_continuations[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND, Abbr `start`] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP h (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, ADD_CLAUSES, MEM_APPEND] >>
      Cases_on `exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[Abbr `tail`] >>
      rename1 `exec_block _ _ _ _ = OK post` >>
      Cases_on `post.vs_halted` >> gvs[] >>
      metis_tac[focus_later_row_excludes, MEM_EL]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2, ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise focus_row_continuations[local]

Theorem focus_row_continuation[local]:
  !P D fuel C f s h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)
Proof
  ACCEPT_TAC (cj 3 focus_row_continuations)
QED

(* Scratch statement for elaboration and independent review.
   Use the actual stopped six tables and their C8 chronology. Split a
   compatible raw at Mcut, with the unread suffix and [0w] as tail.
   The bounded lowered-memory conclusion is separate from the original
   conditional static-memory clause. *)
Theorem focus_source_cut_provider:
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
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
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) ==>
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
          EL q xs = inst8 /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward tf visit_state ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst.inst_opcode ==>
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
      u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?f7 f extra.
      MAP project (gas_events_blocks f unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w];
        vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf (raw ++ [0w]) ++ extra /\
      (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) <= LENGTH (gas_events_blocks f7 (stage
        7) root_sf (root_entry with vs_gas_readings := raw ++ [0w])) /\
      TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f7 (stage 7)
        root_sf (root_entry with vs_gas_readings := raw ++ [0w])) =
        TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f
          unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
          vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  sg `mem_inv (\ctx fn inst u.
         gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail)))
           (root_entry with vs_gas_readings := gs ++ tail) u ==>
         lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
       (stage 7) (root_entry with vs_gas_readings := gs ++ tail)`
  >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH
          (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM] focus_source_stages_cut))))) >> cheat) >>
  cheat
QED

Theorem focus_history_source_slice[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks
    q z cuts levels Mcut F gs tail events u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  ALL_DISTINCT (MAP FST obs) /\
  ALL_DISTINCT (FLAT (TAKE q ks)) /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
  ?Mbefore gpre vals.
    Mcut = Mbefore ++ FLAT (TAKE q ms) /\ gs = gpre ++ vals /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) vals /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := vals ++ tail) = OK u /\
    trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
        (be with vs_gas_readings := vals ++ tail)) = ZIP (FLAT (TAKE q ks),vals)
Proof
  rpt gen_tac >> strip_tac >>
  `!q. LIST_REL (\key slot. slot = ALOOKUP obs key)
        (FLAT (TAKE q ks)) (FLAT (TAKE q ms))` by
    (drule_all dft_packet_retained_prefix_lookup >> simp[]) >>
  `ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     conj_tac >-
       (qpat_assum `(j,obs) = _` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\ FLOOKUP es_tab (a,e) = _ /\
        FLOOKUP ks_tab (a,e) = _ ==> _` (mp_tac o cj 6) >>
     `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
       (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
        qpat_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        Cases_on `FLOOKUP es_tab (a,e)` >> gvs[FLOOKUP_DEF]) >>
     disch_then (drule_all_then ACCEPT_TAC)) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     pop_assum (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  `FDOM ms_tab = FDOM ms_tab` by REFL_TAC >>
  `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
    (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[LIST_REL_refl]) >>
  drule dft_packet_cut_row_trace >>
  disch_then (qspec_then `ms_tab` (drule_all_then strip_assume_tac)) >>
  rename1 `gs = gpre ++ FLAT vals` >>
  qpat_assum `FLOOKUP ms_tab (a,e) = SOME ms` (fn m =>
    qpat_assum `FLOOKUP ks_tab (a,e) = SOME ks` (fn k =>
      qpat_assum `FLOOKUP acts a = SOME _` (fn act =>
        RULE_ASSUM_TAC (REWRITE_RULE [m,k,act,optionTheory.THE_DEF,pairTheory.FST])))) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
     (FLAT (TAKE q ms)) (FLAT vals)` by
    (qpat_assum `LIST_REL _ Mcut gs` mp_tac >>
     qpat_assum `Mcut = Mbefore ++ _` (fn m =>
       qpat_assum `gs = gpre ++ FLAT vals`
         (fn g => rewrite_tac[m,g])) >>
     qpat_assum `LIST_REL _ Mbefore gpre` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     rpt strip_tac >> drule_all LIST_REL_APPEND_IMP >> simp[]) >>
  qexistsl [`Mbefore`,`gpre`,`FLAT vals`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
