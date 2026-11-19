Theory gasFocusWalkInventoryReplay
Ancestors
  gasFocusUniformStop gasFocusPacketCoverage
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
  o1ContractCfgNormCursors cfgNormSupplySim stateFrame
  gasFocusPlainGasPreEdge codegenAsmProgOk
  gasFocusGasPreEdge[qualified,ignore_grammar]
  gasFocusOptLabelFlow[qualified,ignore_grammar]
  gasFocusOptStaticAssembly[qualified,ignore_grammar]
  venomPipelineDriverProps[qualified,ignore_grammar]
  dftGasFromListUnion[qualified,ignore_grammar]
  dftGasPrefixProvider[qualified,ignore_grammar]
  dftGasToListTrace[qualified,ignore_grammar]
  dftGasFromListReadings[qualified,ignore_grammar]
  dftGasFromListTracePrefix[qualified,ignore_grammar]
  dftPacketNativeContinuation[qualified,ignore_grammar]
  dftPacketClosedRowNative[qualified,ignore_grammar]
  dftGasToListReplay[qualified,ignore_grammar]
  stateEquiv[qualified,ignore_grammar]
  dftPacketCalleeAlignment[qualified,ignore_grammar]
  dftPacketFillingBoundary[qualified,ignore_grammar]
  dftIndexedExec[qualified,ignore_grammar]
  dftPacketEntryReplay[qualified,ignore_grammar]
  venomExecProofs[qualified,ignore_grammar]
  dftRunRel[qualified,ignore_grammar]
  o1ScheduleDecompHelpers[qualified,ignore_grammar]
  venomWfProps[qualified,ignore_grammar]
  sorting[qualified,ignore_grammar]
  fnBlockBodyHelpers[qualified,ignore_grammar]
  gasFocusCutGuards[qualified,ignore_grammar]
  gasFocusSourceProvider[qualified,ignore_grammar]
  gasEventsFuel[qualified,ignore_grammar]
  gasFocusPreDftStaticAbortLift[qualified,ignore_grammar]
  finite_map list rich_list words arithmetic

(* Scratch statement for elaboration and independent review.
   The H1 hypotheses through the stage family apply to both joins. The stopped
   packet supplies the endpoint and indexed historical cuts. A pseudo-instruction
   endpoint uses the replayed pseudo prefix and zero body rows. The literal
   readiness failures use C9 non-INVOKE evaluator Error, unsuccessful
   INVOKE setup, or the empty readings at a moving GAS.
   Terminal evidence names the last C8 instruction and its root result. *)
Theorem focus_walk_stopped_selection:
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
    EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
  ?raw_slots sites unused N root_sf root_tf root_entry lbl7
    q80 q90 evs8 qs8 evs9 qs9 schedules current saved asm_fuel ast ss j obs
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8
    stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9.
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
      sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) =
        SymOK ss /\
      normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
        (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
    dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8
        oms8 om8 hs8 hist8) raw_slots sites unused /\
    j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks
      [] 0 N (stage 8) root_tf root_entry)) = j /\
    j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
      dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
      root_tf root_entry)) /\
    EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
      ((p,d,inst8.inst_id),fn8,inst8,s8) /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    (?align old_cursors old_asm old_sym costs.
      LENGTH costs = LENGTH evs9 /\ LENGTH old_asm = LENGTH evs9 /\
      (fin = asm_opt_finalizer ==> LENGTH old_sym = LENGTH evs9) /\
      align 0 = 0 /\ align (LENGTH evs9) = j /\
      asm_fuel = SUM costs /\ ast = EL (LENGTH evs9) ((entry_asm_state vs0 es0)::old_asm) /\
      (fin = asm_opt_finalizer ==> ss = EL (LENGTH evs9) (sym_init (entry_asm_state vs0 es0)::old_sym)) /\
      LIST_REL (\cost edge. 0 < cost \/
        (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
           case lookup_block s.vs_current_bb fn.fn_blocks of
             NONE => 0
           | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (SND edge) <
        (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
           case lookup_block s.vs_current_bb fn.fn_blocks of
             NONE => 0
           | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (FST edge))
        costs (ZIP (TAKE (LENGTH evs9) (q90::qs9),qs9)) /\
      (!k. k < LENGTH evs9 ==>
        align k <= j /\
        (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
        align (SUC k) <= j /\
        cfg_norm_joint_cursors (stage 8) (stage 9) (old_cursors k) (EL (align k) (q80::qs8)) (EL k
          (q90::qs9)) /\
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog (EL k costs) (EL k ((entry_asm_state vs0 es0)::old_asm)) =
            AsmOK (EL (SUC k) ((entry_asm_state vs0 es0)::old_asm)) /\
        (fin = asm_opt_finalizer ==>
          sym_steps prog (asm_data_env prog vs0.vs_code) (EL k costs) (EL k (sym_init (entry_asm_state vs0
            es0)::old_sym)) =
            SymOK (EL (SUC k) (sym_init (entry_asm_state vs0 es0)::old_sym))) /\
        (case ((EL (align k) (q80::qs8)),(EL k (q90::qs9))) of
          (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
           JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
            (~in_revert_forward fn9 s9 /\
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
      source_memory_reads_disjoint cpl inst9 s9 /\
      context_source_memory_writes_disjoint cpl inst9 s9) /\
    (fin = asm_opt_finalizer ==>
      !dst x sz src off.
        inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
        code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
        w2n (src - n2w off) < dimword (:256) DIV 2)) /\ (active_inst fn9 inst9 s9 /\
    (inst9.inst_opcode = INVOKE ==>
      ?nm' ops callee args ent.
        decode_invoke inst9 = SOME (nm',ops) /\
        lookup_function nm' (stage 9).ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
    (inst9.inst_opcode <> INVOKE ==>
      (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
      (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
            (align (SUC k) = SUC (align k) /\ i8.inst_opcode = GAS ==>
              u8.vs_gas_readings <> [])))) /\
    (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt s8.vs_inst_idx = SOME inst8 /\
        ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
          src_inst = EL (LENGTH z)
            (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
            s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
            q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
            (p <> p \/ d <> d \/ s8 <> s8 \/
              (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
               (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
            (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
               inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
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
              u.vs_initial_fmp = s8.vs_initial_fmp))) /\
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
                  u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
    ((?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\
        r8 = (case r of OK u => Halt u | other => other) /\
        ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/
         (?ex u. r = Abort ex u)) /\
        inst8.inst_opcode <> INVOKE /\
        run_blocks N (stage 8) root_tf root_entry = r8 /\
        (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
            raw_slots gs ==>
          ?extra. sites = gas_events_blocks F (stage 7) root_sf
            (root_entry with vs_gas_readings := gs ++ tail) ++ extra)) \/
      in_revert_forward fn9 s9 \/
      (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
       (~source_memory_reads_disjoint cpl inst9 s9 \/
        ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
      (fin = asm_opt_finalizer /\
        ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
          inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
          eval_operand (Var x) s9 = SOME src /\
          FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
          ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
      (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
      (inst9.inst_opcode = INVOKE /\
       ~(?callee_name ops callee args ent.
          decode_invoke inst9 = SOME (callee_name,ops) /\
          lookup_function callee_name (stage 9).ctx_functions = SOME callee /\
          eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
      (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err)) /\
    (!raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      ?rest. MAP project sites = markf (raw ++ [0w]) ++ rest)
Proof
  let
    val reduce_lets = PURE_REWRITE_CONV [LET_THM] THENC DEPTH_CONV BETA_CONV
    fun prove_conj facts goal =
      if is_conj goal then
        CONJ (prove_conj facts (lhand goal)) (prove_conj facts (rand goal))
      else
        Lib.first (fn th => aconv (concl th) goal) facts
    val fmp = Lib.first (fn tm => fst (dest_var tm) = "fmp")
      (free_vars (concl focus_uniform_frontier))
    val (_, fmp_type) = match_term fmp ``fmp:bytes32``
    val frontier = INST_TYPE fmp_type focus_uniform_frontier
    val coverage = CONV_RULE reduce_lets focus_packet_coverage
  in
    CONV_TAC reduce_lets >>
    DISCH_THEN (fn roots =>
      let
        val root_facts = CONJUNCTS roots
        val packet = MP frontier (prove_conj root_facts (lhand (concl frontier)))
        val (variables, _) = strip_exists (concl packet)
        val witnesses = map (genvar o type_of) variables
        val coverage = INST (ListPair.mapEq (op |->) (variables, witnesses)) coverage
      in
        foldr (fn (w, choose) => X_CHOOSE_THEN w choose) (fn selected =>
          let
            val selected_facts = CONJUNCTS (CONV_RULE reduce_lets selected)
            val facts = root_facts @ selected_facts
            val stop = List.last selected_facts
            val coverage_input = lhand (concl coverage)
            val coverage_stop = List.last (strip_conj coverage_input)
            val (terminal, _) = dest_disj (concl stop)
            val steps = map (genvar o type_of) (fst (strip_exists terminal))
            val weaken_terminal = foldr (fn (w, choose) => X_CHOOSE_THEN w choose)
              (fn terminal_facts => DISJ1_TAC >> MAP_EVERY EXISTS_TAC steps >>
                (fn (asl, goal) =>
                  ACCEPT_TAC (prove_conj (CONJUNCTS terminal_facts) goal) (asl, goal))) steps
            val weaken_stop = prove (mk_imp (concl stop, coverage_stop),
              DISCH_THEN (DISJ_CASES_THEN2 weaken_terminal
                (fn other => DISJ2_TAC >> ACCEPT_TAC other)))
            val covered = MP coverage (prove_conj (MP weaken_stop stop :: facts) coverage_input)
          in
            MAP_EVERY EXISTS_TAC witnesses >>
            (fn (asl, goal) => ACCEPT_TAC (prove_conj (covered :: facts) goal) (asl, goal))
          end) witnesses packet
      end)
  end
QED

Triviality focus_cursor_readings:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    (SND (FST (HD cells))).vs_gas_readings = (SND (FST (LAST cells))).vs_gas_readings
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp[LAST_CONS] >> rpt strip_tac >>
  qpat_x_assum `supply_state_agree _ _ _`
    (mp_tac o AP_TERM ``(\s:venom_state. s.vs_gas_readings)`` o CONJUNCT1 o
      REWRITE_RULE [supply_state_agree_def]) >>
  simp[execution_frame_def]
QED

Triviality focus_stopped_cursor:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ==>
  (active_inst fn9 inst9 s9 /\ supply_prefix_defined fn9 s9 /\ ~s9.vs_halted) /\
  s8.vs_gas_readings = s9.vs_gas_readings
Proof
  PairCases_on `current` >> simp[cfg_norm_joint_cursors_def] >>
  strip_tac >>
  conj_tac
  >- (`?t. LAST current0 = (t,fn9,NONE)` by
        (qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `(fn8,fn9,current0)` mp_tac) >>
         simp[] >> metis_tac[]) >>
      qpat_assum `LAST current0 = _` (fn last_round =>
        qpat_assum `LAST current1 = _` (fn last_cursor =>
          drule cfg_norm_cursors_last >> simp[last_round,last_cursor]))) >>
  drule focus_cursor_readings >> simp[]
QED

Triviality focus_stopped_plain_gas:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  normal_frame_plan rpolicy unit cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast /\
  active_inst fn inst s /\ inst.inst_opcode = GAS ==>
  s.vs_gas_readings <> []
Proof
  strip_tac >>
  `asm_frame_prog_ok prog` by metis_tac[codegen_assembly_frame_prog_ok] >>
  `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0`
    by fs[entry_asm_state_def] >>
  drule_all focus_plain_frame_gas_available >> simp[]
QED

(* A non-OK accumulator is absorbing, so the first failed step retains
   both components of the final result. *)
Triviality focus_stopped_fold_first_failure:
  !xs es0 s events r.
    (!es bad x. (!v. bad <> OK v) ==> advance (es,bad) x = (es,bad)) /\
    FOLDL advance (es0,OK s) xs = (events,r) /\ (!v. r <> OK v) ==>
    ?pre x post prior u.
      xs = pre ++ x::post /\
      FOLDL advance (es0,OK s) pre = (prior,OK u) /\
      FOLDL advance (es0,OK s) (pre ++ [x]) = (events,r)
Proof
  Induct using listTheory.SNOC_INDUCT >- simp[] >>
  simp[SNOC_APPEND, FOLDL_APPEND] >> rpt gen_tac >> strip_tac >>
  Cases_on `FOLDL advance (es0,OK s) xs` >>
  rename1 `FOLDL advance (es0,OK s) xs = (ep,res)` >>
  Cases_on `?v. res = OK v`
  >- (gvs[] >> qexistsl [`xs`,`x`,`[]`,`ep`,`v`] >> simp[]) >>
  `advance (ep,res) x = (ep,res)` by metis_tac[] >>
  gvs[] >>
  first_x_assum (qspecl_then [`es0`,`s`,`ep`,`r`] mp_tac) >> simp[] >>
  strip_tac >> qexistsl [`pre`,`x'`,`post ++ [x]`,`prior`,`u`] >>
  gvs[APPEND_ASSOC, FOLDL_APPEND]
QED

Triviality focus_stopped_nested_fold_failure:
  root_run = (\ls entry. FOLDL level_step ([],OK entry) ls) /\
  level_step = (\(prior,r) (sf,plan,call).
    case r of
      OK ent =>
        (prior ++ FST (plan_run sf.fn_name plan ent),
         case SND (plan_run sf.fn_name plan ent) of
           OK caller => (case call of NONE => OK caller | SOME c => setup_run c caller)
         | other => other)
    | other => (prior,other)) /\
  plan_run = (\owner rows entry. FOLDL (row_step owner) ([],OK entry) rows) /\
  (!owner es bad row. (!v. bad <> OK v) ==> row_step owner (es,bad) row = (es,bad)) /\
  root_run levels R = (events,r) /\ (!v. r <> OK v) ==>
  ?pre sf plan call post prior ent.
    levels = pre ++ (sf,plan,call)::post /\
    root_run pre R = (prior,OK ent) /\
    ((?rows row later ev0 u.
       plan = rows ++ row::later /\
       root_run (pre ++ [(sf,rows,NONE)]) R = (ev0,OK u) /\
       root_run (pre ++ [(sf,rows ++ [row],NONE)]) R = (events,r)) \/
     (?c caller. call = SOME c /\
       root_run (pre ++ [(sf,plan,NONE)]) R = (events,OK caller) /\
       setup_run c caller = r))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "root_eq")
    (CONJUNCTS_THEN2 (mk_asm "level_eq")
      (CONJUNCTS_THEN2 (mk_asm "plan_eq") STRIP_ASSUME_TAC))) >>
  `FOLDL level_step ([],OK R) levels = (events,r)` by
    gvs[markerLib.L "root_eq"] >>
  `!es bad x. (!v. bad <> OK v) ==> level_step (es,bad) x = (es,bad)` by
    (rpt gen_tac >> disch_tac >> PairCases_on `x` >> Cases_on `bad` >>
     gvs[markerLib.L "level_eq"]) >>
  drule_all focus_stopped_fold_first_failure >> strip_tac >>
  PairCases_on `x` >> rename1 `levels = pre ++ (sf,plan,call)::post` >>
  `root_run (pre ++ [(sf,plan,call)]) R = (events,r)` by simp[markerLib.L "root_eq"] >>
  `!rows c. root_run (pre ++ [(sf,rows,c)]) R =
     (prior ++ FST (plan_run sf.fn_name rows u),
      case SND (plan_run sf.fn_name rows u) of
        OK caller => (case c of NONE => OK caller | SOME i => setup_run i caller)
      | other => other)` by
    (simp[markerLib.L "root_eq", FOLDL_APPEND] >> simp[markerLib.L "level_eq"]) >>
  qexistsl [`pre`,`sf`,`plan`,`call`,`post`,`prior`,`u`] >>
  conj_tac >- simp[] >> conj_tac >- simp[markerLib.L "root_eq"] >>
  Cases_on `plan_run sf.fn_name plan u` >>
  rename1 `plan_run sf.fn_name plan u = (evs,res)` >>
  Cases_on `?v. res = OK v`
  >- (disj2_tac >> Cases_on `call` >> gvs[] >> metis_tac[]) >>
  disj1_tac >>
  `FOLDL (row_step sf.fn_name) ([],OK u) plan = (evs,res)` by
    gvs[markerLib.L "plan_eq"] >>
  `!es bad x. (!v. bad <> OK v) ==> row_step sf.fn_name (es,bad) x = (es,bad)` by
    metis_tac[] >>
  `!v. res <> OK v` by metis_tac[] >>
  qpat_assum `FOLDL (row_step _) _ _ = _`
    (mp_then (Pat `FOLDL _ _ _ = _`) mp_tac focus_stopped_fold_first_failure) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `plan = rows ++ row::later` >>
  rename1 `FOLDL (row_step _) _ rows = (ev0,OK v)` >>
  qexistsl [`rows`,`row`,`later`,`prior ++ ev0`,`v`] >>
  Cases_on `res` >> gvs[markerLib.L "plan_eq"]
QED

Theorem focus_stopped_rooted_first_failure:
  !(F:num).
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  rooted_eval F C7 levels R = (events,r) /\ (!v. r <> OK v) ==>
  ?pre sf plan call post prior ent.
    levels = pre ++ (sf,plan,call)::post /\
    rooted_eval F C7 pre R = (prior,OK ent) /\
    ((?rows row later ev0 u.
       plan = rows ++ row::later /\
       rooted_eval F C7 (pre ++ [(sf,rows,NONE)]) R = (ev0,OK u) /\
       rooted_eval F C7 (pre ++ [(sf,rows ++ [row],NONE)]) R = (events,r)) \/
     (?c caller. call = SOME c /\
       rooted_eval F C7 (pre ++ [(sf,plan,NONE)]) R = (events,OK caller) /\
       (case decode_invoke c of
          NONE => Error "invoke: bad operand format"
        | SOME (nm,ops) =>
          case lookup_function nm C7.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee =>
            case eval_operands ops caller of
              NONE => Error "invoke: undefined argument"
            | SOME args =>
              case setup_callee callee args caller of
                NONE => Error "invoke: empty function"
              | SOME cs => OK cs) = r))
Proof
  rpt strip_tac >>
  rename1 `rooted_eval fuel C7 levels R = (events,r)` >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `call_setup = _`
    (fn th => ONCE_REWRITE_TAC [GSYM (BETA_RULE (REWRITE_RULE [FUN_EQ_THM] th))]) >>
  irule focus_stopped_nested_fold_failure >>
  qpat_x_assum `rooted_eval = _` mp_tac >>
  qpat_x_assum `plan_eval = _` mp_tac >>
  qpat_x_assum `rooted_eval fuel C7 levels R = _` mp_tac >>
  qpat_x_assum `!v. r <> OK v` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> csimp[] >>
  qexists_tac `\owner (es,r) row.
    case r of
      OK s => (es ++ FST (row_eval fuel C7 owner row s), SND (row_eval fuel C7 owner row s))
    | other => (es,other)` >>
  simp[] >> rpt gen_tac >> Cases_on `bad` >> simp[]
QED

Theorem focus_observed_cut_cell[local]:
  ALL_DISTINCT keys /\ LENGTH keys = LENGTH slots /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw /\
  keys = cut ++ rest /\ MEM k cut /\ MEM (k,w) obs ==>
  MEM (k,w) (ZIP (cut,TAKE (LENGTH cut) raw))
Proof
  strip_tac >>
  `MEM (k,SOME w) (ZIP (keys,slots))` by
    (drule sortingTheory.PERM_MEM_EQ >>
     disch_then (qspec_then `(k,w)` mp_tac) >>
     simp[MEM_MAP,MEM_FILTER,pairTheory.EXISTS_PROD] >>
     strip_tac >> rename1 `IS_SOME slot` >> Cases_on `slot` >> gvs[]) >>
  qpat_x_assum `MEM (k,SOME w) (ZIP _)` mp_tac >>
  simp[MEM_ZIP] >> disch_then (qx_choose_then `i` strip_assume_tac) >>
  `?h. h < LENGTH cut /\ k = EL h cut` by metis_tac[MEM_EL] >>
  `h < LENGTH keys /\ EL h keys = EL h cut` by
    (simp[EL_APPEND1] >> gvs[] >> decide_tac) >>
  `i = h` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  qpat_x_assum `LIST_REL _ slots raw` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `h` mp_tac) >>
  `h < LENGTH slots` by metis_tac[] >> simp[] >> strip_tac >>
  `w = EL h raw` by metis_tac[optionTheory.SOME_11,optionTheory.NOT_NONE_SOME] >>
  `LENGTH cut <= LENGTH raw` by gvs[] >>
  simp[MEM_ZIP] >> qexists_tac `h` >> simp[EL_TAKE]
QED

Theorem focus_stopped_packet_key_projection[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) ==>
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  ALL_DISTINCT Kroot /\ LENGTH Kroot = LENGTH raw_slots /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (Kroot,raw_slots)))) obs /\
  obs = dftGasFromListTraceDefs$trace_gas
    (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry))
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `Kroot = _` mp_tac >>
  qpat_assum `AK = _` mp_tac >>
  qpat_assum `raw_slots = _` mp_tac >>
  qpat_assum `(j,obs) = _` mp_tac >>
  qpat_assum `ALL_DISTINCT (AK [])` mp_tac >>
  qpat_assum `LENGTH (AM []) = LENGTH (AK [])` mp_tac >>
  qpat_assum `PERM _ _` mp_tac >>
  qpat_assum `_ = dftGasFromListTraceDefs$trace_gas (TAKE _ _)` mp_tac >>
  qpat_assum `o1_ctx_shape C7` mp_tac >>
  qpat_assum `o1_ctx_shape C8` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED

Theorem focus_stopped_recorded_functional[local]:
  o1_ctx_shape C /\ dftGasFromListUnion$recorded C s k w /\
  dftGasFromListUnion$recorded C s k v ==> w = v
Proof
  strip_tac >> irule dftGasFromListUnionTheory.recorded_functional >>
  qexistsl [`C`,`k`,`s`] >> asm_rewrite_tac[] >>
  qpat_assum `o1_ctx_shape C` mp_tac >>
  simp_tac bool_ss [o1_ctx_shape_def,venomWfTheory.ctx_inst_ids_distinct_def] >>
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
  BETA_TAC >> strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]
QED

Theorem focus_stopped_cut_observed_agreement:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Kroot = Kcut ++ kr /\
  dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf
    (root_entry with vs_gas_readings := raw ++ [0w]) = before ++ after /\
  dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,TAKE (LENGTH Kcut) raw) ==>
  !k w7 w8. MEM k Kcut /\ MEM k (MAP FST obs) /\
    dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k w7 /\
    dftGasFromListUnion$recorded C8 vs0 k w8 ==> w7 = w8
Proof
  strip_tac >> drule_all focus_stopped_packet_key_projection >> strip_tac >>
  rpt strip_tac >>
  `?w. MEM (k,w) obs` by
    (qpat_x_assum `MEM k (MAP FST obs)` mp_tac >>
     simp[MEM_MAP,pairTheory.EXISTS_PROD] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `MEM (k,w) (dftGasFromListTraceDefs$trace_gas before)` by
    (asm_rewrite_tac[] >> irule focus_observed_cut_cell >> metis_tac[]) >>
  `dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k w` by
    (simp[dftGasFromListUnionTheory.recorded_def] >> qexists_tac `fuel` >>
     gvs[dftGasFromListTraceDefsTheory.trace_context_def,
         dftGasFromListTraceDefsTheory.trace_function_def,
         dftGasFromListReadingsTheory.trace_gas_append]) >>
  `dftGasFromListUnion$recorded C8 vs0 k w` by
    (simp[dftGasFromListUnionTheory.recorded_def] >> qexists_tac `N` >>
     simp[dftGasFromListTraceDefsTheory.trace_context_def,
          dftGasFromListTraceDefsTheory.trace_function_def] >>
     qmatch_goalsub_abbrev_tac `dftGasFromListTraceDefs$trace_gas visits` >>
     `MEM (k,w) (dftGasFromListTraceDefs$trace_gas (TAKE j visits))` by
       metis_tac[] >>
     qspecl_then [`j`,`visits`] (SUBST1_TAC o SYM) TAKE_DROP >>
     simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
  metis_tac[focus_stopped_recorded_functional]
QED

Theorem focus_terminal_recorded_regions:
  let tr = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry in
  C8.ctx_entry = SOME nm /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl7 /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  j < LENGTH tr /\ EL j tr = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  obs = dftGasFromListTraceDefs$trace_gas (TAKE j tr) /\
  (!err. run_blocks N C8 root_tf root_entry <> Error err) ==>
  ?bt rest. lookup_block s8.vs_current_bb fn8.fn_blocks = SOME bt /\
    get_instruction bt s8.vs_inst_idx = SOME inst8 /\
    DROP j tr = dftGasFromListTraceDefs$trace_block p d (N-d) C8 fn8 bt s8 ++ rest /\
    (!k w. dftGasFromListUnion$recorded C8 vs0 k w <=>
      MEM (k,w) obs \/
      MEM (k,w) (dftGasFromListTraceDefs$trace_gas
        (dftGasFromListTraceDefs$trace_block p d (N-d) C8 fn8 bt s8)) \/
      MEM (k,w) (dftGasFromListTraceDefs$trace_gas rest))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `!n. dftGasFromListTraceDefs$trace_context n C8 vs0 =
       dftGasFromListTraceDefs$trace_blocks [] 0 n C8 root_tf root_entry` by
    gvs[dftGasFromListTraceDefsTheory.trace_context_def,
        dftGasFromListTraceDefsTheory.trace_function_def] >>
  qpat_x_assum `root_entry = _` kall_tac >>
  `!k w. dftGasFromListUnion$recorded C8 vs0 k w <=>
     MEM (k,w) (dftGasFromListTraceDefs$trace_gas
       (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry))` by
    (simp[dftGasFromListUnionTheory.recorded_def] >> rpt gen_tac >> eq_tac
     >- (strip_tac >> Cases_on `n <= N`
         >- (`?suffix. dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry =
                dftGasFromListTraceDefs$trace_blocks [] 0 n C8 root_tf root_entry ++ suffix` by
               (irule (cj 3 dftGasFromListTracePrefixTheory.trace_prefix) >> simp[]) >>
             simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
         `dftGasFromListTraceDefs$trace_blocks [] 0 n C8 root_tf root_entry =
            dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry` by
           (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >> simp[] >> decide_tac) >>
         metis_tac[]) >>
     strip_tac >> qexists_tac `N` >> simp[]) >>
  drule_all dftPacketNativeContinuationTheory.native_trace_blocks_continuation >>
  simp[] >> strip_tac >>
  qexistsl [`bt`,`rest`] >> simp[] >>
  `dftGasFromListTraceDefs$trace_gas
     (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
   obs ++ dftGasFromListTraceDefs$trace_gas
     (dftGasFromListTraceDefs$trace_block p d (N-d) C8 fn8 bt s8) ++
   dftGasFromListTraceDefs$trace_gas rest` by
    (qspecl_then [`j`,`dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry`]
       (SUBST1_TAC o SYM) TAKE_DROP >>
     pure_once_rewrite_tac [dftGasFromListReadingsTheory.trace_gas_append] >>
     simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
  simp[DISJ_ASSOC]
QED

Theorem focus_stopped_shared_recording_replay:
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\ C7.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME f7 /\ fn_entry_label f7 = SOME lbl /\
  (!k w7 w8.
    dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k w7 /\
    dftGasFromListUnion$recorded C8 vs0 k w8 ==> w7 = w8) ==>
  ?orc.
    (!fuel. gas_res_rel (run_context fuel C7
      (vs0 with vs_gas_readings := raw ++ [0w])) (ev_context orc fuel C7 vs0)) /\
    (!fuel. gas_res_rel (run_context fuel C8 vs0) (ev_context orc fuel C8 vs0)) /\
    (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s ==>
      ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
        C7 fn inst (s with vs_gas_readings := ws)) /\
    (!fn inst s. raw_reachable vs0 C8 fn inst s ==>
      ?p d. ev_reachable orc vs0 C8 p d fn inst
        (s with vs_gas_readings := vs0.vs_gas_readings))
Proof
  strip_tac >>
  `EVERY wf_function C7.ctx_functions /\ EVERY wf_function C8.ctx_functions` by
    (fs[o1_ctx_shape_def,EVERY_MEM,o1_fn_shape_def] >> metis_tac[]) >>
  qabbrev_tac `s7 = vs0 with vs_gas_readings := raw ++ [0w]` >>
  qabbrev_tac `orc = (\k. @w. dftGasFromListUnion$recorded C7 s7 k w \/
                               dftGasFromListUnion$recorded C8 vs0 k w)` >>
  `!k w. dftGasFromListUnion$recorded C7 s7 k w \/
          dftGasFromListUnion$recorded C8 vs0 k w ==> orc k = w` by
    (rpt gen_tac >> disch_tac >> simp_tac pure_ss [Abbr `orc`] >>
     BETA_TAC >> SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
     metis_tac[focus_stopped_recorded_functional]) >>
  `!n. trace_agrees orc (dftGasFromListTraceDefs$trace_context n C8 vs0)` by
    (simp[trace_agrees_def,EVERY_MEM,pairTheory.FORALL_PROD] >>
     metis_tac[dftGasFromListUnionTheory.recorded_def]) >>
  qabbrev_tac `entry = vs0 with <|vs_prev_bb := NONE;
                                  vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `!n. trace_agrees orc (dftGasFromListTraceDefs$trace_blocks [] 0 n C7 f7
         (entry with vs_gas_readings := raw ++ [0w]))` by
    (`!n. dftGasFromListTraceDefs$trace_context n C7 s7 =
          dftGasFromListTraceDefs$trace_blocks [] 0 n C7 f7
            (entry with vs_gas_readings := raw ++ [0w])` by
       simp[trace_context_def,trace_function_def,Abbr `s7`,Abbr `entry`] >>
     simp[trace_agrees_def,EVERY_MEM,pairTheory.FORALL_PROD] >>
     metis_tac[dftGasFromListUnionTheory.recorded_def]) >>
  qexists_tac `orc` >> simp_tac pure_ss [Abbr `s7`] >>
  irule dftGasPrefixProviderTheory.fixed_shared_oracle_replay >>
  asm_rewrite_tac[] >> gen_tac >>
  rename1 `dftGasToListTrace$trace_context orc fuel C7 vs0` >>
  first_x_assum (qspec_then `fuel` assume_tac) >>
  drule (cj 3 dftGasPrefixProviderTheory.native_trace_oracle_agreement) >>
  disch_then (qspec_then `vs0.vs_gas_readings` mp_tac) >>
  simp[dftGasToListTraceTheory.trace_context_def,
       dftGasToListTraceTheory.trace_function_def,Abbr `entry`]
QED

(* The focused index, rather than just the final result, determines which
   continuation to discard. A terminal INVOKE still has its callee visits. *)
Theorem focus_stopped_nonreturning_suffix_with_error:
  (!P D fuel C f outer s h p d g i u r.
    h < LENGTH (trace_step P D fuel C f outer s) /\
    EL h (trace_step P D fuel C f outer s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t) \/ (?err. r = Error err)) ==>
    step_inst fuel C outer s = r /\
    DROP h (trace_step P D fuel C f outer s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u) /\
  (!P D fuel C f bb s h p d g i u r.
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t) \/ (?err. r = Error err)) ==>
    exec_block fuel C bb s = r /\
    DROP h (trace_block P D fuel C f bb s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u) /\
  (!P D fuel C f s h p d g i u r.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t) \/ (?err. r = Error err)) ==>
    run_blocks fuel C f s = r /\
    DROP h (trace_blocks P D fuel C f s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_stopped_nonreturning_suffix_with_error[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac))) >>
  Cases_on `outer.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke outer` >> gvs[] >>
  rename1 `decode_invoke outer = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  qpat_x_assum `!h p d g i u. _` drule >> disch_then drule >>
  simp[] >> strip_tac >>
  once_rewrite_tac[cj 1 venomExecSemanticsTheory.run_defs] >> simp[]
QED

Resume focus_stopped_nonreturning_suffix_with_error[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac))) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> once_rewrite_tac[cj 2 venomExecSemanticsTheory.run_defs] >> simp[]) >>
  rename1 `SUC k` >> gnvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND, DROP_APPEND1] >>
      qpat_x_assum `!h p d g i u. _` drule >> disch_then drule >>
      simp[] >> strip_tac >> gvs[] >>
      once_rewrite_tac[cj 2 venomExecSemanticsTheory.run_defs] >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gnvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  qmatch_asmsub_abbrev_tac `LENGTH right + LENGTH left` >>
  `k - LENGTH left < LENGTH right` by decide_tac >>
  once_rewrite_tac[cj 2 venomExecSemanticsTheory.run_defs] >> simp[] >>
  qpat_x_assum `!h p d g i u. h < LENGTH right /\ _ ==> _` drule >>
  disch_then drule >> simp[]
QED

Resume focus_stopped_nonreturning_suffix_with_error[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac))) >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gnvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gnvs[ADD_CLAUSES] >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND, DROP_APPEND1] >>
      qpat_x_assum `!h p d g i u. _` drule >> disch_then drule >>
      simp[] >> strip_tac >>
      once_rewrite_tac[cj 3 venomExecSemanticsTheory.run_defs] >> gvs[Abbr `start`]) >>
  Cases_on `exec_block n C bb start` >> gnvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  qmatch_asmsub_abbrev_tac `LENGTH right + LENGTH left` >>
  once_rewrite_tac[cj 3 venomExecSemanticsTheory.run_defs] >> gvs[Abbr `start`] >>
  `h - LENGTH left < LENGTH right` by decide_tac >>
  qpat_x_assum `!h p d g i u. h < LENGTH right /\ _ ==> _` drule >>
  disch_then drule >> simp[]
QED

Finalise focus_stopped_nonreturning_suffix_with_error

Theorem focus_stopped_nonreturning_suffix:
  (!P D fuel C f outer s h p d g i u r.
    h < LENGTH (trace_step P D fuel C f outer s) /\
    EL h (trace_step P D fuel C f outer s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t)) ==>
    step_inst fuel C outer s = r /\
    DROP h (trace_step P D fuel C f outer s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u) /\
  (!P D fuel C f bb s h p d g i u r.
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t)) ==>
    exec_block fuel C bb s = r /\
    DROP h (trace_block P D fuel C f bb s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u) /\
  (!P D fuel C f s h p d g i u r.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,i.inst_id),g,i,u) /\
    step_inst (D + fuel - d) C i u = r /\
    ((?t. r = Halt t) \/ (?a t. r = Abort a t)) ==>
    run_blocks fuel C f s = r /\
    DROP h (trace_blocks P D fuel C f s) =
      ((p,d,i.inst_id),g,i,u) :: trace_step p d (D + fuel - d) C g i u)
Proof
  conj_tac >- metis_tac[cj 1 focus_stopped_nonreturning_suffix_with_error] >>
  conj_tac >- metis_tac[cj 2 focus_stopped_nonreturning_suffix_with_error] >>
  metis_tac[cj 3 focus_stopped_nonreturning_suffix_with_error]
QED

(* A missing operand at a native CODECOPY visit is a root error at the
   fuel of that visit, including when the visit is inside a callee. *)
Theorem focus_native_codecopy_label_error:
  trace_blocks [] 0 fuel C7 root_sf R = before ++ [((a,e,i.inst_id),sf,i,u)] ++ after /\
  i.inst_opcode = CODECOPY /\
  MEM op i.inst_operands /\
  eval_operand op u = NONE ==>
  ?err. run_blocks fuel C7 root_sf R = Error err
Proof
  strip_tac >>
  `?err. step_inst (fuel - e) C7 i u = Error err` by
    (simp[step_inst_non_invoke] >>
     irule fnBlockBodyHelpersTheory.label_eval_error >> simp[] >>
     qexists `op` >> simp[]) >>
  `LENGTH before < LENGTH (trace_blocks [] 0 fuel C7 root_sf R)` by simp[] >>
  `EL (LENGTH before) (trace_blocks [] 0 fuel C7 root_sf R) =
   ((a,e,i.inst_id),sf,i,u)` by simp[EL_APPEND_EQN] >>
  drule (cj 3 focus_stopped_nonreturning_suffix_with_error) >>
  disch_then drule >> simp[] >> metis_tac[]
QED

(* The selected frame rules out an empty-reading GAS endpoint on either
   finalizer route, without requiring an additional joint transition. *)
Theorem focus_stopped_gas_not_empty:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
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
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
      rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  inst9.inst_opcode = GAS ==>
  s8.vs_gas_readings <> []
Proof
  strip_tac >> drule focus_stopped_cursor >> strip_tac >> simp[] >>
  Cases_on `fin = K SOME`
  >- (qpat_x_assum `fin = K SOME` SUBST_ALL_TAC >>
      qpat_x_assum `K SOME _ _ = _`
        (SUBST_ALL_TAC o SYM o REWRITE_RULE [combinTheory.K_THM, optionTheory.SOME_11]) >>
      qpat_x_assum `K SOME = K SOME ==> _`
        (strip_assume_tac o REWRITE_RULE []) >>
      drule_all focus_stopped_plain_gas >> simp[]) >>
  `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
  ntac 2 (qpat_x_assum `asm_opt_finalizer = asm_opt_finalizer ==> _`
    (strip_assume_tac o REWRITE_RULE [])) >>
  `codegen_ready out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
       (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     drule venomPipelineDriverPropsTheory.run_venom_pipeline_success_boundary >> simp[]) >>
  `focus_s7_symbolic_context out.po_unit prog` by
    (drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow >> strip_tac >>
     drule_all gasFocusOptStaticAssemblyTheory.focus_opt_static_assembly >>
     simp[focus_s7_symbolic_context_def]) >>
  drule_all gasFocusGasPreEdgeTheory.focus_normal_frame_gas_available >>
  disch_then (qx_choose_then `max_cost`
    (drule_all o Q.SPECL [`asm_fuel`, `ast`, `ss`])) >> simp[]
QED

(* A nonreturning focus has no later continuation, but an INVOKE can
   still record GAS inside the focused step. *)
Theorem focus_stopped_terminal_recordings:
  let tr = trace_blocks [] 0 N C8 root_tf root_entry in
  C8.ctx_entry = SOME nm /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl7 /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  j < LENGTH tr /\ EL j tr = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  obs = trace_gas (TAKE j tr) /\
  step_inst (N-d) C8 inst8 s8 = r /\
  ((?u. r = Halt u) \/ (?ex u. r = Abort ex u)) ==>
  !k w. dftGasFromListUnion$recorded C8 vs0 k w <=>
    MEM (k,w) obs \/
    (inst8.inst_opcode = INVOKE /\
     MEM (k,w) (trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8)))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `run_blocks N C8 root_tf root_entry = r /\
   DROP j (trace_blocks [] 0 N C8 root_tf root_entry) =
     ((p,d,inst8.inst_id),fn8,inst8,s8) :: trace_step p d (N-d) C8 fn8 inst8 s8` by
    metis_tac[SIMP_RULE bool_ss [ADD_CLAUSES]
      (Q.SPECL [`[]`, `0`] (cj 3 focus_stopped_nonreturning_suffix))] >>
  `!err. run_blocks N C8 root_tf root_entry <> Error err` by
    (qpat_assum `(?u. r = Halt u) \/ _` mp_tac >> strip_tac >> simp[]) >>
  `inst8.inst_opcode <> GAS` by
    (strip_tac >>
     `step_inst (N-d) C8 inst8 s8 = exec_gas inst8 s8` by
       (qpat_assum `inst8.inst_opcode = GAS` (fn th =>
          simp[NoAsms, th, step_inst_non_invoke, step_inst_base_def])) >>
     qpat_assum `(?u. r = Halt u) \/ _` mp_tac >> strip_tac >>
     metis_tac[exec_gas_not_terminal]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] focus_terminal_recorded_regions) >>
  strip_tac >>
  qpat_x_assum `root_entry = _` SUBST_ALL_TAC >>
  `trace_gas (trace_block p d (N-d) C8 fn8 bt s8) ++ trace_gas rest =
   trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8)` by
    (pure_once_rewrite_tac[GSYM dftGasFromListReadingsTheory.trace_gas_append] >>
     qpat_assum `DROP j _ = _ ++ _` (SUBST1_TAC o SYM) >>
     qpat_assum `DROP j _ = _ :: _` SUBST1_TAC >>
     simp[trace_gas_def, visit_gas_def]) >>
  rpt gen_tac >>
  `MEM (k,w) (trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8)) <=>
   MEM (k,w) (trace_gas (trace_block p d (N-d) C8 fn8 bt s8)) \/
   MEM (k,w) (trace_gas rest)` by metis_tac[MEM_APPEND] >>
  Cases_on `inst8.inst_opcode = INVOKE`
  >- metis_tac[] >>
  `~MEM (k,w) (trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8))` by
    (qpat_assum `inst8.inst_opcode <> INVOKE` (fn th =>
       simp[NoAsms, th, trace_step_noninvoke, dftGasFromListReadingsTheory.trace_gas_nil])) >>
  metis_tac[]
QED

(* An OK step at the selected C8 cursor cannot set the halted flag. *)
Theorem focus_stopped_cursor_ok_nonhalted:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  step_inst fuel C8 inst8 s8 = OK u ==>
  ~u.vs_halted
Proof
  PairCases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  rename1 `cfg_norm_cursors C8 rounds cells` >>
  drule cfg_norm_cursors_lengths >> strip_tac >>
  Cases_on `cells` >> gvs[] >>
  Cases_on `rounds` >> gvs[] >>
  rename1 `cfg_norm_cursors C8 (row::rs) (((inst8,s8),pending)::cs)` >>
  PairCases_on `row` >>
  drule cfg_norm_cursors_head >> strip_tac >>
  drule venomStepPropsTheory.step_inst_ok_halted >> simp[]
QED

Theorem focus_bounded_source_recording_position:
  let v = vs0 with vs_gas_readings := raw ++ [0w];
      R = root_entry with vs_gas_readings := raw ++ [0w] in
  C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME sf /\
  fn_entry_label sf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  LENGTH B <= LENGTH raw /\
  ((!F. N <= F ==> ?z. B = gas_events_blocks F C sf R ++ z) \/
   (?F z. N <= F /\ (!err. run_blocks F C sf R <> Error err) /\
          B = gas_events_blocks F C sf R ++ z)) ==>
  !k w. dftGasFromListUnion$recorded C v k w <=>
    ?F i z. N <= F /\ B = gas_events_blocks F C sf R ++ z /\
      i < LENGTH (gas_events_blocks F C sf R) /\
      FST (EL i (trace_gas (trace_blocks [] 0 F C sf R))) = k /\
      EL i raw = w
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  qabbrev_tac `R = root_entry with vs_gas_readings := raw ++ [0w]` >>
  `!n. trace_context n C (vs0 with vs_gas_readings := raw ++ [0w]) =
       trace_blocks [] 0 n C sf R` by
    simp[trace_context_def, trace_function_def, Abbr `R`] >>
  qpat_x_assum `root_entry = _` kall_tac >>
  `!n m k w. MEM (k,w) (trace_gas (trace_blocks [] 0 n C sf R)) /\
     (n <= m \/ (!err. run_blocks m C sf R <> Error err)) ==>
     MEM (k,w) (trace_gas (trace_blocks [] 0 m C sf R))` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     Cases_on `n <= m`
     >- (`?suffix. trace_blocks [] 0 m C sf R = trace_blocks [] 0 n C sf R ++ suffix` by
           (irule (cj 3 dftGasFromListTracePrefixTheory.trace_prefix) >> simp[]) >>
         simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
     `trace_blocks [] 0 n C sf R = trace_blocks [] 0 m C sf R` by
       (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >> gvs[]) >>
     metis_tac[]) >>
  `!fuel i z. B = gas_events_blocks fuel C sf R ++ z /\
     i < LENGTH (gas_events_blocks fuel C sf R) ==>
     SND (EL i (trace_gas (trace_blocks [] 0 fuel C sf R))) = EL i raw` by
    (simp[gas_events_length] >> rpt strip_tac >>
     `i < LENGTH raw` by gvs[LENGTH_APPEND, gas_events_length] >>
     `i < LENGTH (trace_gas (trace_blocks [] 0 fuel C sf R))` by
       simp[dftGasFromListReadingsTheory.trace_gas_lengths] >>
     `EL i (MAP SND (trace_gas (trace_blocks [] 0 fuel C sf R))) = EL i raw` by
       (simp[dftGasFromListReadingsTheory.trace_gas_readings,
             dftGasFromListReadingsTheory.gas_prefix_genlist] >>
        simp[Abbr `R`, EL_APPEND1]) >>
     gvs[EL_MAP]) >>
  `!k w. dftGasFromListUnion$recorded C
      (vs0 with vs_gas_readings := raw ++ [0w]) k w <=>
    ?fuel z. N <= fuel /\ B = gas_events_blocks fuel C sf R ++ z /\
      MEM (k,w) (trace_gas (trace_blocks [] 0 fuel C sf R))` by
    (simp[dftGasFromListUnionTheory.recorded_def] >> rpt gen_tac >> eq_tac
     >- (strip_tac >> qpat_x_assum `(!fuel. _) \/ _` strip_assume_tac
         >- (qpat_x_assum `!fuel. N <= fuel ==> _` (qspec_then `MAX n N` mp_tac) >>
             simp[MAX_LE] >> strip_tac >> qexistsl [`MAX n N`,`z`] >>
             simp[MAX_LE] >> first_x_assum irule >> qexists_tac `n` >> simp[MAX_LE]) >>
         rename1 `B = gas_events_blocks fuel C sf R ++ z` >>
         qexistsl [`fuel`,`z`] >> simp[] >>
         first_x_assum irule >> qexists_tac `n` >> simp[]) >>
     strip_tac >> qexists_tac `fuel` >> simp[]) >>
  simp[] >>
  simp_tac bool_ss [MEM_EL, quantHeuristicsTheory.PAIR_EQ_EXPAND,
    dftGasFromListReadingsTheory.trace_gas_lengths, gas_events_length] >>
  qpat_x_assum `!fuel i z. _ ==> SND _ = _`
    (fn th => POP_ASSUM_LIST (K (assume_tac (REWRITE_RULE [gas_events_length] th)))) >>
  metis_tac[]
QED

(* The native trace carries dynamic keys; the event list keeps only static
   sites. These projections preserve the order of GAS visits in callees. *)
Theorem focus_native_gas_site_ids:
  (!p d fuel ctx fn inst s.
    MAP (\kw. SND (SND (FST kw)))
      (visit_gas ((p,d,inst.inst_id),fn,inst,s) ++
       trace_gas (trace_step p d fuel ctx fn inst s)) =
    MAP SND (gas_events_step fuel ctx fn.fn_name inst s)) /\
  (!p d fuel ctx fn bb s.
    MAP (\kw. SND (SND (FST kw)))
      (trace_gas (trace_block p d fuel ctx fn bb s)) =
    MAP SND (gas_events_block fuel ctx fn.fn_name bb s)) /\
  (!p d fuel ctx fn s.
    MAP (\kw. SND (SND (FST kw)))
      (trace_gas (trace_blocks p d fuel ctx fn s)) =
    MAP SND (gas_events_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_native_gas_site_ids[step]:
  rpt gen_tac >> strip_tac >>
  simp[Once (cj 1 trace_defs), Once gas_events_step_def, visit_gas_def] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  metis_tac[]
QED

Resume focus_native_gas_site_ids[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs), Once gas_events_block_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  once_rewrite_tac[cj 2 trace_defs, gas_events_block_def] >>
  simp[dftGasFromListReadingsTheory.trace_gas_cons,
       dftGasFromListReadingsTheory.trace_gas_append, MAP_APPEND] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  metis_tac[MAP_APPEND]
QED

Resume focus_native_gas_site_ids[blocks]:
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[Once gas_events_blocks_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs), Once gas_events_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once (cj 3 trace_defs), Once gas_events_blocks_def] >>
  rename1 `eval_phis _ _ = OK sp` >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[dftGasFromListReadingsTheory.trace_gas_append, MAP_APPEND] >>
  rename1 `exec_block _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >> metis_tac[]
QED

Finalise focus_native_gas_site_ids

(* A completed call cell needs no filling for subsequent cells in its row. *)
Theorem focus_retained_call_cell_keys:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F q pregs childgs tail u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  MEM q (TAKE count rho) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pregs /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) childgs /\
  FOLDR (dftIndexedExec$dft_exec_cons (F-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT pregs ++ (childgs ++ tail)) = OK u ==>
  (?extra. EL q ks = MAP FST (trace_gas
    (trace_step a e (F-e) C7 sf (EL q xs) u)) ++ extra) /\
  (!v. step_inst (F-e) C7 (EL q xs) u = OK v ==>
    EL q ks = MAP FST (trace_gas (trace_step a e (F-e) C7 sf (EL q xs) u)))
Proof
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  `?call_h b0 done centry ir cout post.
    FLOOKUP calls (a,e,(EL q xs).inst_id) =
      SOME (q,call_h,b0,done,centry,SOME (ir,cout,post))` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> !q. _` (drule_then mp_tac) >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  `u.vs_gas_readings = childgs ++ tail` by
    suspend "prefix" >>
  `?csf ctf corder crest nm ops args.
    FLOOKUP acts ((e,(EL q xs).inst_id)::a) =
      SOME (csf,ctf,e,centry,corder,SOME (IntRet ir cout),SOME crest) /\
    decode_invoke (EL q xs) = SOME (nm,ops) /\
    lookup_function nm C7.ctx_functions = SOME csf /\
    eval_operands ops u = SOME args /\
    setup_callee csf args u = SOME (centry with vs_gas_readings := u.vs_gas_readings)` by
    suspend "setup" >>
  `EL q ms = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab ((e,(EL q xs).inst_id)::a,f)))) corder) /\
   EL q ks = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ((e,(EL q xs).inst_id)::a,f)))) corder)` by
    suspend "row" >>
  drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >>
  disch_then (fn th => rewrite_tac[th]) >>
  `?extra. EL q ks = MAP FST (trace_gas
    (trace_blocks ((e,(EL q xs).inst_id)::a) e (fuel-e) C7 csf
      (centry with vs_gas_readings := childgs ++ tail))) ++ extra` by
    (qpat_assum `EL q ks = _` SUBST1_TAC >>
     irule dft_packet_closed_keys >>
     qpat_assum `FLOOKUP acts ((e,_)::a) = _` (irule_at Any) >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     gvs[]) >>
  simp[] >> rpt strip_tac >>
  `?cir cv. run_blocks (fuel-e) C7 csf
    (centry with vs_gas_readings := childgs ++ tail) = IntRet cir cv` by
    (qpat_x_assum `step_inst _ _ _ _ = OK v` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_def,AllCaseEqs()] >>
     rpt strip_tac >> goal_assum (drule_at Any)) >>
  suspend "return_keys"
QED

Resume focus_retained_call_cell_keys[prefix]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!F k kgss tail. _`
    (qspecl_then [`fuel`,`q`,`pregs`,`childgs ++ tail`] mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Resume focus_retained_call_cell_keys[setup]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = _ /\ FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ ==> _`
    (drule_all_then mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` (drule_then mp_tac) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `FLOOKUP blocks (a,e) = SOME _`, `FLOOKUP acts a = SOME _`,
     `LIST_REL (\f g. g = dft_fn f) _ _`, `LIST_REL dft_fn_rel _ _`,
     `o1_ctx_shape C7`, `u.vs_gas_readings = _`,
     `!op. MEM op (EL q xs).inst_operands ==> _`,
     `!callee args. setup_callee callee args (u with vs_gas_readings := _) = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `FLOOKUP acts a = _` kall_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `FLOOKUP acts ((e,_)::a) = SOME (_,_,e,_,_,_,child_rest)` >>
  Cases_on `child_rest` >- gvs[] >>
  drule_all dftPacketCalleeAlignmentTheory.dft_packet_callee_alignment >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C7.ctx_functions)` by
    fs[o1_ctx_shape_def,venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,venomInstTheory.ctx_fn_names_def] >>
  `lookup_function nm C7.ctx_functions = SOME csf` by
    gvs[o1ScheduleDecompHelpersTheory.lookup_function_member_iff,dftRunRelTheory.dft_fn_rel_def] >>
  gvs[]
QED

Resume focus_retained_call_cell_keys[row]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

Resume focus_retained_call_cell_keys[return_keys]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME(sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!gs tail. _` (qspecl_then [`childgs`,`tail`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `!v. _ \/ _ ==> _` (qspec_then `cv` mp_tac) >>
  simp[] >> strip_tac >>
  `LENGTH (EL q ks) = LENGTH childgs` by
    (qpat_assum `LIST_REL _ (EL q ms) childgs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH (AM (_::_)) = LENGTH (AK (_::_))` mp_tac >>
     qpat_assum `AM = _` mp_tac >>
     qpat_assum `AK = _` mp_tac >>
     qpat_assum `FLOOKUP acts ((e,_)::a) = _` mp_tac >>
     qpat_assum `EL q ms = _` mp_tac >>
     qpat_assum `EL q ks = FLAT _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `MAP FST (trace_gas (trace_blocks ((e,(EL q xs).inst_id)::a) e (fuel-e) C7 csf
      (centry with vs_gas_readings := childgs ++ tail))) = EL q ks` by
    (qpat_assum `trace_gas _ = ZIP _` mp_tac >>
     qpat_assum `EL q ks = FLAT _` (mp_tac o SYM) >>
     qpat_assum `LENGTH (EL q ks) = LENGTH childgs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MAP_ZIP]) >>
  qpat_assum `EL q ks = MAP FST _ ++ extra` mp_tac >>
  qpat_assum `MAP FST (trace_gas _) = EL q ks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise focus_retained_call_cell_keys

Theorem focus_native_failed_slice_trace:
  !k s r.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = r /\
    (!v. r <> OK v) ==>
    trace_block a e fuel C fn bb s =
      trace_block a e fuel C fn
        (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s
Proof
  Induct_on `k` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by simp[DROP_CONS_EL] >>
  `get_instruction bb s.vs_inst_idx =
    SOME (EL s.vs_inst_idx bb.bb_instructions)` by simp[get_instruction_def] >>
  dxrule_then assume_tac trace_block_visit >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC k + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  dxrule_then assume_tac trace_block_visit >>
  simp[] >>
  gvs[TAKE_def, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
  gvs[ADD_CLAUSES] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  qpat_x_assum `!s'. _ ==> trace_block _ _ _ _ _ _ _ = _`
    (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[ADD_CLAUSES]
QED

(* The native trace can stop inside the last executed cell of the slice. *)
Theorem focus_retained_row_slice_keys:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F k rowgs tail.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ k <= LENGTH xs /\
  (!t. t < k /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE t xs) /\
       (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE count rho)) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE k ms)) rowgs ==>
  ?extra. FLAT (TAKE k ks) = MAP FST (trace_gas
    (trace_block a e (F-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := rowgs ++ tail))) ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH ms = LENGTH xs /\
   LIST_REL (\i keys. if i.inst_opcode = GAS then keys = [(a,e,i.inst_id)]
                    else if i.inst_opcode = INVOKE then T else keys = []) xs ks` by
    suspend "shape" >>
  drule_then strip_assume_tac dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split >>
  irule dft_packet_native_row_keys >> qexists_tac `TAKE k xs` >>
  simp[DROP_APPEND2,rich_listTheory.LIST_REL_TAKE] >>
  rpt gen_tac >> strip_tac >> rename1 `j < k` >>
  `j < LENGTH xs /\ j < LENGTH ks` by
    (qpat_assum `LIST_REL _ xs ks` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  gvs[rich_listTheory.TAKE_TAKE_T, EL_TAKE] >>
  suspend "invoke"
QED

Resume focus_retained_row_slice_keys[shape]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (qspec_then `n` drule) >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `(EL n xs).inst_opcode = GAS` >>
  Cases_on `(EL n xs).inst_opcode = INVOKE` >> simp[]
QED

Resume focus_retained_row_slice_keys[invoke]:
  rename1 `N <= fuel` >>
  `j < LENGTH gss` by
    (qpat_assum `LIST_REL _ (TAKE k ms) gss`
      (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  `!i. i < k ==> LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
       (EL i ms) (EL i gss)` by
    (qpat_assum `LIST_REL _ (TAKE k ms) gss`
      (mp_tac o ONCE_REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[EL_TAKE]) >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
     (TAKE j ms) (TAKE j gss)` by
    (simp[Once LIST_REL_EL_EQN, EL_TAKE] >> rpt strip_tac >>
     qpat_assum `!i. i < k ==> LIST_REL _ _ _` irule >> decide_tac) >>
  `FLAT gss ++ tail = FLAT (TAKE j gss) ++
      (EL j gss ++ (FLAT (DROP (SUC j) gss) ++ tail))` by
    (qpat_assum `j < LENGTH gss` (mp_tac o MATCH_MP rich_listTheory.TAKE_DROP_SUC) >>
     disch_then (mp_tac o AP_TERM ``FLAT:(256 word) list list -> (256 word) list``) >>
     simp[APPEND_ASSOC]) >>
  (* Preserve the append grouping used by the call-cell interface. *)
  qpat_x_assum `FOLDR _ OK _ _ = OK st` mp_tac >>
  qpat_x_assum `FLAT gss ++ tail = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  rename1 `FLOOKUP blocks (a,e) =
    SOME (_,_,_,xs,_,row_order,_,_,SOME (be,_),ncompleted,_,_,_)` >>
  `MEM j (TAKE ncompleted row_order)` by metis_tac[] >>
  `!r. r < j /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE ncompleted row_order)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     `TAKE r (TAKE j xs) = TAKE r xs` by simp[rich_listTheory.TAKE_TAKE_T] >>
     metis_tac[rich_listTheory.EVERY_TAKE]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL j ms) (EL j gss)` by simp[] >>
  `j < LENGTH xs` by decide_tac >>
  MATCH_MP_TAC focus_retained_call_cell_keys >>
  qpat_assum `FOLDR _ OK _ _ = OK st` (irule_at Any) >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP ms_tab (a,e) = SOME _` (irule_at Any) >> simp[]
QED

Finalise focus_retained_row_slice_keys

Theorem focus_native_closed_row_step:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front rest ms ks depth fuel rowgs tail sp r.
  let phi = phi_prefix_length bb.bb_instructions;
      v = hin with vs_gas_readings := rowgs ++ tail;
      bs = be with vs_gas_readings := rowgs ++ tail;
      n = fuel - e in
  let start = sp with vs_inst_idx := phi in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,SOME rest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  e = SUC depth /\ e <= N /\ N <= fuel /\
  lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis v bb.bb_instructions = OK sp /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
  phi <= LENGTH ps /\ bs.vs_inst_idx = LENGTH ps /\
  FOLDR (dftIndexedExec$dft_exec_cons n C7) OK (DROP phi ps) start = OK bs /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) rowgs /\
  ((?post. front = OK post) \/ (?ir post. front = IntRet ir post)) /\
  FOLDR (dftIndexedExec$dft_exec_cons n C7) OK xs bs = r /\ terminates r ==>
  exec_block n C7 bb start = r /\
  dftGasToListReplay$residual_result tail front r /\
  MAP FST (trace_gas (trace_block a e n C7 sf bb start)) = FLAT ks /\
  MAP FST (trace_gas (trace_blocks a depth (SUC n) C7 sf v)) =
    FLAT ks ++ (case r of
      OK u => if u.vs_halted then [] else
                MAP FST (trace_gas (trace_blocks a e n C7 sf u))
    | _ => [])
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `dftGasToListReplay$residual_result tail front r` by
    (qpat_assum `FOLDR _ OK xs _ = r`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule dft_packet_closed_row_residual >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     simp[] >> qexists `fuel-e` >> simp[]) >>
  `?u. r = OK u \/ ?ir. r = IntRet ir u` by
    (Cases_on `r` >> gvs[dftGasToListReplayTheory.residual_result_def,
      stateEquivTheory.lift_result_def]) >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `start = sp with vs_inst_idx := phi` >>
  qabbrev_tac `bs = be with vs_gas_readings := rowgs ++ tail` >>
  qabbrev_tac `k = LENGTH ps - phi` >>
  `start.vs_inst_idx = phi` by simp[Abbr `start`] >>
  `TAKE k (DROP start.vs_inst_idx bb.bb_instructions) = DROP phi ps /\
   start.vs_inst_idx + k <= LENGTH bb.bb_instructions` by
    simp[Abbr `k`, DROP_APPEND1, TAKE_APPEND, LENGTH_DROP] >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP phi ps)` by simp[EVERY_DROP] >>
  `DROP bs.vs_inst_idx bb.bb_instructions = xs` by
    simp[Abbr `bs`, DROP_APPEND] >>
  `exec_block (fuel-e) C7 bb start = r` by
    (irule EQ_TRANS >> qexists `exec_block (fuel-e) C7 bb bs` >> conj_tac
     >- (irule dftPacketClosedRowNativeTheory.native_exec_block_prefix_skip >>
         qexists `k` >> gvs[] >>
         irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
         simp[] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
         simp[is_pseudo_def, is_terminator_def]) >>
     drule_all_then mp_tac dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >>
     gvs[]) >>
  `MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb start)) = FLAT ks` by
    (`trace_gas (trace_block a e (fuel-e) C7 sf bb start) =
      trace_gas (trace_block a e (fuel-e) C7 sf bb bs)` by
       (irule dftPacketClosedRowNativeTheory.native_trace_block_pseudo_skip >>
        qexists `k` >> gvs[]) >>
     `trace_block a e (fuel-e) C7 sf bb bs =
      trace_block a e (fuel-e) C7 sf
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> bs` by
       (irule dftPacketClosedRowNativeTheory.native_trace_block_suffix_cong >>
        gvs[Abbr `bs`, DROP_APPEND]) >>
     qpat_assum `trace_gas (trace_block _ _ _ _ _ bb start) = _`
       (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `trace_block _ _ _ _ _ bb bs = _`
       (fn th => pure_once_rewrite_tac[th]) >>
     qunabbrev_tac `bs` >> irule dft_packet_closed_row_key_success >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  simp[] >> drule_all_then (fn th => simp[th]) trace_blocks_enter >>
  gvs[Abbr `start`, Abbr `phi`, dftGasFromListReadingsTheory.trace_gas_append] >>
  simp[COND_RAND, trace_gas_def]
QED

Theorem focus_native_failed_row_step:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks depth fuel
    k rowgs tail sp z r.
  let phi = phi_prefix_length bb.bb_instructions;
      v = hin with vs_gas_readings := rowgs ++ tail;
      bs = be with vs_gas_readings := rowgs ++ tail;
      n = fuel - e in
  let start = sp with vs_inst_idx := phi in
  let Tz = trace_block a e n C7 sf
      (bb with bb_instructions := TAKE phi bb.bb_instructions ++ z) start in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  e = SUC depth /\ e <= N /\ N <= fuel /\
  lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis v bb.bb_instructions = OK sp /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
  phi <= LENGTH ps /\ bs.vs_inst_idx = LENGTH ps /\
  FOLDR (dftIndexedExec$dft_exec_cons n C7) OK (DROP phi ps) start = OK bs /\
  k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
  (!t. t < k /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE t xs) /\
       (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE count rho)) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE k ms)) rowgs /\
  z = DROP phi ps ++ TAKE k xs /\
  FOLDR (dftIndexedExec$dft_exec_cons n C7) OK z start = r /\ (!u. r <> OK u) ==>
  trace_blocks a depth (SUC n) C7 sf v = Tz /\
  ?extra. FLAT (TAKE k ks) = MAP FST (trace_gas Tz) ++ extra
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `start = sp with vs_inst_idx := phi` >>
  qabbrev_tac `bs = be with vs_gas_readings := rowgs ++ tail` >>
  qabbrev_tac `trunc = bb with bb_instructions := TAKE phi bb.bb_instructions ++ z` >>
  `start.vs_inst_idx = phi` by simp[Abbr `start`] >>
  `DROP phi bb.bb_instructions = z ++ DROP k xs` by
    simp[DROP_APPEND1, listTheory.APPEND_ASSOC] >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP phi ps)` by simp[EVERY_DROP] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) z` by
    (asm_rewrite_tac[EVERY_APPEND] >> simp[] >>
     irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
     simp[] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def, is_terminator_def]) >>
  conj_tac
  >- suspend "entry"
  >> suspend "keys"
QED

Resume focus_native_failed_row_step[entry]:
  `exec_block (fuel-e) C7 bb start = r` by
    (`exec_block (fuel-e) C7 bb start =
      dftIndexedExec$dft_exec_suffix (fuel-e) C7 (z ++ DROP k xs) start` by
       (irule dftIndexedExecTheory.dft_exec_suffix_boundary >>
        simp[DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
     pop_assum (fn th => pure_rewrite_tac[th, dftIndexedExecTheory.dft_exec_suffix_append]) >>
     qmatch_goalsub_abbrev_tac `FOLDR _ c z start` >>
     `!zs s. EVERY (\i. ~is_terminator i.inst_opcode) zs /\
       (!u. FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK zs s <> OK u) ==>
       FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) c zs s =
       FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK zs s` by
       (POP_ASSUM_LIST (K all_tac) >>
        Induct >- simp[] >> rpt gen_tac >>
        simp[dftIndexedExecTheory.dft_exec_cons_def] >>
        Cases_on `step_inst (fuel-e) C7 h s` >> simp[] >>
        strip_tac >> gvs[] >> first_x_assum irule >> simp[]) >>
     qpat_assum `!zs s. _` (qspecl_then [`z`,`start`] mp_tac) >> simp[]) >>
  `trace_block a e (fuel-e) C7 sf bb start = trace_block a e (fuel-e) C7 sf trunc start` by
    (`start.vs_inst_idx + LENGTH z <= LENGTH bb.bb_instructions` by
       simp[LENGTH_DROP] >>
     `TAKE (LENGTH z) (DROP start.vs_inst_idx bb.bb_instructions) = z` by
       (qpat_assum `start.vs_inst_idx = phi` (fn th => pure_rewrite_tac[th]) >>
        qpat_assum `DROP phi bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
        simp[TAKE_APPEND1]) >>
     `TAKE (start.vs_inst_idx + LENGTH z) bb.bb_instructions = trunc.bb_instructions` by
       (qpat_assum `TAKE (LENGTH z) _ = z` (fn th => pure_rewrite_tac[TAKE_SUM, th]) >>
        simp[Abbr `trunc`]) >>
     `trunc = bb with bb_instructions := TAKE (start.vs_inst_idx + LENGTH z) bb.bb_instructions` by
       (qpat_assum `TAKE _ _ = trunc.bb_instructions` (fn th => pure_rewrite_tac[th]) >>
        simp[Abbr `trunc`]) >>
     pop_assum SUBST1_TAC >> irule focus_native_failed_slice_trace >>
     qpat_assum `TAKE (LENGTH z) _ = z` (fn th => pure_rewrite_tac[th]) >>
     asm_rewrite_tac[] >> qexists `r` >> asm_rewrite_tac[]) >>
  drule_all_then (fn th => simp[th]) trace_blocks_enter >>
  Cases_on `r` >> gvs[Abbr `start`, Abbr `phi`]
QED

Resume focus_native_failed_row_step[keys]:
  qpat_x_assum `e = SUC depth` kall_tac >>
  `trunc.bb_instructions = ps ++ TAKE k xs` by
    simp[Abbr `trunc`, TAKE_APPEND1, listTheory.APPEND_ASSOC, TAKE_DROP] >>
  `TAKE (LENGTH ps - phi) (DROP start.vs_inst_idx trunc.bb_instructions) = DROP phi ps /\
   start.vs_inst_idx + (LENGTH ps - phi) <= LENGTH trunc.bb_instructions` by
    simp[DROP_APPEND1, TAKE_APPEND, LENGTH_DROP] >>
  `trace_gas (trace_block a e (fuel-e) C7 sf trunc start) =
   trace_gas (trace_block a e (fuel-e) C7 sf trunc bs)` by
    (irule dftPacketClosedRowNativeTheory.native_trace_block_pseudo_skip >>
     qexists `LENGTH ps - phi` >> gvs[]) >>
  `trace_block a e (fuel-e) C7 sf trunc bs =
   trace_block a e (fuel-e) C7 sf
     <|bb_label := be.vs_current_bb; bb_instructions :=
       REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|> bs` by
    (irule dftPacketClosedRowNativeTheory.native_trace_block_suffix_cong >>
     gvs[Abbr `bs`, DROP_APPEND]) >>
  simp[] >> qunabbrev_tac `bs` >>
  MATCH_MP_TAC focus_retained_row_slice_keys >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP ms_tab (a,e) = SOME _` (irule_at Any) >> simp[]
QED

Finalise focus_native_failed_row_step

Theorem focus_native_row_call_descent:
  !C7 sf v bb sp z caller c nm ops csf args cs a depth n.
  let phi = phi_prefix_length bb.bb_instructions;
      e = SUC depth in
  let start = sp with vs_inst_idx := phi in
  let Tz = trace_block a e n C7 sf
    (bb with bb_instructions := TAKE phi bb.bb_instructions ++ z) start in
  lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis v bb.bb_instructions = OK sp /\
  TAKE (LENGTH z) (DROP phi bb.bb_instructions) = z /\
  phi + LENGTH z <= LENGTH bb.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode) z /\
  FOLDR (dftIndexedExec$dft_exec_cons n C7) OK z start = OK caller /\
  get_instruction bb caller.vs_inst_idx = SOME c /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C7.ctx_functions = SOME csf /\
  eval_operands ops caller = SOME args /\ setup_callee csf args caller = SOME cs ==>
  ?after. trace_gas (trace_blocks a depth (SUC n) C7 sf v) =
    trace_gas Tz ++ trace_gas (trace_blocks ((e,c.inst_id)::a) e n C7 csf cs) ++ after
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `start = sp with vs_inst_idx := phi` >>
  `start.vs_inst_idx = phi` by simp[Abbr `start`] >>
  `trace_block a (SUC depth) n C7 sf bb start =
    trace_block a (SUC depth) n C7 sf
      (bb with bb_instructions := TAKE (start.vs_inst_idx + LENGTH z) bb.bb_instructions) start ++
    trace_block a (SUC depth) n C7 sf bb caller` by
    (irule (cj 2 dftPacketNativeSliceTheory.native_trace_block_prefix_split) >> simp[]) >>
  drule_all_then (fn th => once_rewrite_tac[th]) trace_blocks_enter >>
  gvs[Abbr `start`, Abbr `phi`, TAKE_SUM] >>
  drule_then (fn th => once_rewrite_tac[th]) trace_block_visit >>
  drule_all_then (fn th => once_rewrite_tac[th]) trace_step_invoke >>
  simp[dftGasFromListReadingsTheory.trace_gas_append,
       dftGasFromListReadingsTheory.trace_gas_cons, visit_gas_def, APPEND_ASSOC]
QED

Theorem focus_fixed_filling_stage7_terminates:
  ctx_sim_fuel I D src C7
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
                vs_initial_fmp := fmp|>)
    (vs0 with vs_gas_readings := raw ++ [0w]) /\
  terminates (run_context fr src
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
                vs_initial_fmp := fmp|>)) /\
  C7.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  fn_entry_label root_sf = SOME lbl7 /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> ==>
  terminates (run_blocks (MAX N fr) C7 root_sf
    (root_entry with vs_gas_readings := raw ++ [0w]))
Proof
  strip_tac >>
  `terminates (run_context fr C7 (vs0 with vs_gas_readings := raw ++ [0w]))` by
    (fs[ctx_sim_fuel_def] >> metis_tac[dead_result_rel_terminates]) >>
  `terminates (run_blocks fr C7 root_sf
     (root_entry with vs_gas_readings := raw ++ [0w]))` by
    (qpat_x_assum `terminates (run_context fr C7 _)` mp_tac >>
     simp[run_context_def, run_function_def]) >>
  `run_blocks (MAX N fr) C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w]) =
   run_blocks fr C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w])` by
    (irule run_blocks_terminates_mono >> simp[MAX_LE]) >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Theorem focus_native_preceding_row_record[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 body count front closed brest ds later.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
  order = ds ++ e::later ==>
  e = SUC (inc + LENGTH ds) /\
  (ds = [] ==> hin = entry) /\
  (ds <> [] ==> ~hin.vs_halted /\
    ?pb pt pps pxs pys prho pin ph pbe pc pu.
      FLOOKUP blocks (a,LAST ds) =
        SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu))
Proof
  rpt gen_tac >> strip_tac >>
  `order = GENLIST (\i. inc + SUC i) (LENGTH order)` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
          (mp_then Any ACCEPT_TAC (cj 6 th)))) >>
  `!i. i < LENGTH order ==> EL i order = inc + SUC i` by
    (rpt strip_tac >> qpat_assum `order = GENLIST _ _`
       (fn th => pure_once_rewrite_tac [th]) >> simp[EL_GENLIST]) >>
  `e = SUC (inc + LENGTH ds)` by
    (qpat_x_assum `!i. i < LENGTH order ==> _` (qspec_then `LENGTH ds` mp_tac) >>
     simp[EL_APPEND2]) >>
  `ds <> [] ==> LAST ds = e - 1` by
    (strip_tac >> `PRE (LENGTH ds) < LENGTH ds /\ SUC (PRE (LENGTH ds)) = LENGTH ds` by
       (Cases_on `ds` >> gvs[]) >>
     qpat_x_assum `!i. i < LENGTH order ==> _` (qspec_then `PRE (LENGTH ds)` mp_tac) >>
     simp[EL_APPEND1, GSYM LAST_EL] >> decide_tac) >>
  simp[] >>
  `if e = SUC inc then hin = entry else
    ?pb pt pps pxs pys prho pin ph pbe pc pu.
      FLOOKUP blocks (a,e-1) =
        SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
      ~hin.vs_halted` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,_,_,_,_,_)`
          (mp_then Any strip_assume_tac th)) >>
     qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
       (fn th => qpat_x_assum `FLOOKUP acts a = SOME _` (mp_tac o REWRITE_RULE [th])) >>
     simp[NoAsms] >> strip_tac >> (simp[])) >>
  Cases_on `ds` >> gvs[LENGTH_NON_NIL]
QED

Theorem focus_native_rooted_snoc_success[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  rooted_eval fuel C7 [(sf,rows ++ [(bb,e,z)],NONE)] ent = (ev,OK v) ==>
  ?prior u sp.
    rooted_eval fuel C7 [(sf,rows,NONE)] ent = (prior,OK u) /\
    eval_phis u bb.bb_instructions = OK sp /\
    FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v /\
    ev = prior ++ gas_events_block (fuel-e) C7 sf.fn_name
      (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
         bb.bb_instructions ++ z)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`rooted_eval = _`, `plan_eval = _`, `row_eval = _`,
     `rooted_eval fuel C7 _ ent = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL next` >>
  Cases_on `FOLDL next ([],OK ent) rows` >>
  rename1 `FOLDL next ([],OK ent) rows = (prior,r)` >>
  Cases_on `r` >> gvs[AllCaseEqs(), Abbr `next`, FOLDL_APPEND] >>
  Cases_on `eval_phis v' bb.bb_instructions` >> gvs[]
QED

Theorem focus_native_closed_row_data[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys row_order hin h0 body_entry ct post rest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,ct,OK post,T,SOME rest) ==>
  ?be hbe sp ms ks. body_entry = SOME (be,hbe) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    e <= N /\ lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
    bb.bb_instructions = ps ++ xs /\ bb_well_formed bb /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    be.vs_inst_idx = LENGTH ps /\
    eval_phis hin (ps ++ ys) = OK sp /\
    FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`,
     `o1_ctx_shape C7`, `FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM ks_tab`,
     `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,_,F,NONE)`,
     `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
     `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,_,OK post,T,SOME rest)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `body_entry <> NONE` by
    (strip_tac >> gvs[] >>
     qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,T,_)`
         (mp_then Any strip_assume_tac th)) >> gvs[]) >>
  Cases_on `body_entry` >> gvs[] >> PairCases_on `x` >>
  qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
    (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (mp_then Any assume_tac (cj 1 th))) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,T,_)`
      (mp_then Any strip_assume_tac th)) >>
  `?ms. FLOOKUP ms_tab (a,e) = SOME ms` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ks. FLOOKUP ks_tab (a,e) = SOME ks` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  gvs[] >>
  `wf_function sf` by metis_tac[dftContractGasTheory.o1_ctx_shape_wf_functions, EVERY_MEM] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def] >>
  simp[] >> metis_tac[wf_function_def]
QED

(* The construction consumes the same selected witness, before raw and D. *)
Theorem focus_native_closed_row_eval[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys row_order hin h0 body_entry ct post rest depth F gs tail prior ev v.
  let phi = phi_prefix_length bb.bb_instructions in
  let z = DROP phi bb.bb_instructions;
      u = hin with vs_gas_readings := gs ++ tail in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,ct,OK post,T,SOME rest) /\
  e = SUC depth /\ N <= F /\ ~post.vs_halted /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (THE (FLOOKUP ms_tab (a,e)))) gs /\
  (?sp. eval_phis u bb.bb_instructions = OK sp /\
    FOLDR (dftIndexedExec$dft_exec_cons (F-e) C7) OK z
      (sp with vs_inst_idx := phi) = OK v /\
    ev = prior ++ gas_events_block (F-e) C7 sf.fn_name
      (bb with bb_instructions := TAKE phi bb.bb_instructions ++ z)
      (sp with vs_inst_idx := phi)) ==>
  v = post with vs_gas_readings := tail /\
  ?G. trace_gas (trace_blocks a depth (F-depth) C7 sf u) =
      G ++ trace_gas (trace_blocks a e (F-e) C7 sf v) /\
    MAP FST G = FLAT (THE (FLOOKUP ks_tab (a,e))) /\
    LENGTH ev = LENGTH prior + LENGTH G
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all focus_native_closed_row_data >> strip_tac >>
  qmatch_asmsub_rename_tac `dft_exec_cons (fuel-e) C7` >>
  `?sq. eval_phis (hin with vs_gas_readings := gs ++ tail) bb.bb_instructions = OK sq /\
    FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK
      (DROP (phi_prefix_length bb.bb_instructions) ps)
      (sq with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
       OK (be with vs_gas_readings := gs ++ tail)` by
    (qpat_assum `bb.bb_instructions = ps ++ xs` (fn th => rewrite_tac[th]) >>
     irule dftPacketEntryReplayTheory.dft_packet_body_entry_replay >>
     qpat_assum `FOLDR (dft_exec_cons (N-e) C8) OK _ _ = OK be` (irule_at Any) >> simp[]) >>
  `sq = sp` by metis_tac[exec_result_11] >>
  qpat_x_assum `sq = sp` SUBST_ALL_TAC >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `start = sp with vs_inst_idx := phi` >>
  qabbrev_tac `bs = be with vs_gas_readings := gs ++ tail` >>
  `phi <= LENGTH ps` by
    (`EVERY (\i. i.inst_opcode <> PHI) xs` by
       (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
     simp[Abbr `phi`, dftIndexedExecTheory.dft_phi_prefix_append,
          venomExecProofsTheory.phi_prefix_length_le]) >>
  `ps ++ xs <> [] /\ is_terminator (LAST (ps ++ xs)).inst_opcode` by
    (qpat_assum `bb_well_formed bb`
       (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >> (metis_tac[])) >>
  `xs <> [] /\ is_terminator (LAST xs).inst_opcode` by
    (Cases_on `xs = []`
     >- (`ps <> [] /\ is_terminator (LAST ps).inst_opcode` by metis_tac[APPEND_NIL] >>
         `MEM (LAST ps) ps` by simp[rich_listTheory.MEM_LAST_NOT_NIL] >>
         `is_pseudo (LAST ps).inst_opcode` by
           (qpat_assum `EVERY _ ps`
              (qspec_then `LAST ps` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
         qpat_x_assum `is_pseudo (LAST ps).inst_opcode` mp_tac >>
         qpat_x_assum `is_terminator (LAST ps).inst_opcode` mp_tac >>
         Cases_on `(LAST ps).inst_opcode` >> simp[is_pseudo_def, is_terminator_def]) >>
     simp[] >> metis_tac[rich_listTheory.LAST_APPEND_NOT_NIL]) >>
  `DROP phi bb.bb_instructions = DROP phi ps ++ xs` by
    simp[DROP_APPEND1] >>
  `exec_block (fuel-e) C7 bb start = OK v` by
    (irule EQ_TRANS >>
     qexists `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK
       (DROP phi bb.bb_instructions) start` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >>
     simp[Abbr `start`, DROP_APPEND1, rich_listTheory.LAST_APPEND_NOT_NIL] >>
     `0 < LENGTH xs` by (Cases_on `xs` >> fs[]) >>
     qpat_assum `phi <= LENGTH ps` mp_tac >>
     qpat_assum `0 < LENGTH xs` mp_tac >> decide_tac) >>
  `TAKE (LENGTH ps - phi) (DROP start.vs_inst_idx bb.bb_instructions) = DROP phi ps /\
   start.vs_inst_idx + (LENGTH ps - phi) <= LENGTH bb.bb_instructions` by
    simp[Abbr `start`, DROP_APPEND1, TAKE_APPEND, LENGTH_DROP] >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK xs bs = OK v` by
    (`exec_block (fuel-e) C7 bb start = exec_block (fuel-e) C7 bb bs` by
       (irule dftPacketClosedRowNativeTheory.native_exec_block_prefix_skip >>
        qexists `LENGTH ps - phi` >> simp[IgnAsm `e = SUC depth`] >>
        irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
        simp[EVERY_DROP] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
        simp[is_pseudo_def, is_terminator_def]) >>
     `exec_block (fuel-e) C7 bb bs = FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK xs bs` by
       (irule dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >>
        simp[Abbr `bs`, DROP_APPEND]) >> metis_tac[]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs` by
    (qpat_assum `FLOOKUP ms_tab (a,e) = SOME ms` (fn th =>
       qpat_assum `LIST_REL _ (FLAT (THE (FLOOKUP ms_tab (a,e)))) gs`
         (mp_tac o REWRITE_RULE [th, optionTheory.THE_DEF])) >> simp[]) >>
  `dftGasToListReplay$residual_result tail (OK post) (OK v) /\
   MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb start)) = FLAT ks` by
    (qunabbrev_tac `start` >> qunabbrev_tac `phi` >> qunabbrev_tac `bs` >>
     conj_tac >>
     FIRST [irule (cj 2 (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_closed_row_step))),
            irule (cj 3 (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_closed_row_step)))] >>
     qpat_x_assum `body_entry = SOME (be,hbe)` SUBST_ALL_TAC >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     qpat_assum `FOLDR _ OK xs _ = OK v` (irule_at Any) >>
     qpat_assum `eval_phis (hin with vs_gas_readings := gs ++ tail) _ = OK sp`
       (irule_at Any) >>
     qpat_assum `e = SUC depth` (irule_at Any) >>
     simp[IgnAsm `e = SUC depth`, terminates_def]) >>
  `v = post with vs_gas_readings := tail` by
    fs[dftGasToListReplayTheory.residual_result_def, stateEquivTheory.lift_result_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `trace_gas (trace_block a e (fuel-e) C7 sf bb start)` >>
  `fuel-depth = SUC (fuel-e)` by
    (qpat_assum `e = SUC depth` mp_tac >>
     qpat_assum `e <= N` mp_tac >> qpat_assum `N <= fuel` mp_tac >> decide_tac) >>
  `lookup_block (hin with vs_gas_readings := gs ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  `~v.vs_halted` by simp[] >>
  rpt conj_tac
  >- (qpat_assum `fuel-depth = SUC (fuel-e)` SUBST1_TAC >>
      drule_all trace_blocks_enter >>
      disch_then (qspecl_then [`a`,`fuel-e`,`depth`,`C7`]
        (fn th => pure_once_rewrite_tac[th])) >>
      qpat_assum `e = SUC depth` (fn th => pure_once_rewrite_tac[GSYM th]) >>
      qpat_assum `exec_block (fuel-e) C7 bb start = OK v` (mp_tac) >>
      simp[Abbr `start`, Abbr `phi`, IgnAsm `e = SUC depth`])
  >- simp[IgnAsm `e = SUC depth`] >>
  qpat_assum `ev = _` (fn th => rewrite_tac[th]) >>
  simp[TAKE_DROP, gas_events_length, dftGasFromListReadingsTheory.trace_gas_lengths,
       IgnAsm `e = SUC depth`] >>
  qpat_assum `bb.bb_instructions = ps ++ xs` (fn th => pure_once_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem focus_native_preceding_rows:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order res nrest fuel.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ N <= fuel ==>
  !ds e later bb bt ps xs ys rho hin h0 body count front closed brest rs tail ev v.
    order = ds ++ e::later /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds)) rs /\
    rooted_eval fuel C7 [(sf,MAP (\f.
      (FST (THE (FLOOKUP blocks (a,f))),f,
       DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
         (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds,NONE)]
      (entry with vs_gas_readings := rs ++ tail) = (ev,OK v) ==>
    e = SUC (inc + LENGTH ds) /\ v = hin with vs_gas_readings := tail /\
    ?G. trace_gas (trace_blocks a inc (fuel-inc) C7 sf
           (entry with vs_gas_readings := rs ++ tail)) =
          G ++ trace_gas (trace_blocks a (inc + LENGTH ds)
                         (fuel-(inc + LENGTH ds)) C7 sf v) /\
        MAP FST G = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) /\
        LENGTH G = LENGTH ev
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `ds` using SNOC_INDUCT
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      `order = [] ++ e::later` by simp[] >>
      drule_all focus_native_preceding_row_record >> simp[] >> strip_tac >>
      `rooted_eval fuel C7 [(sf,[],NONE)] (entry with vs_gas_readings := tail) =
         ([],OK (entry with vs_gas_readings := tail))` by
        (qhdtm_assum `dft_focus_packet_rel`
           (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
         qpat_assum `rooted_eval = _` (fn th => rewrite_tac[th]) >>
         qpat_assum `plan_eval = _` (fn th => rewrite_tac[th]) >> simp[]) >>
      gvs[] >> qexists `[]` >> simp[])
  >> rewrite_tac[listTheory.SNOC_APPEND] >>
  rpt gen_tac >> strip_tac >>
  drule_all focus_native_preceding_row_record >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [rich_listTheory.LAST_APPEND_NOT_NIL]) >>
  rename1 `FLOOKUP blocks (a,f) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu)` >>
  `order = ds ++ f::e::later` by
    (qpat_assum `order = (ds ++ [f]) ++ e::later` mp_tac >>
     rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `LIST_REL _ _ rs` mp_tac >>
  rewrite_tac[MAP_APPEND, FLAT_APPEND, MAP, FLAT, APPEND_NIL] >>
  simp[Once LIST_REL_SPLIT1, NoAsms] >> strip_tac >>
  qpat_x_assum `rooted_eval fuel C7 _ _ = (ev,OK v)` mp_tac >>
  qpat_assum `FLOOKUP blocks (a,f) = SOME _`
    (fn th => simp[NoAsms, MAP_APPEND, th]) >> strip_tac >>
  drule_all focus_native_rooted_snoc_success >> strip_tac >>
  qpat_x_assum `rs = _` SUBST_ALL_TAC >>
  qpat_x_assum `rooted_eval fuel C7 _ _ = (prior,OK u)`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  qpat_x_assum `!e later bb bt ps xs ys rho hin h0 body count front closed brest rs tail ev v. _`
    drule_all >> strip_tac >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  `v = hin with vs_gas_readings := tail /\
   ?H. trace_gas (trace_blocks a (inc + LENGTH ds) (fuel-(inc + LENGTH ds)) C7 sf
                 (pin with vs_gas_readings := ys2 ++ tail)) =
       H ++ trace_gas (trace_blocks a f (fuel-f) C7 sf v) /\
       MAP FST H = FLAT (THE (FLOOKUP ks_tab (a,f))) /\
       LENGTH ev = LENGTH prior + LENGTH H` by
    (MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_closed_row_eval)) >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,f) = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     simp[IgnAsm `f = SUC (inc + LENGTH ds)`] >> first_assum ACCEPT_TAC) >>
  `inc + (LENGTH ds + 1) = f` by simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `G ++ H` >>
  conj_tac >-
    (qpat_assum `inc + (LENGTH ds + 1) = f` SUBST1_TAC >>
     rewrite_tac[GSYM APPEND_ASSOC] >>
     qpat_assum `trace_gas (trace_blocks a inc _ C7 sf _) = G ++ _` SUBST1_TAC >>
     qpat_assum `trace_gas (trace_blocks a (inc + LENGTH ds) _ C7 sf _) = H ++ _` SUBST1_TAC >>
     REFL_TAC) >>
  simp[MAP_APPEND, IgnAsm `f = SUC (inc + LENGTH ds)`]
QED

Theorem focus_native_open_child_step:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys sched hin h0 ben ct front closed brest ms ks
    q call_h b0 done child_entry csf ctf child_order child_res child_rest
    depth fuel rg tail ev caller.
  let phi = phi_prefix_length bb.bb_instructions in
  let z = DROP phi ps ++ TAKE q xs;
      v = hin with vs_gas_readings := rg ++ tail;
      c = EL q xs;
      cv = child_entry with vs_gas_readings := tail in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,ben,ct,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  FLOOKUP calls (a,e,c.inst_id) = SOME (q,call_h,b0,done,child_entry,NONE) /\
  FLOOKUP acts ((e,c.inst_id)::a) =
    SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
  e = SUC depth /\ N <= fuel /\ done = TAKE ct sched /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r done) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) rg /\
  rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v = (ev,OK caller) ==>
  c.inst_opcode = INVOKE /\
  (?nm ops args.
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C7.ctx_functions = SOME csf /\
    eval_operands ops caller = SOME args /\ setup_callee csf args caller = SOME cv) /\
  rooted_eval fuel C7 [(sf,[(bb,e,z)],SOME c)] v = (ev,OK cv) /\
  ?G after. trace_gas (trace_blocks a depth (fuel-depth) C7 sf v) =
     G ++ trace_gas (trace_blocks ((e,c.inst_id)::a) e (fuel-e) C7 csf cv) ++ after /\
    MAP FST G = FLAT (TAKE q ks) /\ LENGTH G = LENGTH ev
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `z = DROP phi ps ++ TAKE q xs` >>
  qabbrev_tac `v = hin with vs_gas_readings := rg ++ tail` >>
  qabbrev_tac `c = EL q xs` >>
  qabbrev_tac `cv = child_entry with vs_gas_readings := tail` >>
  `?be hbe nm ops args. ben = SOME (be,hbe) /\ q < LENGTH xs /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry` by
    suspend "record" >>
  qpat_x_assum `ben = SOME _` SUBST_ALL_TAC >>
  `e <= N /\ lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
    bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
    phi <= LENGTH ps /\ be.vs_inst_idx = LENGTH ps /\
    ?sp. eval_phis v bb.bb_instructions = OK sp /\
      FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (DROP phi ps)
        (sp with vs_inst_idx := phi) = OK (be with vs_gas_readings := rg ++ tail)` by
    suspend "entry" >>
  qabbrev_tac `start = sp with vs_inst_idx := phi` >>
  qabbrev_tac `trunc = bb with bb_instructions := TAKE phi bb.bb_instructions ++ z` >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK z start = OK caller /\
   ev = gas_events_block (fuel-e) C7 sf.fn_name trunc start` by suspend "row" >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP phi ps)` by
    (irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
     simp[EVERY_DROP] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def, is_terminator_def]) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
     (be with vs_gas_readings := rg ++ tail) = OK caller` by suspend "fold" >>
  `?kgss. rg = FLAT kgss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss` by
    metis_tac[dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split] >>
  `caller.vs_gas_readings = tail /\
   trace_gas (trace_block a e (fuel-e) C7 sf
     (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
     (be with vs_gas_readings := rg ++ tail)) = ZIP (FLAT (TAKE q ks),rg) /\
   LENGTH (FLAT (TAKE q ks)) = LENGTH rg` by suspend "prefix" >>
  `lookup_function nm C7.ctx_functions = SOME csf /\
   eval_operands ops caller = SOME args /\ setup_callee csf args caller = SOME cv` by
    suspend "setup" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`nm`,`ops`,`args`] >> simp[]) >>
  conj_tac >- suspend "call_eval" >>
  suspend "trace"
QED

Resume focus_native_open_child_step[record]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` (drule_then mp_tac) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP blocks (a,e) = SOME _`, `FLOOKUP acts ((e,c.inst_id)::a) = SOME _`,
     `Abbrev (c = EL q xs)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  pop_assum strip_assume_tac >> gvs[Abbr `c`] >> metis_tac[]
QED

Resume focus_native_open_child_step[entry]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME _,ct,front,closed,brest)`
       (mp_then Any mp_tac th)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
     `Abbrev (v = _)`, `Abbrev (phi = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  pop_assum strip_assume_tac >> gvs[Abbr `v`, Abbr `phi`] >>
  conj_tac >-
    (`EVERY (\i. i.inst_opcode <> PHI) xs` by
       (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
     simp[dftIndexedExecTheory.dft_phi_prefix_append, venomExecProofsTheory.phi_prefix_length_le]) >>
  irule dftPacketEntryReplayTheory.dft_packet_body_entry_replay >>
  qpat_assum `FOLDR (dft_exec_cons (N-e) C8) OK _ _ = OK be` (irule_at Any) >> simp[]
QED

Resume focus_native_open_child_step[row]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`rooted_eval = _`, `plan_eval = _`, `row_eval = _`, `rooted_eval fuel C7 _ v = _`,
     `eval_phis v bb.bb_instructions = OK sp`, `Abbrev (trunc = _)`,
     `Abbrev (start = _)`, `Abbrev (phi = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[Abbr `trunc`, Abbr `start`, Abbr `phi`, AllCaseEqs()]
QED

Resume focus_native_open_child_step[fold]:
  `!pre s k. EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
      FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) k pre s =
      case FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK pre s of
        OK u => k u | other => other` by
    (POP_ASSUM_LIST (K all_tac) >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     simp_tac bool_ss [dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst (fuel-e) C7 h s` >>
     qpat_x_assum `!s k. _`
       (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,`k`] mp_tac) >> simp[]) >>
  qpat_x_assum `!pre s k. _`
    (qspecl_then [`DROP phi ps`, `start`,
                  `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)`] mp_tac) >>
  qpat_assum `FOLDR _ OK (DROP phi ps) start = _` mp_tac >>
  qpat_assum `EVERY _ (DROP phi ps)` mp_tac >>
  qpat_assum `FOLDR _ OK z start = OK caller` mp_tac >>
  qunabbrev_tac `z` >> POP_ASSUM_LIST (K all_tac) >> simp[FOLDR_APPEND]
QED
Resume focus_native_open_child_step[prefix]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _`
    (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
       (mp_then Any strip_assume_tac th)) >>
  `LENGTH (FLAT (TAKE q ks)) = LENGTH (FLAT (TAKE q ms))` by
    (`LIST_REL (\m keys. LENGTH m = LENGTH keys) (TAKE q ms) (TAKE q ks)` by
       simp[rich_listTheory.LIST_REL_TAKE] >>
     `MAP LENGTH (TAKE q ms) = MAP LENGTH (TAKE q ks)` by
       (pure_once_rewrite_tac[GSYM LIST_REL_eq] >>
        simp[Excl "LIST_REL_eq", LIST_REL_MAP1, LIST_REL_MAP2, combinTheory.o_DEF]) >>
     simp[rich_listTheory.LENGTH_FLAT]) >>
  `LENGTH (FLAT (TAKE q ms)) = LENGTH rg` by
    (qpat_assum `LIST_REL _ (FLAT (TAKE q ms)) rg` (MATCH_ACCEPT_TAC o MATCH_MP LIST_REL_LENGTH)) >>
  qpat_x_assum `rg = FLAT kgss` SUBST_ALL_TAC >>
  qpat_x_assum `!F k kgss tail. _`
    (qspecl_then [`fuel`,`q`,`kgss`,`tail`] mp_tac) >>
  `q <= LENGTH xs` by decide_tac >>
  qpat_assum `done = TAKE ct sched` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  simp[IgnAsm `e = SUC depth`] >>
  strip_tac >>
  qpat_x_assum `!u. FOLDR _ OK (TAKE q xs) _ = OK u ==> _`
    (qspec_then `caller` mp_tac) >>
  simp[IgnAsm `e = SUC depth`]
QED
Resume focus_native_open_child_step[setup]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `rg = FLAT kgss` SUBST_ALL_TAC >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = _ /\ FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
    (fn th => qpat_assum `FLOOKUP acts ((e,c.inst_id)::a) = SOME _`
       (mp_then Any strip_assume_tac th)) >>
  qunabbrev_tac `c` >>
  drule_all dftPacketCalleeAlignmentTheory.dft_packet_callee_alignment >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C7.ctx_functions)` by
    (qpat_assum `o1_ctx_shape C7` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[o1_ctx_shape_def,venomWfTheory.ctx_wf_def,
          venomWfTheory.ctx_distinct_fn_names_def,venomInstTheory.ctx_fn_names_def]) >>
  `lookup_function nm C7.ctx_functions = SOME csf` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM csf C7.ctx_functions`, `lookup_function nm C8.ctx_functions = SOME ctf`,
        `ALL_DISTINCT _`, `dft_fn_rel csf ctf`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[o1ScheduleDecompHelpersTheory.lookup_function_member_iff,dftRunRelTheory.dft_fn_rel_def] >>
     metis_tac[fmpAnalysisPropsTheory.lookup_function_name]) >>
  rename1 `setup_callee found args caller = SOME (child_entry with vs_gas_readings := _)` >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`lookup_function nm C7.ctx_functions = SOME csf`,
     `lookup_function nm C7.ctx_functions = SOME found`,
     `setup_callee found args caller = SOME _`,
     `eval_operands ops caller = SOME args`, `caller.vs_gas_readings = tail`,
     `Abbrev (cv = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[markerTheory.Abbrev_def]
QED
Resume focus_native_open_child_step[call_eval]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`rooted_eval = _`, `plan_eval = _`, `row_eval = _`, `call_setup = _`,
     `eval_phis v bb.bb_instructions = OK sp`, `Abbrev (trunc = _)`,
     `Abbrev (start = _)`, `Abbrev (phi = _)`, `FOLDR _ OK z start = OK caller`,
     `ev = gas_events_block _ _ _ trunc start`, `decode_invoke c = SOME (nm,ops)`,
     `lookup_function nm C7.ctx_functions = SOME csf`,
     `eval_operands ops caller = SOME args`, `setup_callee csf args caller = SOME cv`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[Abbr `trunc`, Abbr `start`, Abbr `phi`]
QED
Resume focus_native_open_child_step[trace]:
  `LENGTH z = LENGTH ps - phi + q` by simp[Abbr `z`,LENGTH_TAKE,MIN_DEF] >>
  `phi + LENGTH z = LENGTH ps + q` by decide_tac >>
  `phi + LENGTH z <= LENGTH bb.bb_instructions` by simp[] >>
  `trunc.bb_instructions = TAKE (LENGTH ps + q) bb.bb_instructions` by
    simp[Abbr `trunc`, Abbr `z`, TAKE_APPEND1, rich_listTheory.TAKE_APPEND2] >>
  `TAKE (LENGTH z) (DROP phi bb.bb_instructions) = z` by
    simp[Abbr `z`, DROP_APPEND1, rich_listTheory.TAKE_APPEND2] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) z` by simp[Abbr `z`, EVERY_APPEND] >>
  `caller.vs_inst_idx = LENGTH ps + q` by
    (`start.vs_inst_idx = phi` by simp[Abbr `start`] >>
     `caller.vs_inst_idx = start.vs_inst_idx + LENGTH z` suffices_by simp[] >>
     irule (cj 1 dftPacketNativeSliceTheory.native_trace_block_prefix_split) >>
     metis_tac[]) >>
  `get_instruction bb caller.vs_inst_idx = SOME c` by
    simp[Abbr `c`, get_instruction_def, rich_listTheory.EL_APPEND2] >>
  qabbrev_tac `G = trace_gas (trace_block a e (fuel-e) C7 sf trunc start)` >>
  `?after. trace_gas (trace_blocks a depth (fuel-depth) C7 sf v) =
      G ++ trace_gas (trace_blocks ((e,c.inst_id)::a) e (fuel-e) C7 csf cv) ++ after` by
    (`fuel-depth = SUC (fuel-e)` by decide_tac >>
     qunabbrev_tac `G` >> qunabbrev_tac `trunc` >>
     qunabbrev_tac `start` >> qunabbrev_tac `phi` >>
     qpat_x_assum `fuel-depth = SUC (fuel-e)` SUBST1_TAC >>
     qpat_x_assum `e = SUC depth` SUBST_ALL_TAC >>
     irule (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_row_call_descent)) >>
     qpat_assum `setup_callee csf args caller = SOME cv` (irule_at Any) >>
     qpat_assum `FOLDR _ OK z _ = OK caller` (irule_at Any) >>
     qpat_assum `eval_phis v bb.bb_instructions = OK sp` (irule_at Any) >>
     qpat_assum `decode_invoke c = SOME (nm,ops)` (irule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  qexistsl [`G`,`after`] >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >-
    simp[Abbr `G`,dftGasFromListReadingsTheory.trace_gas_lengths,gasEventsTheory.gas_events_length] >>
  `G = ZIP (FLAT (TAKE q ks),rg)` suffices_by simp[MAP_ZIP] >>
  `trunc = bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions` by
    simp[venomInstTheory.basic_block_component_equality,Abbr `trunc`] >>
  `trace_gas (trace_block a e (fuel-e) C7 sf trunc start) =
   trace_gas (trace_block a e (fuel-e) C7 sf trunc (be with vs_gas_readings := rg ++ tail))` by
    (irule dftPacketClosedRowNativeTheory.native_trace_block_pseudo_skip >>
     qexists `LENGTH ps - phi` >>
     simp[Abbr `start`, IgnAsm `e = SUC depth`, LENGTH_TAKE, MIN_DEF,
          listTheory.TAKE_DROP_SWAP, TAKE_TAKE, TAKE_APPEND1, EVERY_DROP]) >>
  qpat_assum `Abbrev (G = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  metis_tac[]
QED
Finalise focus_native_open_child_step

(* A failed selected row has no native continuation at its matched input. *)
Theorem focus_native_cut_failure_row:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys sched hin h0 bodyrec ct front closed brest ms ks depth fuel
    z mr kr rowgs tail ev r.
  let phi = phi_prefix_length bb.bb_instructions;
      v = hin with vs_gas_readings := rowgs ++ tail in
  let native_gas = trace_gas (trace_blocks a depth (fuel-depth) C7 sf v) in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  e = SUC depth /\ e <= N /\ N <= fuel /\
  ((e <> LAST order /\ z = DROP phi bb.bb_instructions /\ mr = FLAT ms /\ kr = FLAT ks) \/
   (?be hbe k. bodyrec = SOME (be,hbe) /\ k <= LENGTH xs /\
      z = DROP phi ps ++ TAKE k xs /\ mr = FLAT (TAKE k ms) /\ kr = FLAT (TAKE k ks) /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!t. t < k /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
   (bodyrec = NONE /\ mr = [] /\ kr = [] /\
    z = DROP phi (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h =>
      st.vs_inst_idx) ps))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) mr rowgs /\
  rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v = (ev,r) /\ terminates r /\ (!u. r <> OK u) ==>
  (?rest. kr = MAP FST native_gas ++ rest) /\ LENGTH native_gas = LENGTH ev
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qabbrev_tac `phi = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `v = hin with vs_gas_readings := rowgs ++ tail` >>
  qabbrev_tac `native_gas = trace_gas (trace_blocks a depth (fuel-depth) C7 sf v)` >>
  qabbrev_tac `trunc = bb with bb_instructions := TAKE phi bb.bb_instructions ++ z` >>
  `bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
   EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys /\ lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
   (?sp0. eval_phis hin bt.bb_instructions = OK sp0 /\
     (!be hbe. bodyrec = SOME (be,hbe) ==> be.vs_inst_idx = LENGTH ps /\
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (DROP phi ps)
         (sp0 with vs_inst_idx := phi) = OK be))` by suspend "row_data" >>
  `phi <= LENGTH ps /\ phi = phi_prefix_length bt.bb_instructions` by
    simp[Abbr `phi`, dftIndexedExecTheory.dft_phi_prefix_append,
         venomExecProofsTheory.phi_prefix_length_le] >>
  `eval_phis v bb.bb_instructions = OK (sp0 with vs_gas_readings := rowgs ++ tail)` by
    suspend "phis" >>
  qabbrev_tac `start = sp0 with <|vs_gas_readings := rowgs ++ tail; vs_inst_idx := phi|>` >>
  `!zs u. EVERY (\i. is_pseudo i.inst_opcode) zs /\
    FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK zs (sp0 with vs_inst_idx := phi) = OK u ==>
    FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK zs start =
      OK (u with vs_gas_readings := rowgs ++ tail)` by
    (rpt strip_tac >> drule_all dftPacketEntryReplayTheory.dft_packet_pseudo_fold_gas >>
     disch_then (qspecl_then [`rowgs ++ tail`,`fuel-e`,`C7`] mp_tac) >>
     simp[Abbr `start`, venom_state_component_equality]) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK z start = r /\
   ev = gas_events_block (fuel-e) C7 sf.fn_name trunc start` by suspend "eval" >>
  qpat_x_assum `(_ /\ _ /\ _ /\ _) \/ _ \/ _` strip_assume_tac
  >- suspend "complete"
  >- suspend "body"
  >> suspend "pseudo"
QED
Resume focus_native_cut_failure_row[row_data]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`
       (mp_then Any mp_tac th)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts a = SOME _`, `Abbrev (v = _)`, `Abbrev (phi = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> pop_assum strip_assume_tac >>
  gvs[Abbr `v`,Abbr `phi`] >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\ EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  simp[dftIndexedExecTheory.dft_phi_prefix_append] >> rpt strip_tac >>
  gvs[dftIndexedExecTheory.dft_phi_prefix_append]
QED
Resume focus_native_cut_failure_row[phis]:
  `eval_phis hin ps = OK sp0` by gvs[dftIndexedExecTheory.dft_eval_phis_append] >>
  qspecl_then [`ps`,`hin`,`rowgs ++ tail`] mp_tac dftGasToListReplayTheory.replay_phis >>
  simp[Abbr `v`,dftIndexedExecTheory.dft_eval_phis_append,
       dftGasToListReplayTheory.residual_result_def] >>
  Cases_on `eval_phis (hin with vs_gas_readings := rowgs ++ tail) ps` >>
  simp[stateEquivTheory.lift_result_def]
QED
Resume focus_native_cut_failure_row[eval]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`rooted_eval = _`, `plan_eval = _`, `row_eval = _`, `rooted_eval fuel C7 _ v = _`,
     `eval_phis v bb.bb_instructions = OK _`, `Abbrev (trunc = _)`,
     `Abbrev (start = _)`, `Abbrev (phi = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[Abbr `trunc`, Abbr `start`, Abbr `phi`, AllCaseEqs(), venom_state_component_equality]
QED
Resume focus_native_cut_failure_row[complete]:
  `?post rest. FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,OK post,T,SOME rest)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`
          (mp_then Any mp_tac th)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
        `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`,
        `e <> LAST order`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> pop_assum strip_assume_tac >>
     gvs[] >> Cases_on `brest` >> gvs[]) >>
  `?be hbe. bodyrec = SOME (be,hbe)` by
    (drule_all focus_native_closed_row_data >> metis_tac[]) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (DROP phi ps) start =
    OK (be with vs_gas_readings := rowgs ++ tail)` by
    (first_x_assum irule >> simp[EVERY_DROP]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP phi ps)` by
    (irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
     simp[EVERY_DROP] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def,is_terminator_def]) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK xs
      (be with vs_gas_readings := rowgs ++ tail) = r` by
    (`z = DROP phi ps ++ xs` by simp[DROP_APPEND1, IgnAsm `phi = phi_prefix_length bt.bb_instructions`] >>
     qpat_assum `FOLDR _ OK z start = r` mp_tac >>
     pop_assum (fn th => pure_once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[FOLDR_APPEND] >>
     simp[Once dftRunRelTheory.dft_exec_prefix_continue, IgnAsm `e = SUC depth`]) >>
  `dftGasToListReplay$residual_result tail (OK post) r` by
    ((qpat_assum `FOLDR _ OK xs _ = r` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule dft_packet_closed_row_residual >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `bodyrec = SOME (be,hbe)` SUBST_ALL_TAC >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,OK post,T,SOME rest)` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP ms_tab (a,e) = SOME _` (irule_at Any) >>
     simp[] >> qexists `fuel-e` >> simp[] >> (gvs[dft_packet_closed_row_residual]))) >>
  Cases_on `r` >> gvs[dftGasToListReplayTheory.residual_result_def, stateEquivTheory.lift_result_def]
QED
Resume focus_native_cut_failure_row[body]:
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (DROP phi ps) start =
    OK (be with vs_gas_readings := rowgs ++ tail)` by
    (first_x_assum irule >> simp[EVERY_DROP]) >>
  `fuel-depth = SUC (fuel-e)` by decide_tac >>
  `trace_blocks a depth (SUC (fuel-e)) C7 sf v = trace_block a e (fuel-e) C7 sf trunc start /\
   ?rest. kr = MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf trunc start)) ++ rest` by
    (qpat_assum `kr = _` SUBST1_TAC >>
     `start = (sp0 with vs_gas_readings := rowgs ++ tail) with vs_inst_idx := phi` by
       simp[Abbr `start`, venom_state_component_equality] >>
     pop_assum SUBST1_TAC >> qunabbrev_tac `trunc` >> qunabbrev_tac `phi` >> qunabbrev_tac `v` >>
     MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_failed_row_step)) >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `bodyrec = SOME _` SUBST_ALL_TAC >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     qexistsl [`r`,`ms`] >>
     `start = sp0 with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
                         vs_gas_readings := rowgs ++ tail|>` by
       simp[Abbr `start`,venom_state_component_equality] >>
     pop_assum (SUBST1_TAC o SYM) >>
     qpat_x_assum `mr = FLAT (TAKE k ms)` SUBST_ALL_TAC >>
     `be.vs_inst_idx = LENGTH ps` by metis_tac[] >>
     simp[IgnAsm `e = SUC depth`] >> metis_tac[]) >>
  simp[Abbr `native_gas`,IgnAsm `e = SUC depth`] >>
  simp[gas_events_length,dftGasFromListReadingsTheory.trace_gas_lengths]
QED
Resume focus_native_cut_failure_row[pseudo]:
  `?u. FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK z
      (sp0 with vs_inst_idx := phi) = OK u` by suspend "pseudo_record" >>
  `EVERY (\i. is_pseudo i.inst_opcode) z` by simp[EVERY_DROP,rich_listTheory.EVERY_TAKE] >>
  `FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK z start =
     OK (u with vs_gas_readings := rowgs ++ tail)` by (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED
Resume focus_native_cut_failure_row[pseudo_record]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `a = p /\ e = d` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`
          (mp_then Any strip_assume_tac th)) >>
     qpat_assum `case bodyrec of NONE => _ | SOME (_,_) => _` mp_tac >>
     qpat_assum `bodyrec = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,_,F,NONE)`,
     `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`,
     `a = p`, `e = d`, `bodyrec = NONE`,
     `q8 = JointConfig _ _ _ _ _ _ _ _ _ _ _`,
     `z = DROP phi _`, `phi = phi_prefix_length bt.bb_instructions`,
     `eval_phis hin bt.bb_instructions = OK sp0`,
     `case _ of NONE => _ /\ _ /\ _ /\ FOLDR _ OK _ _ = _ | SOME (_,_) => _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED
Finalise focus_native_cut_failure_row

Theorem focus_native_event_fold[local]:
  !xs step es r.
    (!acc result x. step (acc,result) x =
      (acc ++ FST (step ([],result) x), SND (step ([],result) x))) ==>
    FOLDL step (es,r) xs =
      (es ++ FST (FOLDL step ([],r) xs), SND (FOLDL step ([],r) xs))
Proof
  Induct >- (rpt gen_tac >> disch_tac >> simp[NoAsms]) >>
  map_every qx_gen_tac [`h`,`next`,`es`,`r`] >> disch_tac >>
  Cases_on `next ([],r) h` >> rename1 `next ([],r) h = (more,r')` >>
  `next (es,r) h = (es ++ more,r')` by
    (qpat_assum `!acc result x. next (acc,result) x = _`
       (qspecl_then [`es`,`r`,`h`] mp_tac) >>
     pop_assum (fn th => pure_once_rewrite_tac [th]) >> simp[NoAsms]) >>
  rewrite_tac[FOLDL] >>
  qpat_assum `next (es,r) h = _` SUBST1_TAC >>
  qpat_assum `next ([],r) h = _` SUBST1_TAC >>
  qpat_assum `!f a b. _ ==> FOLDL f (a,b) xs = _`
    (qspecl_then [`next`,`es ++ more`,`r'`] mp_tac) >>
  qpat_assum `!f a b. _ ==> FOLDL f (a,b) xs = _`
    (qspecl_then [`next`,`more`,`r'`] mp_tac) >>
  qpat_assum `!acc result x. next (acc,result) x = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[APPEND_ASSOC, pairTheory.FST, pairTheory.SND]
QED

Theorem focus_native_event_fold_stopped[local]:
  !xs step es r.
    (!acc bad x. (!v. bad <> OK v) ==> step (acc,bad) x = (acc,bad)) /\
    (!v. r <> OK v) ==> FOLDL step (es,r) xs = (es,r)
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem focus_native_rooted_append[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  rooted_eval fuel C7 (left ++ right) v =
    (let (ev,r) = rooted_eval fuel C7 left v in
       case r of
         OK u => (ev ++ FST (rooted_eval fuel C7 right u), SND (rooted_eval fuel C7 right u))
       | other => (ev,other))
Proof
  strip_tac >> qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `rooted_eval = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  simp[FOLDL_APPEND] >> qmatch_goalsub_abbrev_tac `FOLDL next _ left` >>
  `!acc r x. next (acc,r) x = (acc ++ FST (next ([],r) x), SND (next ([],r) x))` by
    (rpt gen_tac >> PairCases_on `x` >> Cases_on `r` >> simp[NoAsms, Abbr `next`]) >>
  `!acc r x. (!w. r <> OK w) ==> next (acc,r) x = (acc,r)` by
    (rpt gen_tac >> PairCases_on `x` >> Cases_on `r` >> simp[NoAsms, Abbr `next`]) >>
  Cases_on `FOLDL next ([],OK v) left` >> rename1 `_ = (ev,r)` >>
  Cases_on `r` >> simp[NoAsms] >>
  (irule focus_native_event_fold ORELSE irule focus_native_event_fold_stopped) >>
  TRY conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms])
QED

Theorem focus_native_rooted_rows_call_append[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  rooted_eval fuel C7 [(sf,left ++ right,call)] v =
    (let (ev,r) = rooted_eval fuel C7 [(sf,left,NONE)] v in
       case r of
         OK u => (ev ++ FST (rooted_eval fuel C7 [(sf,right,call)] u),
                  SND (rooted_eval fuel C7 [(sf,right,call)] u))
       | other => (ev,other))
Proof
  strip_tac >> qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac) [`rooted_eval = _`, `plan_eval = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp[FOLDL_APPEND] >> qmatch_goalsub_abbrev_tac `FOLDL next _ left` >>
  `!acc r x. next (acc,r) x = (acc ++ FST (next ([],r) x), SND (next ([],r) x))` by
    (rpt gen_tac >> Cases_on `r` >> simp[NoAsms, Abbr `next`]) >>
  `!acc r x. (!w. r <> OK w) ==> next (acc,r) x = (acc,r)` by
    (rpt gen_tac >> Cases_on `r` >> simp[NoAsms, Abbr `next`]) >>
  Cases_on `FOLDL next ([],OK v) left` >> rename1 `_ = (ev,r)` >>
  `FOLDL next (ev,r) right =
     (case r of OK u => (ev ++ FST (FOLDL next ([],OK u) right),
                        SND (FOLDL next ([],OK u) right)) | other => (ev,other))` by
    (Cases_on `r` >> simp[NoAsms] >>
     (irule focus_native_event_fold ORELSE irule focus_native_event_fold_stopped) >>
     TRY conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms])) >>
  pop_assum SUBST1_TAC >> Cases_on `r` >> simp[NoAsms]
QED

Theorem focus_native_rooted_without_call[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  rooted_eval fuel C7 [(sf,rows,call)] v = (ev,OK u) ==>
  ?w. rooted_eval fuel C7 [(sf,rows,NONE)] v = (ev,OK w)
Proof
  strip_tac >> qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac) [`rooted_eval = _`,
    `rooted_eval fuel C7 [(sf,rows,call)] v = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  Cases_on `SND (plan_eval fuel C7 sf.fn_name rows v)` >> gvs[]
QED

Theorem focus_native_live_child_record[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q h b0 done_at_call child_entry ret
    bb bt ps xs ys rho hin h0 body ct front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,ct,front,closed,brest) ==>
  ret = NONE /\ done_at_call = TAKE ct rho
Proof
  rpt gen_tac >> strip_tac >>
  `?k. k < LENGTH p /\ DROP (SUC k) p = a /\ EL k p = (e,cid)` by
    (qpat_x_assum `MEM _ (GENLIST _ _)` mp_tac >> simp[MEM_GENLIST, EQ_SYM_EQ] >>
     disch_then (qx_choose_then `k` strip_assume_tac) >> qexists `k` >>
     `k < LENGTH p` by
       (Cases_on `k < LENGTH p` >> gvs[DROP_LENGTH_TOO_LONG]) >>
     drule rich_listTheory.DROP_CONS_EL >> simp[]) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe ct
      q h b0 done child cid e a. _` (qspec_then `k` mp_tac) >>
  simp[IgnAsm `rooted_eval = _`] >> strip_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP calls (a,e,cid) = SOME (_,_,_,_,_,_)`,
     `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,_,_,_,_)`,
     `FLOOKUP calls (a,LAST _,cid) = SOME (_,_,_,_,_,NONE)`,
     `FLOOKUP blocks (a,LAST _) = SOME (_,_,_,_,_,_,_,_,_,_,_,_,_)`,
     `LAST _ = e`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED

Theorem focus_native_rooted_entry[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  rooted_eval fuel C7 [] v = ([],OK v)
Proof
  simp[dft_focus_packet_rel_def] >> rpt strip_tac >>
  qpat_assum `rooted_eval = _` (fn th => simp[NoAsms,th])
QED

Theorem focus_native_cut_live_level[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys sched hin h0 bodyrec ct front closed brest ds later
    q h b0 done child_entry ret csf ctf child_order child_res child_rest
    fuel ws tail ev u.
  let c = EL q xs in
  let z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs;
      v = entry with vs_gas_readings := ws ++ tail;
      rows = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest) /\
  FLOOKUP calls (a,e,c.inst_id) = SOME (q,h,b0,done,child_entry,ret) /\
  FLOOKUP acts ((e,c.inst_id)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
  MEM ((e,c.inst_id)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  order = ds ++ e::later /\ N <= fuel /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!i. i < q /\ (EL i xs).inst_opcode = INVOKE ==> MEM i done) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) ++
       FLAT (TAKE q (THE (FLOOKUP ms_tab (a,e))))) ws /\
  rooted_eval fuel C7 [(sf,rows ++ [(bb,e,z)],SOME c)] v = (ev,OK u) ==>
  u = child_entry with vs_gas_readings := tail /\
  ?G after. trace_gas (trace_blocks a inc (fuel-inc) C7 sf v) =
    G ++ trace_gas (trace_blocks ((e,c.inst_id)::a) e (fuel-e) C7 csf u) ++ after /\
    MAP FST G = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) ++
      FLAT (TAKE q (THE (FLOOKUP ks_tab (a,e)))) /\ LENGTH G = LENGTH ev
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `c = EL q xs` >>
  qabbrev_tac `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` >>
  qmatch_asmsub_abbrev_tac `rooted_eval fuel C7 [(sf,rows ++ _,SOME c)] _` >>
  `ret = NONE /\ done = TAKE ct sched` by
    (drule_all focus_native_live_child_record >> simp[]) >>
  `?ms ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks` by
    suspend "tables" >>
  qpat_x_assum `LIST_REL _ (_ ++ _) ws` mp_tac >> simp[Once LIST_REL_SPLIT1] >> strip_tac >>
  qpat_x_assum `ws = _` SUBST_ALL_TAC >>
  `?ev0 v0 erow caller. rooted_eval fuel C7 [(sf,rows,NONE)]
        (entry with vs_gas_readings := (ys1 ++ ys2) ++ tail) = (ev0,OK v0) /\
      rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v0 = (erow,OK caller) /\
      rooted_eval fuel C7 [(sf,[(bb,e,z)],SOME c)] v0 = (erow,OK u) /\
      ev = ev0 ++ erow` by suspend "eval" >>
  `e = SUC (inc + LENGTH ds) /\ v0 = hin with vs_gas_readings := ys2 ++ tail /\
   ?G0. trace_gas (trace_blocks a inc (fuel-inc) C7 sf
           (entry with vs_gas_readings := (ys1 ++ ys2) ++ tail)) =
          G0 ++ trace_gas (trace_blocks a (inc + LENGTH ds) (fuel - (inc + LENGTH ds)) C7 sf v0) /\
        MAP FST G0 = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) /\
        LENGTH G0 = LENGTH ev0` by suspend "preceding" >>
  `(u = child_entry with vs_gas_readings := tail) /\
   ?G1 after. trace_gas (trace_blocks a (inc + LENGTH ds) (fuel - (inc + LENGTH ds)) C7 sf v0) =
     G1 ++ trace_gas (trace_blocks ((e,c.inst_id)::a) e (fuel-e) C7 csf u) ++ after /\
     MAP FST G1 = FLAT (TAKE q ks) /\ LENGTH G1 = LENGTH erow` by suspend "child" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G0 ++ G1`,`after`] >>
  conj_tac >-
    (qpat_assum `trace_gas (trace_blocks a inc _ C7 sf _) = _` SUBST1_TAC >>
     qpat_assum `trace_gas (trace_blocks a (inc + LENGTH ds) _ C7 sf _) = _` SUBST1_TAC >>
     rewrite_tac[APPEND_ASSOC]) >>
  simp[MAP_APPEND]
QED
Resume focus_native_cut_live_level[tables]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  map_every (fn pat => qpat_assum pat (mp_tac o GSYM))
    [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM ks_tab`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[FLOOKUP_DEF, AllCaseEqs()]
QED
Resume focus_native_cut_live_level[eval]:
  drule focus_native_rooted_rows_call_append >>
  disch_then (fn th => qpat_assum `rooted_eval fuel C7 [(sf,rows ++ _,SOME c)] _ = _`
    (mp_tac o ONCE_REWRITE_RULE [th])) >>
  Cases_on `rooted_eval fuel C7 [(sf,rows,NONE)]
              (entry with vs_gas_readings := ys1 ++ ys2 ++ tail)` >>
  rename1 `_ = (previous,res0)` >> Cases_on `res0` >> gvs[] >>
  rename1 `rooted_eval fuel C7 [(sf,rows,NONE)] _ = (previous,OK v0)` >>
  Cases_on `rooted_eval fuel C7 [(sf,[(bb,e,z)],SOME c)] v0` >> gvs[] >>
  strip_tac >> gvs[] >>
  rename1 `rooted_eval fuel C7 [(sf,[(bb,e,z)],SOME c)] v0 = (events,OK u)` >>
  `?caller. rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v0 = (events,OK caller)` by
    (drule_all focus_native_rooted_without_call >> simp[]) >>
  qexists `caller` >> simp[]
QED
Resume focus_native_cut_live_level[preceding]:
  qpat_x_assum `Abbrev (rows = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev0,OK v0)`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all focus_native_preceding_rows >> simp[]
QED
Resume focus_native_cut_live_level[child]:
  `rooted_eval fuel C7 [(sf,[(bb,e,DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs)],NONE)]
     (hin with vs_gas_readings := ys2 ++ tail) = (erow,OK caller)` by
    metis_tac[Abbr `z`] >>
  `FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,child_entry,NONE)` by
    (qpat_assum `FLOOKUP calls (a,e,_) = SOME _` mp_tac >> simp[Abbr `c`]) >>
  `FLOOKUP acts ((e,(EL q xs).inst_id)::a) =
     SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest)` by
    (qpat_assum `FLOOKUP acts ((e,_)::a) = SOME _` mp_tac >> simp[Abbr `c`]) >>
  drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_open_child_step)) >>
  qpat_assum `Abbrev (c = _)` (fn th =>
    once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  `u = child_entry with vs_gas_readings := tail` by
    (qpat_assum `rooted_eval fuel C7 [(_,_,SOME c)] v0 = _` mp_tac >>
     qpat_assum `rooted_eval fuel C7 [(_,_,SOME c)] (hin with vs_gas_readings := _) = _`
       mp_tac >> qpat_assum `v0 = _` mp_tac >>
     qpat_assum `Abbrev (z = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G`,`after`] >>
  qpat_assum `v0 = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
  asm_rewrite_tac[]
QED
Finalise focus_native_cut_live_level

Theorem focus_native_cut_failed_after_rows[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys sched hin h0 bodyrec ct front closed brest ds later
    z mr kr gs tail fuel ev0 v0 ev r.
  let phi = phi_prefix_length bb.bb_instructions in
  let rows = MAP (\f.
    (FST (THE (FLOOKUP blocks (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds;
      v = entry with vs_gas_readings := gs ++ tail in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest) /\
  order = ds ++ e::later /\ N <= fuel /\
  ((later <> [] /\ z = DROP phi bb.bb_instructions /\
      mr = FLAT (THE (FLOOKUP ms_tab (a,e))) /\ kr = FLAT (THE (FLOOKUP ks_tab (a,e)))) \/
   (?be hbe k. bodyrec = SOME (be,hbe) /\ k <= LENGTH xs /\
      z = DROP phi ps ++ TAKE k xs /\ mr = FLAT (TAKE k (THE (FLOOKUP ms_tab (a,e)))) /\
      kr = FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e)))) /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!t. t < k /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
   (bodyrec = NONE /\ mr = [] /\ kr = [] /\
    z = DROP phi (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h =>
      st.vs_inst_idx) ps))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) ++ mr) gs /\
  rooted_eval fuel C7 [(sf,rows,NONE)] v = (ev0,OK v0) /\
  rooted_eval fuel C7 [(sf,rows ++ [(bb,e,z)],NONE)] v = (ev,r) /\
  terminates r /\ (!w. r <> OK w) ==>
  LENGTH (trace_gas (trace_blocks a inc (fuel-inc) C7 sf v)) = LENGTH ev /\
  ?rest. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) ++ kr =
    MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf v)) ++ rest
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qmatch_asmsub_abbrev_tac `rooted_eval fuel C7 [(sf,rows ++ _,NONE)] v` >>
  `?ms ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks` by
    suspend "tables" >>
  `e <= N /\ (later <> [] ==> e <> LAST order)` by suspend "order" >>
  qpat_x_assum `LIST_REL _ (_ ++ _) gs` mp_tac >>
  simp[Once LIST_REL_SPLIT1] >> strip_tac >>
  qpat_x_assum `gs = _` SUBST_ALL_TAC >>
  `?ev1. rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v0 = (ev1,r) /\ ev = ev0 ++ ev1` by
    suspend "eval" >>
  `e = SUC (inc + LENGTH ds) /\ v0 = hin with vs_gas_readings := ys2 ++ tail /\
   ?G0. trace_gas (trace_blocks a inc (fuel-inc) C7 sf
           (entry with vs_gas_readings := (ys1 ++ ys2) ++ tail)) =
          G0 ++ trace_gas (trace_blocks a (inc + LENGTH ds) (fuel-(inc+LENGTH ds)) C7 sf v0) /\
        MAP FST G0 = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) /\
        LENGTH G0 = LENGTH ev0` by suspend "preceding" >>
  `LENGTH (trace_gas (trace_blocks a (inc + LENGTH ds) (fuel-(inc+LENGTH ds)) C7 sf v0)) = LENGTH ev1 /\
   ?rest. kr = MAP FST (trace_gas (trace_blocks a (inc + LENGTH ds) (fuel-(inc+LENGTH ds)) C7 sf v0)) ++ rest` by
    suspend "fail" >>
  qpat_assum `Abbrev (v = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `trace_gas (trace_blocks a inc _ C7 sf _) = _` SUBST1_TAC >>
  conj_tac >- simp[IgnAsm `v0 = _`] >>
  qexists `rest` >> simp[MAP_APPEND, APPEND_ASSOC, IgnAsm `v0 = _`]
QED
Resume focus_native_cut_failed_after_rows[tables]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  map_every (fn pat => qpat_assum pat (mp_tac o GSYM))
    [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM ks_tab`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gvs[FLOOKUP_DEF, AllCaseEqs()]
QED
Resume focus_native_cut_failed_after_rows[order]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  conj_tac
  >- (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> _`
         (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest)`
           (mp_then Any mp_tac th)) >> metis_tac[]) >>
  `ALL_DISTINCT order` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
          (mp_then Any mp_tac (cj 6 th))) >>
     POP_ASSUM_LIST (K all_tac) >> disch_then SUBST1_TAC >> simp[ALL_DISTINCT_GENLIST]) >>
  qpat_assum `ALL_DISTINCT order` mp_tac >>
  qpat_assum `order = _` SUBST1_TAC >> POP_ASSUM_LIST (K all_tac) >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  `LAST (e::later) = LAST later` by
    (Cases_on `later` >> gvs[]) >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED
Resume focus_native_cut_failed_after_rows[eval]:
  drule focus_native_rooted_rows_call_append >>
  disch_then (fn th => qpat_assum `rooted_eval fuel C7 [(sf,rows ++ _,NONE)] _ = _`
    (mp_tac o ONCE_REWRITE_RULE [th])) >>
  Cases_on `rooted_eval fuel C7 [(sf,[(bb,e,z)],NONE)] v0` >>
  simp[IgnAsm `v0 = _`] >> metis_tac[]
QED
Resume focus_native_cut_failed_after_rows[preceding]:
  qpat_x_assum `Abbrev (v = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (rows = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev0,OK v0)`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all focus_native_preceding_rows >> simp[]
QED
Resume focus_native_cut_failed_after_rows[fail]:
  qpat_x_assum `v0 = _` SUBST_ALL_TAC >>
  qsuff_tac `(e <> LAST order /\ z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
     mr = FLAT ms /\ kr = FLAT ks) \/
   (?be hbe k. bodyrec = SOME (be,hbe) /\ k <= LENGTH xs /\
     z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE k xs /\
     mr = FLAT (TAKE k ms) /\ kr = FLAT (TAKE k ks) /\
     EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
     (!t. t < k /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
   (bodyrec = NONE /\ mr = [] /\ kr = [] /\
    z = DROP (phi_prefix_length bb.bb_instructions)
      (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h => st.vs_inst_idx) ps))`
  >- (disch_tac >>
      drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_cut_failure_row)) >>
      metis_tac[]) >>
  qpat_assum `(_ /\ _ /\ _ /\ _) \/ _ \/ _` mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`later <> [] ==> e <> LAST order`, `FLOOKUP ms_tab (a,e) = SOME ms`,
     `FLOOKUP ks_tab (a,e) = SOME ks`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> fs[] >> metis_tac[]
QED
Finalise focus_native_cut_failed_after_rows

Theorem focus_native_row_split[local]:
  !ds before row after f last.
    MAP f ds ++ [last] = before ++ row::after ==>
    (before = MAP f ds /\ row = last) \/
    ?u e v. ds = u ++ e::v /\ before = MAP f u /\ row = f e
Proof
  Induct >> Cases_on `before` >> simp[] >> rpt strip_tac >>
  rename1 `f x = y` >>
  `MAP f ds ++ [last] = t ++ row::after` by simp[] >>
  qpat_x_assum `!before row after f last. _` drule >> strip_tac >> gvs[] >>
  qexistsl [`x::u`,`e`,`v`] >> simp[]
QED

Theorem focus_native_failed_level[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys sched hin h0 bodyrec ct front closed brest ds later
    z mr kr gs tail fuel call ev r.
  let phi = phi_prefix_length bb.bb_instructions in
  let rows = MAP (\f.
    (FST (THE (FLOOKUP blocks (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds;
      v = entry with vs_gas_readings := gs ++ tail in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest) /\
  order = ds ++ e::later /\ N <= fuel /\
  ((?be hbe k. bodyrec = SOME (be,hbe) /\ k <= LENGTH xs /\
      z = DROP phi ps ++ TAKE k xs /\ mr = FLAT (TAKE k (THE (FLOOKUP ms_tab (a,e)))) /\
      kr = FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e)))) /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!t. t < k /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
   (bodyrec = NONE /\ mr = [] /\ kr = [] /\
    z = DROP phi (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h =>
      st.vs_inst_idx) ps))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) ++ mr) gs /\
  rooted_eval fuel C7 [(sf,rows ++ [(bb,e,z)],call)] v = (ev,r) /\
  terminates r /\ (!w. r <> OK w) ==>
  LENGTH (trace_gas (trace_blocks a inc (fuel-inc) C7 sf v)) = LENGTH ev /\
  ?rest. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) ++ kr =
    MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf v)) ++ rest
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qmatch_asmsub_abbrev_tac `rooted_eval fuel C7 [(sf,MAP mk ds ++ _,call)] v` >>
  `?rows row more ev0 u. MAP mk ds ++ [(bb,e,z)] = rows ++ row::more /\
    rooted_eval fuel C7 [(sf,rows,NONE)] v = (ev0,OK u) /\
    rooted_eval fuel C7 [(sf,rows ++ [row],NONE)] v = (ev,r)` by suspend "localise" >>
  drule focus_native_row_split >> strip_tac
  >- suspend "slice" >>
  suspend "full_row"
QED
Resume focus_native_failed_level[localise]:
  PairCases_on `packet` >>
  drule_all focus_stopped_rooted_first_failure >>
  disch_then (qx_choose_then `pre` strip_assume_tac) >>
  `pre = []` by
    (Cases_on `pre` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  gvs[AllCaseEqs(), terminates_def] >>
  qexistsl [`rows`,`row`,`later'`,`ev0`,`u`] >> simp[]
QED
Resume focus_native_failed_level[slice]:
  qpat_x_assum `Abbrev (mk = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (v = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `rows = _` SUBST_ALL_TAC >>
  qpat_x_assum `row = _` SUBST_ALL_TAC >>
  `((later <> [] /\ z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
       mr = FLAT (THE (FLOOKUP ms_tab (a,e))) /\ kr = FLAT (THE (FLOOKUP ks_tab (a,e)))) \/
    (?be hbe k. bodyrec = SOME (be,hbe) /\ k <= LENGTH xs /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE k xs /\
      mr = FLAT (TAKE k (THE (FLOOKUP ms_tab (a,e)))) /\
      kr = FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e)))) /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!t. t < k /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
    (bodyrec = NONE /\ mr = [] /\ kr = [] /\
      z = DROP (phi_prefix_length bb.bb_instructions)
        (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h => st.vs_inst_idx) ps)))`
    suffices_by (disch_tac >>
      drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_cut_failed_after_rows)) >> simp[]) >>
  metis_tac[]
QED
Resume focus_native_failed_level[full_row]:
  rename1 `ds = bef ++ bad::aft` >>
  `?rec. FLOOKUP blocks (a,bad) = SOME rec` by
    (qhdtm_assum `dft_focus_packet_rel` (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
         (mp_then Any mp_tac (cj 7 th))) >>
     qpat_assum `order = _` mp_tac >> qpat_assum `ds = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[venomExecProofsTheory.FDOM_FLOOKUP] >> metis_tac[]) >>
  PairCases_on `rec` >>
  qpat_x_assum `Abbrev (mk = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (v = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `rows = _` SUBST_ALL_TAC >> qpat_x_assum `row = _` SUBST_ALL_TAC >>
  qpat_x_assum `ds = _` SUBST_ALL_TAC >>
  `order = bef ++ bad::(aft ++ e::later)` by simp[APPEND_ASSOC] >>
  qpat_x_assum `LIST_REL _ _ gs` mp_tac >>
  simp[MAP_APPEND, FLAT_APPEND, Once LIST_REL_SPLIT1, NoAsms] >> strip_tac >>
  qpat_x_assum `LIST_REL _ (_ ++ _) ys1` (mp_tac o REWRITE_RULE [APPEND_ASSOC]) >>
  once_rewrite_tac[LIST_REL_SPLIT1] >> strip_tac >>
  `gs ++ tail = ys1' ++ (ys2' ++ ys2 ++ tail)` by simp[APPEND_ASSOC] >>
  qpat_assum `gs ++ tail = _` (fn th =>
    qpat_x_assum `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev0,OK u)`
      (assume_tac o REWRITE_RULE [th]) >>
    qpat_x_assum `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev,r)`
      (mp_tac o REWRITE_RULE [th])) >>
  BETA_TAC >>
  qpat_assum `FLOOKUP blocks (a,bad) = SOME _`
    (fn th => rewrite_tac[th, optionTheory.THE_DEF, pairTheory.FST]) >>
  disch_tac >>
  `LENGTH (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
          (entry with vs_gas_readings := ys1' ++ (ys2' ++ ys2 ++ tail)))) = LENGTH ev /\
   ?ksrest. (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) bef) ++
          FLAT (THE (FLOOKUP ks_tab (a,bad)))) =
     MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
          (entry with vs_gas_readings := ys1' ++ (ys2' ++ ys2 ++ tail)))) ++ ksrest` by
    (MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_cut_failed_after_rows)) >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     map_every (fn pat => qpat_assum pat (irule_at Any))
       [`FLOOKUP acts a = SOME _`, `FLOOKUP blocks (a,bad) = SOME _`,
        `order = bef ++ bad::(aft ++ e::later)`,
        `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev0,OK u)`,
        `rooted_eval fuel C7 [(_,_,NONE)] _ = (ev,r)`] >>
     qpat_assum `LIST_REL _ (_ ++ _) ys1'` (irule_at Any) >> simp[]) >>
  simp[] >>
  (gvs[])
QED
Finalise focus_native_failed_level

(* A stopped evaluation embeds only the GAS visits actually reached. At a
   successful call the remaining evaluation is in its child, but the native
   caller trace can still have a suffix after that child. *)
Theorem focus_native_cut_spine[local]:
  !cuts levels ws tail ev r.
  LENGTH cuts = LENGTH levels /\
  LIST_REL compat (FLAT (MAP slots cuts)) ws /\
  (!v. eval [] v = ([],OK v)) /\
  (!lv lvs v. eval (lv::lvs) v =
    (let (prior,res) = eval [lv] v in
     case res of OK u => (prior ++ FST (eval lvs u), SND (eval lvs u))
               | other => (prior,other))) /\
  (!i gs rest prior res.
    i < LENGTH cuts /\ LIST_REL compat (slots (EL i cuts)) gs /\
    eval [EL i levels] (enter (EL i cuts) (gs ++ rest)) = (prior,res) /\
    terminates res /\ (!u. res <> OK u) ==>
    LENGTH (gas (EL i cuts) (gs ++ rest)) = LENGTH prior /\
    ?later. keys (EL i cuts) = MAP FST (gas (EL i cuts) (gs ++ rest)) ++ later) /\
  (!i gs rest prior u.
    SUC i < LENGTH cuts /\ LIST_REL compat (slots (EL i cuts)) gs /\
    eval [EL i levels] (enter (EL i cuts) (gs ++ rest)) = (prior,OK u) ==>
    u = enter (EL (SUC i) cuts) rest /\
    ?G after. gas (EL i cuts) (gs ++ rest) = G ++ gas (EL (SUC i) cuts) rest ++ after /\
              MAP FST G = keys (EL i cuts) /\ LENGTH G = LENGTH prior) /\
  eval levels (enter (HD cuts) (ws ++ tail)) = (ev,r) /\
  terminates r /\ (!u. r <> OK u) ==>
  ?G after surplus. gas (HD cuts) (ws ++ tail) = G ++ after /\
    FLAT (MAP keys cuts) = MAP FST G ++ surplus /\ LENGTH G = LENGTH ev
Proof
  Induct_on `cuts` >> Cases_on `levels` >> simp[]
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  rename1 `eval (lv::lvs) _ = (ev,r)` >>
  qpat_x_assum `LIST_REL _ (_ ++ _) ws` (mp_tac o REWRITE_RULE [LIST_REL_SPLIT1]) >>
  disch_then (qx_choose_then `gs` (qx_choose_then `ws'` strip_assume_tac)) >>
  qpat_x_assum `ws = _` SUBST_ALL_TAC >>
  `((gs ++ ws') ++ tail) = gs ++ (ws' ++ tail)` by simp[APPEND_ASSOC] >>
  pop_assum SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval (_::lvs) v = (ev,r)` >>
  Cases_on `eval [lv] v` >> rename1 `_ = (prior,res)` >>
  Cases_on `?u. res = OK u`
  >- suspend "advance" >>
  suspend "failed"
QED
Resume focus_native_cut_spine[advance]:
  qpat_x_assum `?u. res = OK u` (qx_choose_then `u` strip_assume_tac) >>
  `?ev'. eval lvs u = (ev',r) /\ ev = prior ++ ev'` by
    (qpat_assum `!l ls v. eval (l::ls) v = _` (qspecl_then [`lv`,`lvs`,`v`] mp_tac) >>
     simp[] >> Cases_on `eval lvs u` >> gvs[]) >>
  qpat_x_assum `!lv lvs v. eval (lv::lvs) v = _` (mk_asm "eval_cons") >>
  Cases_on `cuts = []`
  >- (`lvs = []` by
        (qpat_assum `LENGTH cuts = LENGTH lvs` (mp_tac o SYM) >>
         qpat_assum `cuts = []` (fn th => simp[NoAsms,th])) >>
      qpat_assum `eval lvs u = _` mp_tac >>
      qpat_assum `!u. r <> OK u` (qspec_then `u` mp_tac) >>
      qpat_assum `!v. eval [] v = _` (qspec_then `u` mp_tac) >>
      qpat_assum `lvs = []` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
  `0 < LENGTH cuts` by simp[LENGTH_NON_NIL] >>
  `u = enter (HD cuts) (ws' ++ tail) /\
   ?G after. gas (HD (h'::cuts)) (gs ++ (ws' ++ tail)) =
      G ++ gas (HD cuts) (ws' ++ tail) ++ after /\
      MAP FST G = keys h' /\ LENGTH G = LENGTH prior` by
    (qpat_assum `!i gs rest prior u. _ ==> u = _ /\ _`
       (qspecl_then [`0`,`gs`,`ws' ++ tail`,`prior`,`u`] mp_tac) >>
     qpat_assum `Abbrev (v = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `res = OK u` SUBST_ALL_TAC >>
     pure_rewrite_tac[EL, HD, GSYM APPEND_ASSOC] >>
     qpat_assum `eval [lv] _ = (prior,OK u)` (fn th => simp[NoAsms,th]) >>
     qpat_assum `LIST_REL _ _ gs` (fn th => simp[NoAsms,th]) >>
     qpat_assum `0 < LENGTH cuts` (fn th => simp[NoAsms,th])) >>
  `?G' after' surplus. gas (HD cuts) (ws' ++ tail) = G' ++ after' /\
      FLAT (MAP keys cuts) = MAP FST G' ++ surplus /\ LENGTH G' = LENGTH ev'` by
    (qpat_assum `!levels ws tail ev r. _` (qspecl_then [`lvs`,`ws'`,`tail`,`ev'`,`r`] mp_tac) >>
     impl_tac
     >- ((rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (pure_rewrite_tac[LET_THM] >> asm "eval_cons" ACCEPT_TAC) >>
         TRY (qpat_assum `u = enter _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
         qx_gen_tac `i`
         >- (qpat_assum `!i gs rest prior res. _ ==> LENGTH _ = _ /\ _`
               (qspec_then `SUC i` mp_tac) >> simp[NoAsms, EL]) >>
         qpat_assum `!i gs rest prior u. _ ==> u = _ /\ _`
           (qspec_then `SUC i` mp_tac) >> simp[NoAsms, EL] >> (metis_tac[NoAsms, EL]))) >> simp[NoAsms]) >>
  qexistsl [`G ++ G'`,`after' ++ after`,`surplus`] >>
  qpat_assum `gas (HD (h'::cuts)) _ = _`
    (fn th => simp[REWRITE_RULE [HD,APPEND_ASSOC] th, MAP_APPEND,APPEND_ASSOC])
QED
Resume focus_native_cut_spine[failed]:
  `ev = prior /\ r = res` by
    (qpat_x_assum `!l ls v. eval (l::ls) v = _` (qspecl_then [`lv`,`lvs`,`v`] mp_tac) >>
     Cases_on `res` >> gvs[]) >>
  qpat_x_assum `!l ls v. eval (l::ls) v = _` kall_tac >>
  qpat_x_assum `r = res` SUBST_ALL_TAC >> qpat_x_assum `ev = prior` SUBST_ALL_TAC >>
  `LENGTH (gas h' (gs ++ (ws' ++ tail))) = LENGTH prior /\
   ?later. keys h' = MAP FST (gas h' (gs ++ (ws' ++ tail))) ++ later` by
    (qpat_assum `!i gs rest prior res. _ ==> LENGTH _ = _ /\ _`
       (qspecl_then [`0`,`gs`,`ws' ++ tail`,`prior`,`res`] mp_tac) >>
     qpat_x_assum `Abbrev (v = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     pure_rewrite_tac[EL,HD,LENGTH] >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  qexistsl [`gas h' (gs ++ (ws' ++ tail))`,`[]`,`later ++ FLAT (MAP keys cuts)`] >>
  simp[APPEND_ASSOC]
QED
Finalise focus_native_cut_spine

Theorem focus_failed_cut_root_keys:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,bodyrec,ct,front,closed,brest) /\
  ((IS_SOME bodyrec /\ q < LENGTH xs /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!t. t < q /\ (EL t xs).inst_opcode = INVOKE ==> MEM t (TAKE ct sched))) \/
   (bodyrec = NONE /\ q = 0 /\
    z = DROP (phi_prefix_length bb.bb_instructions)
      (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h => st.vs_inst_idx) ps))) /\
  MAP (\(a,ds,e,k,z). a) cuts = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts = LENGTH levels /\
  (!i a ds e k zi.
    i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,zi) ==>
    ?sf tf inc entry order res nrest bbi bti psi xsi ysi rhoi
      ini hi bei cti fronti closedi resti later.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,cti,fronti,closedi,resti) /\
      order = ds ++ e::later /\
      (if SUC i = LENGTH cuts then a = p /\ e = d /\ k = q /\ zi = z
       else ?cid h b0 done_at_call child_entry ret.
         EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (e,cid)::a /\
         FLOOKUP calls (a,e,cid) = SOME (k,h,b0,done_at_call,child_entry,ret) /\
         k < LENGTH xsi /\ (EL k xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE k xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xsi) /\
         (!t. t < k /\ (EL t xsi).inst_opcode = INVOKE ==> MEM t done_at_call)) /\
      EL i levels =
        (sf, MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds ++ [(bbi,e,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL k xsi))) /\
  Mcut = FLAT (MAP (\(a,ds,e,k,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) ++
    FLAT (TAKE k (THE (FLOOKUP ms_tab (a,e))))) cuts) /\
  Kcut = FLAT (MAP (\(a,ds,e,k,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) ++
    FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  R = root_entry with vs_gas_readings := gs ++ tail /\
  rooted_eval fuel C7 levels R = (events,r) /\
  terminates r /\ (!u. r <> OK u) /\
  gas_events_blocks fuel C7 root_sf R = events ==>
  ?surplus. Kcut = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf R)) ++ surplus
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qmatch_asmsub_abbrev_tac `Mcut = FLAT (MAP slots cuts)` >>
  qmatch_asmsub_abbrev_tac `Kcut = FLAT (MAP keys cuts)` >>
  qmatch_asmsub_abbrev_tac `MAP path cuts = REVERSE _` >>
  `LENGTH cuts = SUC (LENGTH p)` by
    (qpat_assum `MAP path cuts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qabbrev_tac `enter = \cut ws.
    case THE (FLOOKUP acts (path cut)) of (sf,tf,inc,entry,order,res,nrest) =>
      entry with vs_gas_readings := ws` >>
  qabbrev_tac `native = \cut ws.
    case THE (FLOOKUP acts (path cut)) of (sf,tf,inc,entry,order,res,nrest) =>
      trace_gas (trace_blocks (path cut) inc (fuel-inc) C7 sf
        (entry with vs_gas_readings := ws))` >>
  `!i. i < LENGTH cuts ==> path (EL i cuts) = DROP (LENGTH p - i) p /\
     MEM (path (EL i cuts)) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by suspend "paths" >>
  `enter (HD cuts) (gs ++ tail) = R /\
   native (HD cuts) (gs ++ tail) = trace_gas (trace_blocks [] 0 fuel C7 root_sf R)` by suspend "root" >>
  `?G after surplus. native (HD cuts) (gs ++ tail) = G ++ after /\
    FLAT (MAP keys cuts) = MAP FST G ++ surplus /\ LENGTH G = LENGTH events` by
    (Q.ISPECL_THEN [`enter`,`slots`,`keys`,`native`,`rooted_eval fuel C7`]
       (qspecl_then [`\slot w. slot = NONE \/ slot = SOME w`,`cuts`,`levels`,`gs`,`tail`,`events`,`r`]
          (mp_tac o BETA_RULE))
       (Q.GENL [`enter`,`slots`,`keys`,`gas`,`eval`,`compat`] focus_native_cut_spine) >>
     impl_tac >- suspend "spine" >> disch_then ACCEPT_TAC) >>
  `LENGTH (native (HD cuts) (gs ++ tail)) = LENGTH events` by
    (qpat_assum `native (HD cuts) (gs ++ tail) = trace_gas _` SUBST1_TAC >>
     qpat_assum `gas_events_blocks _ _ _ _ = events` (SUBST1_TAC o SYM) >>
     simp[NoAsms,dftGasFromListReadingsTheory.trace_gas_lengths,gas_events_length]) >>
  `after = []` by
    (qpat_assum `LENGTH (native (HD cuts) (gs ++ tail)) = LENGTH events` mp_tac >>
     qpat_assum `native (HD cuts) (gs ++ tail) = G ++ after` SUBST1_TAC >> simp[]) >>
  qexists `surplus` >> gvs[] >> metis_tac[]
QED
Resume focus_failed_cut_root_keys[paths]:
  rpt strip_tac >>
  `EL i (MAP path cuts) = DROP (LENGTH p - i) p` by
    (`PRE (SUC (LENGTH p) - i) = LENGTH p - i` by decide_tac >>
     simp[EL_REVERSE,EL_GENLIST]) >>
  gvs[EL_MAP,MEM_GENLIST] >> qexists `LENGTH p - i` >> simp[]
QED
Resume focus_failed_cut_root_keys[root]:
  `0 < LENGTH cuts` by simp[] >>
  `path (HD cuts) = []` by
    (qpat_assum `!i. i < LENGTH cuts ==> path (EL i cuts) = _ /\ _`
       (qspec_then `0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms,EL,DROP_LENGTH_NIL]) >>
  `?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qhdtm_assum `dft_focus_packet_rel` (mp_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => FIRST (map ACCEPT_TAC (CONJUNCTS th))))) >>
  simp[Abbr `enter`,Abbr `native`]
QED
Resume focus_failed_cut_root_keys[spine]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `Mcut = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> drule focus_native_rooted_entry >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >>
     drule (Q.INST [`left` |-> `[lv]`, `right` |-> `lvs`] focus_native_rooted_append) >>
     disch_then (qspecl_then [`v`,`lvs`,`lv`,`fuel`] mp_tac) >> rewrite_tac[APPEND]) >>
  conj_tac >- suspend "stop_level" >>
  conj_tac >- suspend "live_level" >>
  qpat_assum `enter (HD cuts) _ = R` SUBST1_TAC >> simp[]
QED
Resume focus_failed_cut_root_keys[stop_level]:
  map_every qx_gen_tac [`i`,`ws`,`taili`,`ev`,`ri`] >> strip_tac >>
  Cases_on `EL i cuts` >> rename1 `EL i cuts = cut` >> PairCases_on `cut` >>
  qpat_assum `!i a ds e k zi. _`
    (qspecl_then [`i`,`cut0`,`cut1`,`cut2`,`cut3`,`cut4`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
  gns[Abbr `slots`,Abbr `keys`,Abbr `enter`,Abbr `native`,Abbr `path`] >>
  `((?be hbe. bei = SOME (be,hbe) /\ cut3 <= LENGTH xsi /\
       cut4 = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE cut3 xsi /\
       EVERY (\x. ~is_terminator x.inst_opcode) (TAKE cut3 xsi) /\
       (!t. t < cut3 /\ (EL t xsi).inst_opcode = INVOKE ==> MEM t (TAKE cti rhoi))) \/
    (bei = NONE /\ cut3 = 0 /\
       cut4 = DROP (phi_prefix_length bbi.bb_instructions)
         (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h => st.vs_inst_idx) psi)))`
    suffices_by suspend "apply_failed_level" >>
  Cases_on `SUC i = LENGTH cuts`
  >- suspend "final_slice" >>
  suspend "ancestor_slice"
QED
Resume focus_failed_cut_root_keys[apply_failed_level]:
  disch_tac >>
  `((?be hbe k. bei = SOME (be,hbe) /\ k <= LENGTH xsi /\
       cut4 = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE k xsi /\
       FLAT (TAKE cut3 (THE (FLOOKUP ms_tab (cut0,cut2)))) =
         FLAT (TAKE k (THE (FLOOKUP ms_tab (cut0,cut2)))) /\
       FLAT (TAKE cut3 (THE (FLOOKUP ks_tab (cut0,cut2)))) =
         FLAT (TAKE k (THE (FLOOKUP ks_tab (cut0,cut2)))) /\
       EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xsi) /\
       (!t. t < k /\ (EL t xsi).inst_opcode = INVOKE ==> MEM t (TAKE cti rhoi))) \/
    (bei = NONE /\ FLAT (TAKE cut3 (THE (FLOOKUP ms_tab (cut0,cut2)))) = [] /\
       FLAT (TAKE cut3 (THE (FLOOKUP ks_tab (cut0,cut2)))) = [] /\
       cut4 = DROP (phi_prefix_length bbi.bb_instructions)
         (TAKE (case q8 of JointConfig stk PG G tn fn inst st oms om hs h => st.vs_inst_idx) psi)))`
    suffices_by
      (disch_tac >>
       `cut1 ++ cut2::later = cut1 ++ cut2::later` by REFL_TAC >>
       drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_failed_level)) >>
       disch_then ACCEPT_TAC) >>
  pop_assum strip_assume_tac >> simp[] >> metis_tac[]
QED
Resume focus_failed_cut_root_keys[final_slice]:
  `SUC i = LENGTH levels` by metis_tac[] >>
  gvs[] >>
  Cases_on `bei` >> gvs[] >>
  metis_tac[pairTheory.PAIR]
QED
Resume focus_failed_cut_root_keys[ancestor_slice]:
  `SUC i < LENGTH cuts /\ SUC i <> LENGTH levels` by decide_tac >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >> simp[Once COND_CLAUSES] >>
  disch_then strip_assume_tac >>
  `MEM ((cut2,(EL cut3 xsi).inst_id)::cut0) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (`MEM (EL (SUC i) (REVERSE (GENLIST (\i. DROP i p) (LENGTH levels))))
        (REVERSE (GENLIST (\i. DROP i p) (LENGTH levels)))` by
       (irule EL_MEM >> simp[]) >> gvs[]) >>
  drule_all focus_native_live_child_record >> strip_tac >>
  `?be hbe. bei = SOME (be,hbe)` by
    (qhdtm_assum `dft_focus_packet_rel` (mp_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
     qpat_x_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _` drule >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
     qpat_assum `FLOOKUP blocks (cut0,cut2) = SOME (_,_,_,_,_,_,_,_,SOME (_,_),_,_,_,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (cut0,cut2) = SOME (_,_,_,_,_,_,_,_,bei,_,_,_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  qpat_assum `done_at_call = TAKE cti rhoi` (SUBST1_TAC o SYM) >> simp[]
QED
Resume focus_failed_cut_root_keys[live_level]:
  map_every qx_gen_tac [`i`,`ws`,`taili`,`ev`,`u`] >> strip_tac >>
  `i < LENGTH cuts /\ SUC i <> LENGTH cuts` by decide_tac >>
  Cases_on `EL i cuts` >> rename1 `EL i cuts = cut` >> PairCases_on `cut` >>
  qpat_assum `!i a ds e k zi. _`
    (qspecl_then [`i`,`cut0`,`cut1`,`cut2`,`cut3`,`cut4`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
  `EL (SUC i) (MAP path cuts) = path (EL (SUC i) cuts)` by
    (irule listTheory.EL_MAP >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >>
  qpat_assum `SUC i <> LENGTH cuts` (fn th => simp[NoAsms,th]) >>
  disch_then strip_assume_tac >>
  qabbrev_tac `cid = (EL cut3 xsi).inst_id` >>
  `path (EL (SUC i) cuts) = (cut2,cid)::cut0` by
    (qpat_assum `EL (SUC i) (MAP path cuts) = path _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `MEM ((cut2,cid)::cut0) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (qpat_assum `path (EL (SUC i) cuts) = _` (SUBST1_TAC o SYM) >>
     qpat_assum `!i. i < LENGTH cuts ==> path (EL i cuts) = _ /\ _`
       (qspec_then `SUC i` mp_tac) >> simp[]) >>
  `?csf ctf child_order child_res child_rest.
      FLOOKUP acts ((cut2,cid)::cut0) =
        SOME (csf,ctf,cut2,child_entry,child_order,child_res,child_rest)` by
    (qhdtm_assum `dft_focus_packet_rel` (mp_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
     qpat_x_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _` drule >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
     qpat_assum `FLOOKUP acts ((cut2,cid)::cut0) = SOME (_,_,cut2,child_entry,_,_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  gns[Abbr `slots`,Abbr `keys`,Abbr `enter`,Abbr `native`,Abbr `path`,Abbr `cid`] >>
  `cut1 ++ cut2::later = cut1 ++ cut2::later` by REFL_TAC >>
  `MEM ((cut2,(EL cut3 xsi).inst_id)::cut0) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (qpat_assum `SUC (LENGTH p) = LENGTH levels` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_native_cut_live_level)) >>
  (metis_tac[])
QED
Finalise focus_failed_cut_root_keys

(* A terminating source fuel contains the bounded prefix supplied at any fuel. *)
Theorem focus_event_bound_at_terminating_fuel[local]:
  terminates (run_blocks fuel C fn R) /\
  n <= LENGTH (gas_events_blocks f C fn R) ==>
  n <= LENGTH (gas_events_blocks fuel C fn R) /\
  TAKE n (gas_events_blocks fuel C fn R) = TAKE n (gas_events_blocks f C fn R)
Proof
  strip_tac >> Cases_on `f <= fuel`
  >- (`?extra. gas_events_blocks fuel C fn R = gas_events_blocks f C fn R ++ extra` by
        metis_tac[cj 3 gasEventsFuelTheory.gas_events_fuel_extension] >>
      simp[TAKE_APPEND1]) >>
  `fuel <= f` by decide_tac >>
  `gas_events_blocks f C fn R = gas_events_blocks fuel C fn R` by
    metis_tac[cj 3 gasEventsFuelTheory.gas_events_fuel_extension, terminates_not_error] >>
  metis_tac[]
QED

Theorem focus_selected_guard_and_bound:
  let C7 = stage 7; C8 = stage 8; C9 = stage 9 in
  let a0 = entry_asm_state vs0 es0;
      env = asm_data_env prog vs0.vs_code;
      planner_base = vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                               vs_return_pc_token := 0w; vs_inst_idx := 0|>;
      trace8 = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry
  in
  let V = TAKE j trace8;
      q8 = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8;
      q9 = JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9;
      Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))));
      filling = raw ++ [0w]
  in
  let R = root_entry with vs_gas_readings := filling;
      n = MIN (LENGTH (markf filling)) (LENGTH filling);
      A = vs0 with <|vs_gas_readings := filling; vs_fmp := fmp; vs_initial_fmp := fmp;
                    vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>
  in
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
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 C8 q80 /\ joint_initial vs0 C9 q90 /\
  joint_trace vs0 C8 q80 evs8 qs8 q8 /\
  joint_trace vs0 C9 q90 evs9 qs9 q9 /\
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved) q8 q9 /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel a0 = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog planner_base es0 q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog env asm_fuel (sym_init a0) = SymOK ss /\
    normal_frame_symbolic_plan env rpolicy out.po_unit cpl prog vs0 es0 q9 ast ss) /\
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH V = j /\
  j < LENGTH trace8 /\ obs = dftGasFromListTraceDefs$trace_gas V /\
  EL j trace8 = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  terminates (run_blocks fuel7 C7 root_sf R) /\
  (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
   inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
  (n <= LENGTH (gas_events_blocks fuel7 C7 root_sf R) /\
   ?f extra.
      MAP project (gas_events_blocks f unit.cu_context entryfn A) = markf filling ++ extra /\
      TAKE n (gas_events_blocks fuel7 C7 root_sf R) =
        TAKE n (gas_events_blocks f unit.cu_context entryfn A)) /\
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
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
         (body_entry = NONE /\ s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
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
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ Kroot = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!fuel gs tail.
          N <= fuel /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval fuel C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval fuel C7 levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval fuel C7 levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks fuel C7 root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks fuel C7 root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval fuel C7 levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!fuel gs tail k u.
          N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < k /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut k (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            C7 (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom C7 sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
        (let gs = TAKE (LENGTH Mcut) raw;
             tail = DROP (LENGTH Mcut) raw ++ [0w]
         in
         (!fuel u.
           N <= fuel /\ LENGTH Mcut < n /\
           rooted_eval fuel C7 levels R = (Ecut,OK u) ==>
           raw_reachable R C7 sf src_inst u /\ gas_cut n R u /\
           lowered_mem_fact cpl.cp_max_static_eom C7 sf src_inst u /\
           u.vs_gas_readings = tail /\
           (fin = asm_opt_finalizer ==>
             inst_dload_in_section src_inst u /\
             code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) C7) /\
           (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
           (inv_memory_observation inst8.inst_opcode ==>
             (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
             u.vs_initial_fmp = s8.vs_initial_fmp)) /\
         ((~in_revert_forward fn9 s9 /\
           (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
            source_memory_reads_disjoint cpl inst9 s9 /\
            context_source_memory_writes_disjoint cpl inst9 s9) /\
           (fin = asm_opt_finalizer ==>
            !dst x sz src off.
              inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
              code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
              FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
              w2n (src - n2w off) < dimword (:256) DIV 2)) \/
          n <= LENGTH Mcut \/
          (LENGTH Mcut < n /\ in_revert_forward fn9 s9) \/
          (LENGTH Mcut < n /\
           ?fuel events stopped.
             N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
             rooted_eval fuel C7 levels R = (events,stopped) /\
             (!u. stopped <> OK u) /\ (!err. stopped <> Error err) /\
             run_blocks fuel C7 root_sf R = stopped /\
             gas_events_blocks fuel C7 root_sf R = events /\
             (?extra. Ecut = events ++ extra)))))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >> conj_tac
  >- suspend "bound"
  >> suspend "guard"
QED

Resume focus_selected_guard_and_bound[bound]:
  mp_tac (cj 3 (CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM] gasFocusSourceProviderTheory.focus_source_cut_provider))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `raw` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all focus_event_bound_at_terminating_fuel >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`f`,`extra`] >> simp[]
QED

Resume focus_selected_guard_and_bound[guard]:
  mp_tac (cj 1 (CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM] gasFocusCutGuardsTheory.focus_cut_guard_or_stop))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac [listTheory.APPEND_ASSOC, TAKE_DROP, REFL_CLAUSE, AND_CLAUSES] >>
  disch_then (REPEAT_TCL (FIRST_TCL [CHOOSE_THEN, CONJUNCTS_THEN]) assume_tac) >>
  rename1 `FLOOKUP blocks (p,d) = SOME
    (bb,bt,ps,xs,ys,row_rho,in_state,h0,body_entry,row_count,front,closed,brest)` >>
  qexistsl [`sf`,`inc`,`entry`,`order`,`res`,`nrest`,`bb`,`bt`,`ps`,`xs`,`ys`,`row_rho`,
    `in_state`,`h0`,`body_entry`,`row_count`,`front`,`closed`,`brest`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum
    `(inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
      inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
     ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr. _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (REPEAT_TCL (FIRST_TCL [CHOOSE_THEN, CONJUNCTS_THEN]) assume_tac) >>
  qexistsl [`q`,`z`,`src_inst`,`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!rs f u. LIST_REL _ raw_slots rs ==> _`
      (qspecl_then [`raw`,`fuel`,`u`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise focus_selected_guard_and_bound

(* Fix the late source filling before transporting termination to C7. *)
Theorem focus_selected_pre_dft_run:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\
  (stage 7).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  fn_entry_label root_sf = SOME lbl7 /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  terminates (run_context fr unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
  ctx_sim_fuel I D unit.cu_context (stage 7)
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
    (vs0 with vs_gas_readings := raw ++ [0w]) /\
  ctx_abort_rq D unit.cu_context (stage 7)
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)
    (vs0 with vs_gas_readings := raw ++ [0w]) /\
  o1_inv D 7 (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]) /\
  ((?b u7. run_context b (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]) =
      Abort ExHalt_abort u7) ==>
    !fuel. terminates (run_context fuel unit.cu_context
             (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
      ?u. run_context fuel unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
          Abort ExHalt_abort u) /\
  terminates (run_blocks (MAX N fr) (stage 7) root_sf
    (root_entry with vs_gas_readings := raw ++ [0w]))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by
    fs[codegenEntrySimTheory.codegen_asm_entry_rel_def] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0` by
    (rewrite_tac[fmp_variant_room_def] >>
     conj_tac >- metis_tac[generate_context_plan_eom_room] >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac
    gasFocusPreDftStaticAbortLiftTheory.focus_pre_dft_static_abort_lift >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[focus_fixed_filling_stage7_terminates]
QED

(* A failed cut can execute fewer cells than Kcut describes. Its actual
   native GAS trace, rather than the entire cut, is the observed prefix. *)
Theorem focus_failed_prefix_observed_agreement:
  let R = root_entry with vs_gas_readings := raw ++ [0w] in
  let G = trace_gas (trace_blocks [] 0 fuel C7 root_sf R) in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Kroot = Kcut ++ kr /\ Kcut = MAP FST G ++ t /\
  LENGTH Kcut <= LENGTH raw /\ terminates (run_blocks fuel C7 root_sf R) ==>
  !k x. dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k x ==>
    MEM (k,x) G /\ MEM k Kcut /\
    (!y. MEM k (MAP FST obs) /\ dftGasFromListUnion$recorded C8 vs0 k y ==> x = y)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `R = root_entry with vs_gas_readings := raw ++ [0w]` >>
  qabbrev_tac `G = trace_gas (trace_blocks [] 0 fuel C7 root_sf R)` >>
  `!n. trace_context n C7 (vs0 with vs_gas_readings := raw ++ [0w]) =
       trace_blocks [] 0 n C7 root_sf R` by
    simp[trace_context_def, trace_function_def, Abbr `R`] >>
  `!k x. dftGasFromListUnion$recorded C7
      (vs0 with vs_gas_readings := raw ++ [0w]) k x ==> MEM (k,x) G` by
    (simp[dftGasFromListUnionTheory.recorded_def, Abbr `G`] >> rpt strip_tac >>
     Cases_on `n <= fuel`
     >- (`?suffix. trace_blocks [] 0 fuel C7 root_sf R =
                    trace_blocks [] 0 n C7 root_sf R ++ suffix` by
           (irule (cj 3 dftGasFromListTracePrefixTheory.trace_prefix) >> simp[]) >>
         simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
     `trace_blocks [] 0 n C7 root_sf R = trace_blocks [] 0 fuel C7 root_sf R` by
       (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >>
        simp[] >> gen_tac >> strip_tac >> fs[terminates_def]) >>
     metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `MEM (k,x) G` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `MEM k (MAP FST G)` by (simp[MEM_MAP] >> qexists_tac `(k,x)` >> simp[]) >>
  conj_tac >- metis_tac[MEM_APPEND] >>
  `LENGTH G <= LENGTH raw` by gvs[] >>
  `MAP SND G = TAKE (LENGTH G) raw` by
    (simp[Abbr `G`, dftGasFromListReadingsTheory.trace_gas_readings,
          dftGasFromListReadingsTheory.trace_gas_lengths] >>
     `gas_count_blocks fuel C7 root_sf R <= LENGTH raw` by
       gvs[dftGasFromListReadingsTheory.trace_gas_lengths] >>
     `R.vs_gas_readings = raw ++ [0w]` by simp[Abbr `R`] >>
     simp[gasOracleReplayTheory.gas_prefix_def, GSYM listTheory.APPEND_ASSOC,
          TAKE_APPEND1]) >>
  `G = ZIP (MAP FST G, TAKE (LENGTH (MAP FST G)) raw)` by
    (pure_rewrite_tac[LENGTH_MAP] >> pop_assum (SUBST1_TAC o SYM) >>
     simp[GSYM UNZIP_MAP, listTheory.ZIP_UNZIP]) >>
  `Kroot = MAP FST G ++ (t ++ kr)` by metis_tac[APPEND_ASSOC] >>
  qpat_x_assum `Kroot = Kcut ++ kr` kall_tac >>
  unabbrev_all_tac >>
  metis_tac[REWRITE_RULE [APPEND_NIL]
    (Q.INST [`after` |-> `[]`] focus_stopped_cut_observed_agreement)]
QED

(* Specialize one choice of focus-cut witnesses to the fixed filling. *)
Theorem focus_selected_cut_native_cases:
  let gs = TAKE (LENGTH Mcut) raw;
      tail = DROP (LENGTH Mcut) raw ++ [0w];
      R = root_entry with vs_gas_readings := raw ++ [0w]
  in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_rho,in_state,h0,body_entry,row_count,front,closed,brest) /\
  ((IS_SOME body_entry /\ q < LENGTH xs /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE row_count row_rho))) \/
   (body_entry = NONE /\ q = 0 /\
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
      (if SUC i = LENGTH cuts then ai = p /\ ei = d /\ qi = q /\ zi = z
       else ?cid h b0 done_at_call child_entry ret.
         EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
         FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
         qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  src_inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  raw_slots = Mcut ++ mr /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  N <= fuel /\ terminates (run_blocks fuel C7 root_sf R) /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,d,src_inst.inst_id),sf,src_inst,u)] ++ after /\
          trace_gas before = ZIP (Kcut,gs)) /\
        (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut,OK (u with vs_gas_readings := tail'))) /\
        (body_entry = NONE ==> u with vs_gas_readings := s8.vs_gas_readings = s8) /\
        (IS_SOME body_entry /\ inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
          (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
          u.vs_initial_fmp = s8.vs_initial_fmp)
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  (?u before after.
    rooted_eval fuel C7 levels R = (Ecut,OK u) /\
    trace_blocks [] 0 fuel C7 root_sf R =
      before ++ [((p,d,src_inst.inst_id),sf,src_inst,u)] ++ after /\
    trace_gas before = ZIP (Kcut,gs) /\ u.vs_gas_readings = tail /\
    (!tail'. rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
      (Ecut,OK (u with vs_gas_readings := tail'))) /\
    (body_entry = NONE ==> u with vs_gas_readings := s8.vs_gas_readings = s8) /\
    (IS_SOME body_entry /\ inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)) \/
  (?ev r t extra.
    rooted_eval fuel C7 levels R = (ev,r) /\ (!u. r <> OK u) /\
    run_blocks fuel C7 root_sf R = r /\ gas_events_blocks fuel C7 root_sf R = ev /\
    Ecut = ev ++ extra /\
    Kcut = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf R)) ++ t)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `gs = TAKE (LENGTH Mcut) raw` >>
  qabbrev_tac `tail = DROP (LENGTH Mcut) raw ++ [0w]` >>
  qabbrev_tac `R = root_entry with vs_gas_readings := raw ++ [0w]` >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs` by
    (drule LIST_REL_TAKE >> disch_then (qspec_then `LENGTH Mcut` mp_tac) >>
     qpat_assum `raw_slots = Mcut ++ mr`
       (fn th => pure_rewrite_tac[th,TAKE_LENGTH_APPEND]) >>
     simp[NoAsms, Abbr `gs`]) >>
  `R = root_entry with vs_gas_readings := gs ++ tail` by
    simp[Abbr `R`, Abbr `gs`, Abbr `tail`, listTheory.APPEND_ASSOC] >>
  Cases_on `rooted_eval fuel C7 levels R` >>
  rename1 `rooted_eval fuel C7 levels R = (ev,r)` >>
  qpat_x_assum `!F gs tail. _ ==> (?extra. Ecut = _ ++ extra) /\ _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  qpat_assum `R = root_entry with vs_gas_readings := gs ++ tail`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  (impl_tac >- simp[]) >>
  qpat_assum `rooted_eval fuel C7 levels R = (ev,r)`
    (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >>
  Cases_on `?u. r = OK u`
  >- (qpat_x_assum `?u. r = OK u` (qx_choose_then `u` SUBST_ALL_TAC) >>
      simp[NoAsms] >> strip_tac >> disj1_tac >>
      qexistsl [`before`,`after`] >> simp[]) >>
  `!u. r <> OK u` by metis_tac[] >>
  disch_tac >>
  `run_blocks fuel C7 root_sf R = r /\ gas_events_blocks fuel C7 root_sf R = ev` by
    (Cases_on `r` >> gvs[]) >>
  `terminates r` by metis_tac[] >>
  `?t. Kcut = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf R)) ++ t` by
    (drule_then (drule_all o BETA_RULE o
       PURE_REWRITE_RULE [TypeBase.case_def_of ``:joint_config``])
       focus_failed_cut_root_keys >> disch_then ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`ev`,`r`,`t`,`extra`] >> simp[]
QED

(* A retained activation cannot descend from the as-yet unrecorded
   focus call. Thus the child cannot contribute a retained cut key. *)
Theorem focus_terminal_retained_uncovered:
  let tr8 = trace_blocks [] 0 N C8 root_tf root_entry;
      H = if inst8.inst_opcode = INVOKE then
            trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8) else [] in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  o1_ctx_shape C8 /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  j < LENGTH tr8 /\ EL j tr8 = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Kroot = Kcut ++ kr /\
  (!k x. MEM (k,x) g ==> MEM k Kcut) ==>
  !k x y. MEM (k,x) g /\ (MEM (k,y) obs \/ MEM (k,y) H) /\
    ~(MEM k Kcut /\ MEM k (MAP FST obs)) ==> x = y
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `tr8 = trace_blocks [] 0 N C8 root_tf root_entry` >>
  `ALL_DISTINCT (MAP FST tr8)` by
    (simp[Abbr `tr8`] >> irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >>
     `MEM root_tf C8.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
         f.fn_blocks) C8.ctx_functions` by
       (qpat_assum `o1_ctx_shape C8` mp_tac >>
        simp_tac bool_ss [o1_ctx_shape_def,venomWfTheory.ctx_inst_ids_distinct_def] >>
        strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
        drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
        BETA_TAC >> strip_tac >>
        drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
     pop_assum mp_tac >> qpat_assum `MEM root_tf C8.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> metis_tac[]) >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (SUBST_ALL_TAC o SYM o CONJUNCT1 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `~IS_SOME (FLOOKUP calls (p,d,inst8.inst_id))` by
    (rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     rename1 `FLOOKUP calls (p,d,inst8.inst_id) = SOME callrec` >>
     PairCases_on `callrec` >>
     qpat_assum `!a e cid q h b0 done ent ret.
       FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,ent,ret) ==> _`
       (drule_then strip_assume_tac) >>
     `FST (EL callrec1 tr8) = (p,d,inst8.inst_id)` by simp[Abbr `tr8`] >>
     `callrec1 < LENGTH tr8` by decide_tac >>
     qspecl_then [`MAP FST tr8`,`callrec1`,`j`] mp_tac ALL_DISTINCT_EL_IMP >>
     simp[EL_MAP] >> decide_tac) >>
  `!e cid a. IS_SOME (FLOOKUP acts ((e,cid)::a)) ==>
     IS_SOME (FLOOKUP calls (a,e,cid)) /\ IS_SOME (FLOOKUP acts a)` by
    (map_every qx_gen_tac [`de`,`id`,`path`] >>
     simp[optionTheory.IS_SOME_EXISTS] >>
     disch_then (qx_choose_then `actrec` assume_tac) >> PairCases_on `actrec` >>
     qpat_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!e cid parent. _ ==> ?q h b0 done ret.
       FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done,_,ret)`
       (qspecl_then [`de`,`id`,`path`] (strip_assume_tac o SIMP_RULE std_ss [])) >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
     qpat_assum `!a e cid q h b0 done ent ret.
       FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,ent,ret) ==> _`
       (drule_then strip_assume_tac) >> goal_assum (drule_at Any) >> simp[]) >>
  `!extra. ~IS_SOME (FLOOKUP acts (extra ++ (d,inst8.inst_id)::p))` by
    (Induct >> pure_rewrite_tac[APPEND]
     >- (strip_tac >> qpat_assum `!e cid a. IS_SOME (FLOOKUP acts _) ==> _`
           (drule_then (mp_tac o CONJUNCT1)) >>
         qpat_assum `~IS_SOME (FLOOKUP calls _)` mp_tac >> simp[NoAsms]) >>
     qx_gen_tac `hd` >> PairCases_on `hd` >> strip_tac >>
     qpat_assum `!e cid a. IS_SOME (FLOOKUP acts _) ==> _`
       (drule_then (mp_tac o CONJUNCT2)) >>
     qpat_assum `~IS_SOME (FLOOKUP acts (extra ++ _))` mp_tac >> simp[NoAsms]) >>
  qx_gen_tac `k` >> PairCases_on `k` >> map_every qx_gen_tac [`x`,`y`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (k0,k1,k2) Kcut` by
    (qpat_assum `!k x. MEM (k,x) g ==> MEM k Kcut` (drule_then ACCEPT_TAC)) >>
  `F` suffices_by simp[] >>
  qpat_x_assum `MEM (_,y) obs \/ _` (DISJ_CASES_THEN assume_tac)
  >- (`MEM (k0,k1,k2) (MAP FST obs)` by
        (simp[NoAsms,MEM_MAP] >> qexists `((k0,k1,k2),y)` >>
         simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      fs[]) >>
  Cases_on `inst8.inst_opcode = INVOKE` >>
  qpat_x_assum `MEM (_,y) (if _ then _ else [])` mp_tac >> simp[] >> strip_tac >>
  `MEM (k0,k1,k2) (MAP FST (trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8)))` by
    (simp[MEM_MAP,pairTheory.EXISTS_PROD] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_then assume_tac dftGasFromListTraceNamesTheory.trace_gas_name_mem >>
  `?extra. k0 = extra ++ (d,inst8.inst_id)::p` by
    (qpat_x_assum `MEM (k0,k1,k2) (MAP FST (trace_step _ _ _ _ _ _ _))` mp_tac >>
     qspecl_then [`p`,`d`,`N-d`,`C8`,`fn8`,`inst8`,`s8`] mp_tac
       (cj 1 dftGasFromListTraceNamesTheory.trace_regions) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM,MEM_MAP] >> rpt strip_tac >>
     first_x_assum drule >> simp[dftGasFromListTraceNamesTheory.frame_below_def] >>
     metis_tac[pairTheory.FST]) >>
  `MEM (k0,k1,k2) Kroot` by
    (qpat_assum `Kroot = Kcut ++ kr` (fn th => simp[NoAsms,th,MEM_APPEND]) >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `Kroot = FLAT (MAP _ _)` (fn keys =>
    qpat_assum `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,_,NONE,NONE)`
      (fn root => qpat_x_assum `MEM (k0,k1,k2) Kroot`
        (assume_tac o SIMP_RULE bool_ss
          [keys,root,pairTheory.FST,pairTheory.SND,optionTheory.THE_DEF]))) >>
  drule_all_then strip_assume_tac dft_packet_retained_key_origin >>
  qpat_assum `!a e bb bt ps xs ys ro st h0 be ct fr cl br.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ro,st,h0,be,ct,fr,cl,br) ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!extra. ~IS_SOME (FLOOKUP acts (extra ++ _))`
    (qspec_then `extra` mp_tac) >>
  qpat_assum `FLOOKUP acts k0 = SOME _` mp_tac >>
  qpat_assum `k0 = _` (fn eq => pure_rewrite_tac [eq]) >> simp[NoAsms]
QED

(* Discharge only the pairs not already covered by the selected cut. At a
   successful cut the visit itself belongs to the source remainder. *)
Theorem focus_terminal_native_pair_reduction:
  let R = root_entry with vs_gas_readings := raw ++ [0w];
      tr8 = trace_blocks [] 0 N C8 root_tf root_entry in
  let tr7 = trace_blocks [] 0 fuel7 C7 root_sf R;
      H = if inst8.inst_opcode = INVOKE then
            trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8) else [] in
  let G = trace_gas tr7;
      uncovered = \g. !k x y. MEM (k,x) g /\
        (MEM (k,y) obs \/ MEM (k,y) H) /\
        ~(MEM k Kcut /\ MEM k (MAP FST obs)) ==> x = y in
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  terminates (run_blocks fuel7 C7 root_sf R) /\
  j < LENGTH tr8 /\ EL j tr8 = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  obs = trace_gas (TAKE j tr8) /\
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  step_inst (N-d) C8 inst8 s8 = r /\
  ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/ (?ex u. r = Abort ex u)) /\
  (((!k x y. MEM k Kcut /\ MEM k (MAP FST obs) /\
       dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k x /\
       dftGasFromListUnion$recorded C8 vs0 k y ==> x = y) /\
    ((?before visit after.
      tr7 = before ++ visit::after /\
      trace_gas before = ZIP (Kcut,TAKE (LENGTH Kcut) raw) /\
      uncovered (trace_gas before) /\ uncovered (trace_gas (visit::after))) \/
     ((?t. Kcut = MAP FST G ++ t) /\ uncovered G))) \/ static_exit) ==>
  (?orc.
    (!fuel. gas_res_rel (run_context fuel C7
      (vs0 with vs_gas_readings := raw ++ [0w])) (ev_context orc fuel C7 vs0)) /\
    (!fuel. gas_res_rel (run_context fuel C8 vs0) (ev_context orc fuel C8 vs0)) /\
    (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s ==>
      ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
        C7 fn inst (s with vs_gas_readings := ws)) /\
    (!fn inst s. raw_reachable vs0 C8 fn inst s ==>
      ?p d. ev_reachable orc vs0 C8 p d fn inst
        (s with vs_gas_readings := vs0.vs_gas_readings))) \/ static_exit
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `static_exit` >- simp[] >>
  qpat_x_assum `(_ /\ _) \/ F`
    (CONJUNCTS_THEN2 assume_tac assume_tac o REWRITE_RULE []) >>
  Q.SUBGOAL_THEN `(?u. r = Halt u) \/ (?ex u. r = Abort ex u)` assume_tac
  >- (qpat_x_assum `(?u. r = OK u /\ _) \/ _` $ DISJ_CASES_THEN2 strip_assume_tac assume_tac
      >- (`step_inst (N-d) C8 inst8 s8 = OK u` by simp[] >>
          drule_all focus_stopped_cursor_ok_nonhalted >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] focus_stopped_terminal_recordings) >>
  disch_tac >>
  qabbrev_tac `R = root_entry with vs_gas_readings := raw ++ [0w]` >>
  qabbrev_tac `tr7 = trace_blocks [] 0 fuel7 C7 root_sf R` >>
  qabbrev_tac `H = if inst8.inst_opcode = INVOKE then
      trace_gas (trace_step p d (N-d) C8 fn8 inst8 s8) else []` >>
  `!k y. dftGasFromListUnion$recorded C8 vs0 k y ==> MEM (k,y) obs \/ MEM (k,y) H` by
    (Cases_on `inst8.inst_opcode = INVOKE` >> simp[Abbr `H`]) >>
  `!n. trace_context n C7 (vs0 with vs_gas_readings := raw ++ [0w]) =
       trace_blocks [] 0 n C7 root_sf R` by
    simp[trace_context_def, trace_function_def, Abbr `R`] >>
  `!k x. dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k x ==>
         MEM (k,x) (trace_gas tr7)` by
    (simp[dftGasFromListUnionTheory.recorded_def, Abbr `tr7`] >> rpt strip_tac >>
     Cases_on `n <= fuel7`
     >- (`?suffix. trace_blocks [] 0 fuel7 C7 root_sf R =
                   trace_blocks [] 0 n C7 root_sf R ++ suffix` by
           (irule (cj 3 dftGasFromListTracePrefixTheory.trace_prefix) >> simp[]) >>
         simp[dftGasFromListReadingsTheory.trace_gas_append]) >>
     `trace_blocks [] 0 n C7 root_sf R = trace_blocks [] 0 fuel7 C7 root_sf R` by
       (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >>
        simp[] >> gen_tac >> strip_tac >> fs[terminates_def]) >>
     metis_tac[]) >>
  disj1_tac >> irule focus_stopped_shared_recording_replay >>
  reverse conj_tac >- (simp[] >> qexistsl [`root_sf`,`lbl`,`nm`] >> simp[]) >>
  map_every qx_gen_tac [`k`,`x`,`y`] >> strip_tac >>
  Cases_on `MEM k Kcut /\ MEM k (MAP FST obs)` >- metis_tac[] >>
  `MEM (k,x) (trace_gas tr7)` by metis_tac[] >>
  Q.SUBGOAL_THEN `MEM (k,y) obs \/ MEM (k,y) H` assume_tac >- metis_tac[] >>
  qpat_x_assum `(?before visit after. tr7 = before ++ visit::after /\ _) \/ _`
    (strip_assume_tac o BETA_RULE)
  >- (qpat_x_assum `MEM (k,x) (trace_gas tr7)` mp_tac >>
      qpat_assum `tr7 = _` (fn th => pure_rewrite_tac
        [th, dftGasFromListReadingsTheory.trace_gas_append, MEM_APPEND]) >>
      metis_tac[]) >>
  metis_tac[]
QED

(* Assemble the static alternative only once the fixed C7 entry abort and
   the guarded post-DFT contracts are available. *)
Theorem focus_selected_static_exit_join:
  let vi = vs0 with <|vs_gas_readings := raw ++ [0w];
                      vs_fmp := fmp; vs_initial_fmp := fmp|> in
  let v7 = vs0 with vs_gas_readings := raw ++ [0w] in
  vs0.vs_call_ctx.cc_static /\ dead_wf D /\
  ctx_sim_fuel I D unit.cu_context C7 vi v7 /\
  ctx_abort_rq D unit.cu_context C7 vi v7 /\
  ctx_sim_fuel g D C7 C9 v7 vs0 /\ ctx_abort_rq D C7 C9 v7 vs0 /\
  (fin = asm_opt_finalizer ==>
    code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
      ~in_static_abort_prefix fn s) C9) /\
  (?eom. max_live_eom C9 = SOME eom /\
    mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
      lowered_mem_fact eom ctx fn inst s) C9 vs0) /\
  C9 = out.po_unit.cu_context /\
  (?b u. run_context b C7 v7 = Abort ExHalt_abort u) /\
  ((?b u. run_context b C7 v7 = Abort ExHalt_abort u) ==>
    !fuel. terminates (run_context fuel unit.cu_context vi) ==>
      ?u. run_context fuel unit.cu_context vi = Abort ExHalt_abort u) ==>
  vs0.vs_call_ctx.cc_static /\
  ctx_sim D unit.cu_context out.po_unit.cu_context vi vs0 /\
  ctx_abort_rq D unit.cu_context out.po_unit.cu_context vi vs0 /\
  (fin = asm_opt_finalizer ==>
    code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
      ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
  (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
    mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
      lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
      out.po_unit.cu_context vs0) /\
  (!fuel. terminates (run_context fuel unit.cu_context vi) ==>
    ?u. run_context fuel unit.cu_context vi = Abort ExHalt_abort u)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ctx_sim_fuel I D unit.cu_context C7 vi _` >>
  qmatch_goalsub_abbrev_tac `ctx_sim_fuel I D unit.cu_context C7 vi v7` >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `C9 = _` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule ctx_sim_fuel_imp_ctx_sim >> qexists `g o I` >>
      irule ctx_sim_fuel_trans >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`C7`, `v7`] >> simp[]) >>
  conj_tac
  >- (irule ctx_abort_rq_trans >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`C7`, `v7`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- fs[lowered_mem_fact_def] >>
  qpat_assum `(?b u. run_context b C7 v7 = Abort ExHalt_abort u) ==> _` drule >>
  disch_then ACCEPT_TAC
QED

(* On failure only the executed part of the cut supplies a native recording. *)
Theorem focus_selected_cut_covered_agreement:
  let R = root_entry with vs_gas_readings := raw ++ [0w] in
  let tr7 = trace_blocks [] 0 fuel C7 root_sf R in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Kroot = Kcut ++ kr /\ raw_slots = Mcut ++ mr /\ LENGTH Mcut = LENGTH Kcut /\
  terminates (run_blocks fuel C7 root_sf R) /\
  ((?before after. tr7 = before ++ after /\
      trace_gas before = ZIP (Kcut,TAKE (LENGTH Mcut) raw)) \/
   (?t. Kcut = MAP FST (trace_gas tr7) ++ t)) ==>
  !k x y. MEM k Kcut /\ MEM k (MAP FST obs) /\
    dftGasFromListUnion$recorded C7 (vs0 with vs_gas_readings := raw ++ [0w]) k x /\
    dftGasFromListUnion$recorded C8 vs0 k y ==> x = y
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH Kcut <= LENGTH raw` by
    (drule LIST_REL_LENGTH >> asm_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  qpat_x_assum `(?before after. _ /\ _) \/ _` strip_assume_tac
  >- (rename1 `trace_gas before = ZIP _` >>
      `trace_gas before = ZIP (Kcut,TAKE (LENGTH Kcut) raw)` by simp[] >>
      metis_tac[focus_stopped_cut_observed_agreement]) >>
  rpt strip_tac >>
  metis_tac[SIMP_RULE bool_ss [LET_THM] focus_failed_prefix_observed_agreement]
QED

(* The owner of a GAS site is the function at the actual native visit,
   including when that visit belongs to a callee. *)
Theorem focus_native_gas_sites[local]:
  (!p d fuel ctx fn inst s.
    let vs = ((p,d,inst.inst_id),fn,inst,s)::trace_step p d fuel ctx fn inst s in
    MAP (\(key,f,i,u). (f.fn_name,i.inst_id))
      (FILTER (\(key,f,i,u). i.inst_opcode = GAS) vs) =
      gas_events_step fuel ctx fn.fn_name inst s /\
    EVERY (\((a,e,id),f,i,u). id = i.inst_id) vs) /\
  (!p d fuel ctx fn bb s.
    let vs = trace_block p d fuel ctx fn bb s in
    MAP (\(key,f,i,u). (f.fn_name,i.inst_id))
      (FILTER (\(key,f,i,u). i.inst_opcode = GAS) vs) =
      gas_events_block fuel ctx fn.fn_name bb s /\
    EVERY (\((a,e,id),f,i,u). id = i.inst_id) vs) /\
  (!p d fuel ctx fn s.
    let vs = trace_blocks p d fuel ctx fn s in
    MAP (\(key,f,i,u). (f.fn_name,i.inst_id))
      (FILTER (\(key,f,i,u). i.inst_opcode = GAS) vs) =
      gas_events_blocks fuel ctx fn s /\
    EVERY (\((a,e,id),f,i,u). id = i.inst_id) vs)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[cj 1 trace_defs, Once gas_events_step_def] >>
      Cases_on `inst.inst_opcode = GAS` >> gvs[] >>
      Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
      Cases_on `decode_invoke inst` >> simp[] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands pair1 s` >> simp[] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      once_rewrite_tac[cj 2 trace_defs, gas_events_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction _ _ = SOME inst` >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[FILTER_APPEND, MAP_APPEND, EVERY_APPEND] >>
      Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
      Cases_on `inst.inst_opcode = GAS` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cj 3 trace_defs, gas_events_blocks_def] >>
  namedCases_on `fuel` ["", "k"] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis _ _ = OK sp` >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[FILTER_APPEND, MAP_APPEND, EVERY_APPEND] >>
  rename1 `exec_block _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >> metis_tac[]
QED

Theorem focus_trace_gas_filter[local]:
  !vs. trace_gas vs =
    MAP (\(key,f,i,u). (key, case u.vs_gas_readings of [] => 0w | w::_ => w))
      (FILTER (\(key,f,i,u). i.inst_opcode = GAS) vs)
Proof
  Induct >> simp[dftGasFromListReadingsTheory.trace_gas_cons] >>
  PairCases >> simp[visit_gas_def] >> rw[]
QED

Theorem focus_terminal_suffix_gas_position:
  let R = root_entry with vs_gas_readings := raw ++ [0w] in
  let tr = trace_blocks [] 0 fuel C7 root_sf R;
      sv = FILTER (\(key,fn,i,s). i.inst_opcode = GAS) suffix in
  tr = before ++ suffix /\ LENGTH (trace_gas before) = LENGTH Ecut /\
  Ecut ++ er = gas_events_blocks fuel C7 root_sf R ++ extra /\
  LENGTH (Ecut ++ er) <= LENGTH raw ==>
  !h. h < LENGTH (trace_gas suffix) ==>
    ?a e id fn i s.
      h < LENGTH sv /\ EL h sv = ((a,e,id),fn,i,s) /\ id = i.inst_id /\
      h < LENGTH er /\ EL h er = (fn.fn_name,id) /\
      EL h (trace_gas suffix) = ((a,e,id),EL (LENGTH Ecut + h) raw)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `R = root_entry with vs_gas_readings := raw ++ [0w]` >>
  qabbrev_tac `sv = FILTER (\(key,fn,i,s). i.inst_opcode = GAS) suffix` >>
  qabbrev_tac `bv = FILTER (\(key,fn,i,s). i.inst_opcode = GAS) before` >>
  qabbrev_tac `site = \((key:gas_event),(fn:ir_function),(i:instruction),(s:venom_state)).
                         (fn.fn_name,i.inst_id)` >>
  `LENGTH bv = LENGTH Ecut` by fs[focus_trace_gas_filter, Abbr `bv`] >>
  `LENGTH sv = LENGTH (trace_gas suffix)` by simp[focus_trace_gas_filter, Abbr `sv`] >>
  `MAP site bv ++ MAP site sv = gas_events_blocks fuel C7 root_sf R /\
   EVERY (\((a,e,id),f,i,u). id = i.inst_id) suffix` by
    (qmatch_asmsub_rename_tac `trace_blocks [] 0 fuel C7 root_sf R` >>
     qspecl_then [`[]`,`0`,`fuel`,`C7`,`root_sf`,`R`] mp_tac (cj 3 focus_native_gas_sites) >>
     simp[Abbr `site`, Abbr `bv`, Abbr `sv`, FILTER_APPEND, MAP_APPEND, EVERY_APPEND]) >>
  `er = MAP site sv ++ extra` by
    (`Ecut ++ er = MAP site bv ++ (MAP site sv ++ extra)` by metis_tac[APPEND_ASSOC] >>
     `LENGTH Ecut = LENGTH (MAP site bv)` by simp[] >>
     metis_tac[APPEND_EQ_APPEND_EQ]) >>
  rpt strip_tac >>
  `h < LENGTH sv /\ h < LENGTH er /\ LENGTH Ecut + h < LENGTH raw` by
    (conj_tac >- decide_tac >> conj_tac >- fs[] >> fs[]) >>
  `trace_gas (trace_blocks [] 0 fuel C7 root_sf R) =
     trace_gas before ++ trace_gas suffix` by
    simp[dftGasFromListReadingsTheory.trace_gas_append] >>
  `LENGTH Ecut + h < gas_count_blocks fuel C7 root_sf R` by
    (pure_rewrite_tac[GSYM (Q.SPECL [`[]`,`0`]
      (cj 3 dftGasFromListReadingsTheory.trace_gas_lengths))] >> simp[]) >>
  `EL (LENGTH Ecut + h) (MAP SND (trace_gas (trace_blocks [] 0 fuel C7 root_sf R))) =
     EL (LENGTH Ecut + h) raw` by
    (pure_rewrite_tac[dftGasFromListReadingsTheory.trace_gas_readings,
                      dftGasFromListReadingsTheory.gas_prefix_genlist] >>
     simp[Abbr `R`, EL_APPEND1]) >>
  `SND (EL h (trace_gas suffix)) = EL (LENGTH Ecut + h) raw` by
    (pop_assum mp_tac >> simp[MAP_APPEND, EL_APPEND2, EL_MAP]) >>
  qabbrev_tac `v = EL h sv` >> PairCases_on `v` >>
  rename1 `Abbrev (((a,e,id),sf,i,s) = EL h sv)` >>
  `MEM ((a,e,id),sf,i,s) sv` by
    (simp[MEM_EL] >> qexists_tac `h` >> fs[markerTheory.Abbrev_def]) >>
  `MEM ((a,e,id),sf,i,s) suffix` by
    fs[Abbr `sv`, MEM_FILTER] >>
  `id = i.inst_id` by
    (qpat_x_assum `EVERY _ suffix` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `((a,e,id),sf,i,s)` mp_tac) >> simp[]) >>
  qpat_x_assum `Abbrev ((_,_,_,_) = EL h sv)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qexistsl [`a`,`e`,`id`,`sf`,`i`,`s`] >>
  simp[EL_APPEND1, EL_MAP, Abbr `site`] >>
  qpat_x_assum `SND (EL h (trace_gas suffix)) = _` mp_tac >>
  simp[focus_trace_gas_filter, Abbr `sv`, EL_MAP]
QED

(* Each step emits its prefix on descent and its remaining row on unwind. *)
Theorem focus_cut_unwind[local]:
  !n A B R. (!i. i < n ==> A i = B i ++ A (SUC i) ++ R i) ==>
    A 0 = FLAT (GENLIST B n) ++ A n ++ FLAT (REVERSE (GENLIST R n))
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  first_x_assum (qspecl_then [`A`,`B`,`R`] mp_tac) >>
  impl_tac >- simp[] >>
  `A n = B n ++ A (SUC n) ++ R n` by simp[] >>
  simp[GENLIST, REVERSE_SNOC, SNOC_APPEND, FLAT_APPEND, APPEND_ASSOC]
QED

Theorem focus_cut_unwind_table[local]:
  0 < LENGTH (cuts : ((num # num) list # num list # num # num # instruction list) list) /\
  FST (EL 0 cuts) = [] /\
  FLAT (MAP (\e. FLAT (row [] e)) (order [])) =
    FLAT (MAP (\(a,ds,e,k,z).
      FLAT (MAP (\f. FLAT (row a f)) ds) ++ FLAT (TAKE k (row a e))) cuts) ++ residual /\
  (!i a ds e k z. i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,z) ==>
    order a = ds ++ [e] /\
    (SUC i < LENGTH cuts ==>
       k < LENGTH (row a e) /\
       EL k (row a e) =
         FLAT (MAP (\f. FLAT (row (FST (EL (SUC i) cuts)) f))
           (order (FST (EL (SUC i) cuts)))))) ==>
  residual = FLAT (REVERSE (GENLIST (\i. let (a,ds,e,k,z) = EL i cuts in
            FLAT (DROP (if SUC i = LENGTH cuts then k else SUC k) (row a e)))
          (LENGTH cuts)))
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qmatch_asmsub_abbrev_tac `MAP piece cuts` >>
  qmatch_goalsub_abbrev_tac `GENLIST rest (LENGTH cuts)` >>
  qabbrev_tac `activation = \a. FLAT (MAP (\e. FLAT (row a e)) (order a))` >>
  qabbrev_tac `A = \i. if i < LENGTH cuts then activation (FST (EL i cuts)) else []` >>
  `!i. i < LENGTH cuts ==> A i = piece (EL i cuts) ++ A (SUC i) ++ rest i` by
    suspend "unwind_step" >>
  qspecl_then [`LENGTH cuts`,`A`,`\i. piece (EL i cuts)`,`rest`] mp_tac focus_cut_unwind >>
  impl_tac >- simp[] >>
  qpat_x_assum `!i. i < LENGTH cuts ==> A i = _` kall_tac >>
  fs[GENLIST_EL_MAP, Abbr `A`, Abbr `activation`, APPEND_11]
QED
Resume focus_cut_unwind_table[unwind_step]:
  rpt strip_tac >> Cases_on `EL i cuts` >> rename1 `EL i cuts = cut` >>
  PairCases_on `cut` >>
  qpat_assum `!i a ds e k z. _`
    (qspecl_then [`i`,`cut0`,`cut1`,`cut2`,`cut3`,`cut4`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> Cases_on `SUC i < LENGTH cuts`
  >- (`cut3 < LENGTH (row cut0 cut2) /\
        EL cut3 (row cut0 cut2) = activation (FST (EL (SUC i) cuts))` by
        (simp[Abbr `activation`] >> metis_tac[]) >>
      qspecl_then [`cut3`,`row cut0 cut2`] mp_tac TAKE_DROP_SUC >>
      impl_tac >- simp[] >>
      disch_then (mp_tac o Q.AP_TERM `FLAT`) >>
      simp[Abbr `A`, Abbr `piece`, Abbr `rest`, Abbr `activation`,
        MAP_APPEND, FLAT_APPEND, APPEND_ASSOC]) >>
  `SUC i = LENGTH cuts` by decide_tac >>
  simp[Abbr `A`, Abbr `piece`, Abbr `rest`, Abbr `activation`, MAP_APPEND,
    FLAT_APPEND] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM FLAT_APPEND))) >>
  rewrite_tac[TAKE_DROP]
QED
Finalise focus_cut_unwind_table

Theorem focus_cut_order_ends[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  order = ds ++ e::later /\
  ((a = p /\ e = d) \/
   (?k cid. k < LENGTH p /\ a = DROP (SUC k) p /\ EL k p = (e,cid))) ==>
  later = []
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `ALL_DISTINCT order` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
          (mp_then Any mp_tac (cj 6 th))) >>
     POP_ASSUM_LIST (K all_tac) >> disch_then SUBST1_TAC >> simp[ALL_DISTINCT_GENLIST]) >>
  `LAST order = e` by suspend "record" >>
  Cases_on `later` >- simp[] >>
  rename1 `order = ds ++ e::x::xs0` >>
  `MEM e (x::xs0)` by
    (qpat_x_assum `LAST order = e` (mp_tac o SYM) >>
     qpat_x_assum `order = _` SUBST1_TAC >>
     rewrite_tac[LAST_APPEND_CONS,LAST_CONS] >>
     disch_then SUBST1_TAC >> irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  qpat_assum `MEM e (x::xs0)` mp_tac >>
  qpat_assum `ALL_DISTINCT order` mp_tac >>
  qpat_assum `order = _` SUBST1_TAC >>
  POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_APPEND]
QED
Resume focus_cut_order_ends[record]:
  qpat_x_assum `(a = p /\ e = d) \/ _` strip_assume_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`a = p`, `e = d`, `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
         `FLOOKUP acts p = SOME (_,_,_,_,_,NONE,NONE)`, `LAST _ = d`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  qpat_assum `!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
       q h b0 done_at_call child_entry cid e a. _` (qspec_then `k` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
  rename1 `(e1,cid1) = EL k p` >>
  rename1 `a1 = DROP (SUC k) p` >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`a = DROP (SUC k) p`, `EL k p = (e,cid)`,
     `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
     `a1 = DROP (SUC k) p`, `FLOOKUP acts a1 = SOME (_,_,_,_,_,NONE,NONE)`,
     `(e1,cid1) = EL k p`, `LAST _ = e1`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED
Finalise focus_cut_order_ends

Theorem focus_cut_call_cells[local]:
  let order = \a. FST (SND (SND (SND (SND (THE (FLOOKUP acts a)))))) in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (k,h,b0,done,child_entry,ret) ==>
  k < LENGTH (THE (FLOOKUP ms_tab (a,e))) /\
  EL k (THE (FLOOKUP ms_tab (a,e))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab ((e,cid)::a,f)))) (order ((e,cid)::a))) /\
  k < LENGTH (THE (FLOOKUP es_tab (a,e))) /\
  EL k (THE (FLOOKUP es_tab (a,e))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab ((e,cid)::a,f)))) (order ((e,cid)::a))) /\
  k < LENGTH (THE (FLOOKUP ks_tab (a,e))) /\
  EL k (THE (FLOOKUP ks_tab (a,e))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ((e,cid)::a,f)))) (order ((e,cid)::a)))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`
    (fn th => drule th) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
  `?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
     FLOOKUP ks_tab (a,e) = SOME ks` by
    (qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     map_every (fn pat => qpat_assum pat (mp_tac o GSYM))
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`, `FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[FLOOKUP_DEF, AllCaseEqs()]) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
     FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\ _ ==> _` drule_all >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (drule_then (qspec_then `k` mp_tac o CONJUNCT1)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`k < LENGTH _`, `_ = EL k _`, `_.inst_id = cid`, `_.inst_opcode = INVOKE`,
     `FLOOKUP calls (a,e,cid) = SOME _`, `LENGTH ms = _`, `LENGTH ess = _`, `LENGTH ks = _`,
     `FLOOKUP ms_tab (a,e) = SOME ms`, `FLOOKUP es_tab (a,e) = SOME ess`,
     `FLOOKUP ks_tab (a,e) = SOME ks`, `AM = _`, `AE = _`, `AK = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED

Theorem focus_cut_unwind_geometry[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  MAP (\(a,ds,e,k,z). a) cuts = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  (!i a ds e k (z:instruction list). i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,z) ==>
    ?sf tf inc entry order res nrest later.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = ds ++ e::later /\
      (if SUC i = LENGTH cuts then a = p /\ e = d else
        ?cid h b0 done child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (e,cid)::a /\
          FLOOKUP calls (a,e,cid) = SOME (k,h,b0,done,child_entry,ret))) ==>
  0 < LENGTH cuts /\ FST (EL 0 cuts) = [] /\
  (!i a ds e k z. i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,z) ==>
    FST (SND (SND (SND (SND (THE (FLOOKUP acts a)))))) = ds ++ [e] /\
    (SUC i < LENGTH cuts ==>
      ?cid h b0 done child_entry ret.
        FST (EL (SUC i) cuts) = (e,cid)::a /\
        FLOOKUP calls (a,e,cid) = SOME (k,h,b0,done,child_entry,ret)))
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qmatch_asmsub_abbrev_tac `MAP path cuts = REVERSE _` >>
  `LENGTH cuts = SUC (LENGTH p)` by
    (qpat_assum `MAP path cuts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `!i. i < LENGTH cuts ==> EL i (MAP path cuts) = DROP (LENGTH p - i) p` by
    (rpt strip_tac >> `PRE (SUC (LENGTH p) - i) = LENGTH p - i` by decide_tac >>
     simp[EL_REVERSE, EL_GENLIST]) >>
  `!i. i < LENGTH cuts ==> path (EL i cuts) = FST (EL i cuts)` by
    (rpt strip_tac >> Cases_on `EL i cuts` >> rename1 `EL i cuts = cut` >>
     PairCases_on `cut` >> simp[Abbr `path`]) >>
  conj_tac >- simp[] >> conj_tac
  >- (`EL 0 (MAP path cuts) = path (EL 0 cuts)` by (irule EL_MAP >> decide_tac) >>
      qpat_assum `!i. i < LENGTH cuts ==> EL i (MAP path cuts) = _`
        (qspec_then `0` mp_tac) >>
      qpat_assum `!i. i < LENGTH cuts ==> path (EL i cuts) = _`
        (qspec_then `0` mp_tac) >>
      qpat_assum `EL 0 (MAP path cuts) = _` mp_tac >>
      qpat_assum `LENGTH cuts = SUC _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[DROP_LENGTH_NIL] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i a ds e k z. _` drule_all >> strip_tac >>
  `later = []` by
    (irule focus_cut_order_ends >> rpt (goal_assum (drule_at Any)) >> suspend "live_path") >>
  conj_tac >- gs[] >> strip_tac >> gvs[EL_MAP] >> metis_tac[]
QED
Resume focus_cut_unwind_geometry[live_path]:
  Cases_on `SUC i = LENGTH cuts` >- gvs[] >>
  `SUC i < LENGTH cuts` by decide_tac >>
  qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >> simp[] >> strip_tac >>
  disj2_tac >> qexistsl [`LENGTH p - SUC i`,`cid`] >>
  `LENGTH p - SUC i < LENGTH p /\ SUC (LENGTH p - SUC i) = LENGTH p - i` by decide_tac >>
  qspecl_then [`LENGTH p - SUC i`,`p`] mp_tac rich_listTheory.DROP_CONS_EL >>
  simp[] >> metis_tac[]
QED
Finalise focus_cut_unwind_geometry

Theorem focus_selected_cut_residual_rows:
  let order = \a. FST (SND (SND (SND (SND (THE (FLOOKUP acts a)))))) in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  MAP (\(a,ds,e,k,z). a) cuts = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  (!i a ds e k (z:instruction list). i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,z) ==>
    ?sf tf inc entry order res nrest later.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = ds ++ e::later /\
      (if SUC i = LENGTH cuts then a = p /\ e = d else
        ?cid h b0 done child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (e,cid)::a /\
          FLOOKUP calls (a,e,cid) = SOME (k,h,b0,done,child_entry,ret))) /\
  raw_slots = FLAT (MAP (\(a,ds,e,k,z).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) ++
    FLAT (TAKE k (THE (FLOOKUP ms_tab (a,e))))) cuts) ++ mr /\
  sites = FLAT (MAP (\(a,ds,e,k,z).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (a,f)))) ds) ++
    FLAT (TAKE k (THE (FLOOKUP es_tab (a,e))))) cuts) ++ er /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) (order [])) =
    FLAT (MAP (\(a,ds,e,k,z).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) ++
      FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e))))) cuts) ++ kr ==>
  er = FLAT (REVERSE (GENLIST (\i. let (a,ds,e,k,z) = EL i cuts in
    FLAT (DROP (if SUC i = LENGTH cuts then k else SUC k)
      (THE (FLOOKUP es_tab (a,e))))) (LENGTH cuts))) /\
  mr = FLAT (REVERSE (GENLIST (\i. let (a,ds,e,k,z) = EL i cuts in
    FLAT (DROP (if SUC i = LENGTH cuts then k else SUC k)
      (THE (FLOOKUP ms_tab (a,e))))) (LENGTH cuts))) /\
  kr = FLAT (REVERSE (GENLIST (\i. let (a,ds,e,k,z) = EL i cuts in
    FLAT (DROP (if SUC i = LENGTH cuts then k else SUC k)
      (THE (FLOOKUP ks_tab (a,e))))) (LENGTH cuts)))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all focus_cut_unwind_geometry >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `raw_slots = FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
   sites = FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))` by
    (qhdtm_assum `dft_focus_packet_rel` (mp_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (fn th => map_every assume_tac (CONJUNCTS th))) >>
     simp[]) >>
  rpt conj_tac >>
  (let
    fun unwind row = Q.ISPECL_THEN
      [row, `\a. FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))`]
      (irule o BETA_RULE o REWRITE_RULE [LET_THM])
      (Q.GENL [`row`, `order`] focus_cut_unwind_table)
   in FIRST (map unwind [`\a e. THE (FLOOKUP es_tab (a,e))`,
                         `\a e. THE (FLOOKUP ms_tab (a,e))`,
                         `\a e. THE (FLOOKUP ks_tab (a,e))`]) end) >>
  asm_rewrite_tac[] >> qexists_tac `acts` >>
  (reverse conj_tac >- (simp[] >> metis_tac[])) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i a ds e k z. _ ==> _ /\ (SUC i < LENGTH cuts ==> _)`
    drule_all >> strip_tac >>
  (conj_tac >- simp[]) >> strip_tac >>
  qpat_assum `SUC i < LENGTH cuts ==> _` drule >> strip_tac >>
  drule_all (BETA_RULE (REWRITE_RULE [LET_THM] focus_cut_call_cells)) >> simp[]
QED

Theorem focus_packet_recorded_call_position:
  let t = b0.vs_inst_idx - LENGTH ps in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (r,h,b0,done,ent,ret) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),ct,front,closed,brest) ==>
  t < LENGTH ys /\ r = EL t sched /\ EL t ys = EL r xs /\
  (EL r xs).inst_id = cid /\ (EL r xs).inst_opcode = INVOKE /\
  (IS_SOME ret ==> t < ct /\ MEM r (TAKE ct sched)) /\
  (ret = NONE ==> t = ct /\ ?j. j < LENGTH p /\ DROP j p = (e,cid)::a)
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `r < LENGTH xs /\ (EL r xs).inst_id = cid /\ (EL r xs).inst_opcode = INVOKE /\
   LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME (EL r xs) /\
   ~MEM r (TAKE (b0.vs_inst_idx - LENGTH ps) sched) /\
   (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
      | SOME _ => MEM r (TAKE ct sched))` by
    (qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> _` drule >>
     qpat_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
     Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[]) >>
  `bt.bb_instructions = ps ++ ys /\ ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
   LIST_REL (\i y. i < LENGTH xs /\ y.inst_id = (EL i xs).inst_id /\ from_block [EL i xs] y)
     sched ys` by
    (qpat_assum `!a e bb bt ps xs ys rho s h ob ct fr cl br.
       FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,s,h,ob,ct,fr,cl,br) ==> _` drule >>
     disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
     (conj_tac >- simp[]) >> (reverse conj_tac >- simp[]) >>
     rename1 `lookup_block bb.bb_label sf.fn_blocks = SOME bb` >>
     `MEM sf C7.ctx_functions` by
       (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _` drule >>
        simp[]) >>
     `wf_function sf` by
       (qpat_assum `o1_ctx_shape C7`
          (mp_then Any mp_tac dftContractGasTheory.o1_ctx_shape_wf_functions) >>
        rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `sf` mp_tac) >> simp[]) >>
     `MEM bb sf.fn_blocks` by
       (qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb`
          (mp_then Any irule venomExecPropsTheory.lookup_block_MEM)) >>
     drule_all dftWfTheory.wf_fn_block_inst_ids_distinct >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  qabbrev_tac `t = b0.vs_inst_idx - LENGTH ps` >>
  `t < LENGTH ys /\ EL t ys = EL r xs` by
    (qpat_x_assum `get_instruction bt b0.vs_inst_idx = SOME _` mp_tac >>
     simp[get_instruction_def, EL_APPEND_EQN, Abbr `t`] >>
     Cases_on `b0.vs_inst_idx < LENGTH ps + LENGTH ys` >> simp[]) >>
  `r = EL t sched` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `ALL_DISTINCT (MAP _ xs)` (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
     disch_then (qspecl_then [`r`,`EL t sched`] mp_tac) >> simp[EL_MAP]) >>
  simp[] >> conj_tac
  >- (Cases_on `ret` >> simp[] >>
      `MEM r (TAKE ct sched)` by
        (qpat_assum `case SOME _ of NONE => _ | SOME _ => _` (mp_tac o SRULE []) >>
         disch_then ACCEPT_TAC) >>
      qpat_assum `MEM r (TAKE ct sched)` mp_tac >>
      qpat_assum `~MEM r (TAKE t sched)` mp_tac >>
      qpat_assum `r = EL t sched` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qpat_x_assum `r = EL t sched` (SUBST_ALL_TAC o SYM) >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      spose_not_then assume_tac >>
      `ct <= t` by decide_tac >>
      `MEM r (TAKE ct (TAKE t sched))` by simp[rich_listTheory.TAKE_TAKE_T] >>
      metis_tac[rich_listTheory.MEM_TAKE]) >>
  suspend "live"
QED
Resume focus_packet_recorded_call_position[live]:
  strip_tac >>
  `?k. k < LENGTH p /\ DROP k p = (e,cid)::a` by
    (qpat_assum `case ret of NONE => _ | SOME _ => _` mp_tac >>
     qpat_assum `ret = NONE` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     disch_then SUBST1_TAC >> simp[MEM_GENLIST] >> strip_tac >>
     rename1 `(e,cid)::a = DROP k p` >>
     `k < LENGTH p` by (spose_not_then assume_tac >> gvs[DROP_LENGTH_TOO_LONG]) >>
     qexists `k` >> metis_tac[]) >>
  conj_tac
  >- (`a = DROP (SUC k) p /\ EL k p = (e,cid)` by
        (drule rich_listTheory.DROP_CONS_EL >> simp[]) >>
      qpat_assum `!k. k < LENGTH p ==>
        ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe ct
          q h b0 done child cid e a. _` (qspec_then `k` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
      map_every (fn pat => qpat_x_assum pat mp_tac)
        [`FLOOKUP calls (a,e,cid) = SOME (r,h,b0,done,ent,ret)`,
         `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,_,_,_,ct,_,_,_)`,
         `FLOOKUP calls (_,_,_) = SOME (_,_,_,_,_,NONE)`,
         `FLOOKUP blocks (_,_) = SOME (_,_,_,_,_,_,_,_,_,_,OK _,F,NONE)`,
         `_.vs_inst_idx = LENGTH _ + _`,
         `a = DROP (SUC k) p`, `EL k p = (e,cid)`,
         `_ = DROP (SUC k) p`, `(_,_) = EL k p`,
         `Abbrev (t = b0.vs_inst_idx - LENGTH ps)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[Abbr `t`]) >>
  qexists `k` >> simp[]
QED
Finalise focus_packet_recorded_call_position

Theorem focus_packet_invoke_predecessor_order:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,body_entry,ct,front,closed,brest) /\
  t < c /\ c < LENGTH ys /\ r = EL t sched /\ k = EL c sched /\
  (EL r xs).inst_opcode = INVOKE /\
  (let x = EL k xs; y = EL r xs in
    x.inst_opcode = INVOKE \/ is_terminator x.inst_opcode \/
    ~dftDefs$dft_abort_compatible x.inst_opcode y.inst_opcode \/
    dftScheduleOrder$dft_must_order x y) ==>
  r < k
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys rho s h ob ct fr cl br.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,s,h,ob,ct,fr,cl,br) ==> _` drule >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `dftRunRel$dft_fn_rel sf tf` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _` drule >> simp[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`t < c`, `c < LENGTH ys`, `r = EL t sched`, `k = EL c sched`,
     `(EL r xs).inst_opcode = INVOKE`, `_ \/ _`,
     `dftRunRel$dft_fn_rel sf tf`, `lookup_block bb.bb_label sf.fn_blocks = SOME bb`,
     `lookup_block bb.bb_label tf.fn_blocks = SOME bt`,
     `bb.bb_instructions = ps ++ xs`, `bt.bb_instructions = ps ++ ys`,
     `EVERY (\i. is_pseudo i.inst_opcode) ps`, `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
     `PERM sched (COUNT_LIST (LENGTH xs))`, `LIST_REL _ sched ys`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `wf_function sf` by fs[dftRunRelTheory.dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  drule_all dftRunRelTheory.dft_fn_rel_lookup_order >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions)` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
       (irule dftWfTheory.wf_fn_block_inst_ids_distinct >> metis_tac[]) >>
     `FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       simp[FILTER_EQ_ID,FILTER_EQ_NIL] >>
     qpat_assum `dftScheduleOrder$dft_block_rel bb bt`
       (strip_assume_tac o REWRITE_RULE [dftScheduleOrderTheory.dft_block_rel_def]) >>
     `PERM (MAP (\i. i.inst_id) ys) (MAP (\i. i.inst_id) xs)` by
       gvs[FILTER_APPEND_DISTRIB] >>
     irule (iffRL sortingTheory.ALL_DISTINCT_PERM) >>
     qexists `MAP (\i. i.inst_id) bb.bb_instructions` >>
     gvs[sortingTheory.PERM_APPEND_IFF,FILTER_APPEND_DISTRIB]) >>
  `LENGTH sched = LENGTH ys /\ r < LENGTH xs /\ k < LENGTH xs /\
   (EL t ys).inst_id = (EL r xs).inst_id /\ (EL c ys).inst_id = (EL k xs).inst_id` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> `t < LENGTH sched /\ c < LENGTH sched` by decide_tac >> metis_tac[]) >>
  `r <> k` by
    (`ALL_DISTINCT sched` by metis_tac[sortingTheory.ALL_DISTINCT_PERM,all_distinct_count_list] >>
     pop_assum (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
     disch_then (qspecl_then [`t`,`c`] mp_tac) >> simp[]) >>
  spose_not_then assume_tac >> `k < r` by decide_tac >>
  `MEM (EL k xs) bb.bb_instructions /\ MEM (EL r xs) bb.bb_instructions` by
    metis_tac[MEM_EL,MEM_APPEND] >>
  `~is_pseudo (EL k xs).inst_opcode /\ ~is_pseudo (EL r xs).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `dftScheduleOrder$id_before (MAP (\i. i.inst_id) bb.bb_instructions)
     (EL k xs).inst_id (EL r xs).inst_id` by
    (simp[] >> irule dftRunRelTheory.id_before_append_right >>
     simp[dftScheduleOrderTheory.id_before_def] >> qexistsl [`k`,`r`] >> simp[EL_MAP]) >>
  `dftScheduleOrder$id_before (MAP (\i. i.inst_id) bt.bb_instructions)
     (EL r xs).inst_id (EL k xs).inst_id` by
    (simp[] >> irule dftRunRelTheory.id_before_append_right >>
     simp[dftScheduleOrderTheory.id_before_def] >> qexistsl [`t`,`c`] >> simp[EL_MAP]) >>
  drule_all_then assume_tac dftRunRelTheory.dft_inversion_not_must_order >>
  drule_then assume_tac dftRunRelTheory.dft_must_order_invokes >>
  metis_tac[dftRunRelTheory.dft_wf_order_nonterminator,dftRunRelTheory.id_before_asym]
QED

Theorem focus_terminal_invoke_order_cases:
  i.inst_opcode <> INVOKE /\ dftStructural$from_block [x] i /\
  inst_shape_ok x /\ y.inst_opcode = INVOKE /\ step_inst f C i s = r /\
  ((?u. r = Halt u) \/ (?ex u. r = Abort ex u)) ==>
  x.inst_opcode = INVOKE \/ is_terminator x.inst_opcode \/
  ~dftDefs$dft_abort_compatible x.inst_opcode y.inst_opcode \/
  dftScheduleOrder$dft_must_order x y
Proof
  strip_tac >>
  `step_inst f C x s = r` by
    (fs[dftStructuralTheory.from_block_def] >>
     metis_tac[dftPermSimTheory.flip_operands_step_inst]) >>
  gvs[]
  >- (drule opcodeClassTheory.step_inst_halt_opcodes >>
      strip_tac >> simp[is_terminator_def]) >>
  drule opcodeClassTheory.step_inst_abort_opcodes >> rpt strip_tac >>
  simp[is_terminator_def, dftDefsTheory.dft_abort_compatible_def,
       dftDefsTheory.dft_abort_kind_def, dftScheduleOrderTheory.dft_must_order_def,
       venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def, pred_setTheory.DISJOINT_INSERT,
       pred_setTheory.DISJOINT_INSERT']
QED

(* A table suffix with one cell per instruction, keeping only singleton cells. *)
Theorem focus_flat_singleton_suffix[local]:
  LENGTH (cells:'b list list) = LENGTH (xs:'a list) /\
  (!r. b <= r /\ r < LENGTH xs ==>
    EL r cells = (if P (EL r xs) then [f (EL r xs)] else [])) ==>
  FLAT (DROP b cells) = MAP f (FILTER P (DROP b xs))
Proof
  strip_tac >>
  `DROP b cells = MAP (\x. if P x then [f x] else []) (DROP b xs)` by
    (once_rewrite_tac[LIST_EQ_REWRITE] >> simp[] >> rpt strip_tac >>
     simp[EL_MAP, EL_DROP]) >>
  pop_assum SUBST1_TAC >>
  qmatch_goalsub_abbrev_tac `MAP _ ys` >>
  POP_ASSUM_LIST (K all_tac) >>
  Induct_on `ys` >> simp[] >> qx_gen_tac `x` >> Cases_on `P x` >> simp[]
QED

Theorem focus_residual_row_gas_cells:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho in_state h0 body_entry ct front closed brest b.
  let g = if IS_SOME body_entry then FILTER (\i. i.inst_opcode = GAS) (DROP b xs)
          else [] in
  let keys = MAP (\i. (a,e,i.inst_id)) g in
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,ct,front,closed,brest) /\
  (!r. b <= r /\ r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==>
    FLOOKUP calls (a,e,(EL r xs).inst_id) = NONE) ==>
  FLAT (DROP b (THE (FLOOKUP ks_tab (a,e)))) = keys /\
  FLAT (DROP b (THE (FLOOKUP es_tab (a,e)))) = MAP (\i. (sf.fn_name,i.inst_id)) g /\
  FLAT (DROP b (THE (FLOOKUP ms_tab (a,e)))) = MAP (ALOOKUP obs) keys
Proof
  rpt gen_tac >> rewrite_tac[LET_THM, MAP_MAP_o, combinTheory.o_DEF] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = (_,_)`
    (CONJUNCTS_THEN2 (K all_tac) SUBST_ALL_TAC o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  Cases_on `body_entry`
  >- (qpat_assum `!a e bb bt ps xs ys rho s h ob ct fr cl br.
        FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,s,h,ob,ct,fr,cl,br) ==> _`
        (fn invariant => qpat_assum
          `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,_,_)`
          (mp_then Any mp_tac invariant)) >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >>
      disch_then (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      simp[]) >>
  PairCases_on `x` >>
  `?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP blocks (a,e) = SOME _`, `FDOM blocks = FDOM ms_tab`,
       `FDOM blocks = FDOM es_tab`, `FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule focus_flat_singleton_suffix >> simp[] >> rpt strip_tac >>
  rename1 `r < LENGTH xs` >>
  qpat_assum `!q. q < LENGTH xs ==> _` (qspec_then `r` mp_tac) >>
  Cases_on `(EL r xs).inst_opcode = GAS` >> simp[] >>
  Cases_on `(EL r xs).inst_opcode = INVOKE` >> simp[] >>
  `FLOOKUP calls (a,e,(EL r xs).inst_id) = NONE` by
    (qpat_assum `!r. b <= r /\ r < LENGTH xs /\ _ ==> _`
      (qspec_then `r` mp_tac) >> simp[]) >>
  qpat_assum `!q. q < LENGTH xs ==> _ /\ _ /\ ((EL q xs).inst_opcode = INVOKE ==> _)`
    (qspec_then `r` (fn row =>
      qpat_assum `r < LENGTH xs` (mp_tac o cj 3 o MP row))) >>
  disch_then (fn invoke_case =>
    qpat_assum `(EL r xs).inst_opcode = INVOKE` (fn opcode =>
      qpat_assum `FLOOKUP calls (a,e,(EL r xs).inst_id) = NONE` (fn lookup =>
        STRIP_ASSUME_TAC (REWRITE_RULE [lookup, optionTheory.option_case_def]
          (MP invoke_case opcode))))) >>
  first_assum ACCEPT_TAC
QED

Theorem focus_stopped_filling_replay:
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
  (0 < N /\
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
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (?align old_cursors old_asm old_sym costs.
    LENGTH costs = LENGTH evs9 /\ LENGTH old_asm = LENGTH evs9 /\
    (fin = asm_opt_finalizer ==> LENGTH old_sym = LENGTH evs9) /\
    align 0 = 0 /\ align (LENGTH evs9) = j /\
    asm_fuel = SUM costs /\ ast = EL (LENGTH evs9) ((entry_asm_state vs0 es0)::old_asm) /\
    (fin = asm_opt_finalizer ==> ss = EL (LENGTH evs9) (sym_init (entry_asm_state vs0 es0)::old_sym)) /\
    LIST_REL (\cost edge. 0 < cost \/
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (SND edge) <
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (FST edge))
      costs (ZIP (TAKE (LENGTH evs9) (q90::qs9),qs9)) /\
    (!k. k < LENGTH evs9 ==>
      align k <= j /\
      (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
      align (SUC k) <= j /\
      cfg_norm_joint_cursors (stage 8) (stage 9) (old_cursors k) (EL (align k) (q80::qs8)) (EL k
        (q90::qs9)) /\
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog (EL k costs) (EL k ((entry_asm_state vs0 es0)::old_asm)) =
          AsmOK (EL (SUC k) ((entry_asm_state vs0 es0)::old_asm)) /\
      (fin = asm_opt_finalizer ==>
        sym_steps prog (asm_data_env prog vs0.vs_code) (EL k costs) (EL k (sym_init (entry_asm_state vs0
          es0)::old_sym)) =
          SymOK (EL (SUC k) (sym_init (entry_asm_state vs0 es0)::old_sym))) /\
      (case ((EL (align k) (q80::qs8)),(EL k (q90::qs9))) of
        (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
         JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
          (~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
    source_memory_reads_disjoint cpl inst9 s9 /\
    context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
    !dst x sz src off.
      inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
      code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2)) /\ (active_inst fn9 inst9 s9 /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm' ops callee args ent.
      decode_invoke inst9 = SOME (nm',ops) /\
      lookup_function nm' (stage 9).ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
          (align (SUC k) = SUC (align k) /\ i8.inst_opcode = GAS ==>
            u8.vs_gas_readings <> [])))) /\
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          (p <> p \/ d <> d \/ s8 <> s8 \/
            (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
             (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
          (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
             inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
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
            u.vs_initial_fmp = s8.vs_initial_fmp))) /\
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
                u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  ((?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\
      r8 = (case r of OK u => Halt u | other => other) /\
      ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/
       (?ex u. r = Abort ex u)) /\
      inst8.inst_opcode <> INVOKE /\
      run_blocks N (stage 8) root_tf root_entry = r8 /\
      (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
          raw_slots gs ==>
        ?extra. sites = gas_events_blocks F (stage 7) root_sf
          (root_entry with vs_gas_readings := gs ++ tail) ++ extra)) \/
    in_revert_forward fn9 s9 \/
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     (~source_memory_reads_disjoint cpl inst9 s9 \/
      ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
    (fin = asm_opt_finalizer /\
      ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
        inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
        eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
        ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
    (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
    (inst9.inst_opcode = INVOKE /\
     ~(?callee_name ops callee args ent.
        decode_invoke inst9 = SOME (callee_name,ops) /\
        lookup_function callee_name (stage 9).ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
    (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err)) /\
  (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?rest. MAP project sites = markf (raw ++ [0w]) ++ rest)) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  (?fr. terminates (run_context fr unit.cu_context
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
  dead_wf D /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  (fin = asm_opt_finalizer ==>
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
               s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
       unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
  (?orc.
    (!fuel. gas_res_rel (run_context fuel (stage 7)
      (vs0 with vs_gas_readings := raw ++ [0w]))
      (ev_context orc fuel (stage 7) vs0)) /\
    (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
      (ev_context orc fuel (stage 8) vs0)) /\
    (!p d fn inst s. ev_reachable orc vs0 (stage 7) p d fn inst s ==>
      ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
           (stage 7) fn inst (s with vs_gas_readings := ws)) /\
    (!fn inst s. raw_reachable vs0 (stage 8) fn inst s ==>
      ?p d. ev_reachable orc vs0 (stage 8) p d fn inst
        (s with vs_gas_readings := vs0.vs_gas_readings))) \/
  (vs0.vs_call_ctx.cc_static /\
   ctx_sim D unit.cu_context out.po_unit.cu_context
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
   ctx_abort_rq D unit.cu_context out.po_unit.cu_context
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
   (fin = asm_opt_finalizer ==>
      code_end_offset_ok
        (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
          ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
   (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
     mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
               lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
       out.po_unit.cu_context vs0) /\
   (!fuel. terminates (run_context fuel unit.cu_context
             (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
           ?u. run_context fuel unit.cu_context
                 (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
               Abort ExHalt_abort u))
Proof
  cheat
QED

(* Check both joins against the same existentially selected witness. *)
val _ = let
  fun normalize tm =
    rhs (concl (QCONV (PURE_REWRITE_CONV [LET_THM] THENC DEPTH_CONV BETA_CONV) tm))
  val (roots, selection) = dest_imp (normalize (concl focus_walk_stopped_selection))
  val selected = strip_conj (snd (strip_exists selection))
  val coverage = CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM] focus_packet_coverage)
  val (needed, ordered) = dest_imp (concl coverage)
  val frontier = List.take (selected, length selected - 1)
  val (terminal, other_stops) = dest_disj (List.last frontier)
  val (witnesses, body) = strip_exists terminal
  val (invoke_guard, terminal_facts) =
    List.partition (aconv ``inst8.inst_opcode <> INVOKE``) (strip_conj body)
  val _ = if length invoke_guard = 1 then ()
          else raise Fail "C1.16 terminal INVOKE guard"
  val coverage_stop = mk_disj
    (list_mk_exists (witnesses, list_mk_conj terminal_facts), other_stops)
  val facts = coverage_stop :: strip_conj roots @ frontier
  val _ = if List.all (fn tm => List.exists (aconv tm) facts) (strip_conj needed)
              andalso aconv (List.last selected) ordered then ()
          else raise Fail "C1.16 selection and coverage must use the same stopped packet"
  val replay = CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM] focus_stopped_filling_replay)
  val (replay_input, replay_facts) = dest_imp (concl replay)
  val (shared, late) =
    List.partition (fn tm => List.exists (aconv tm) (strip_conj roots @ selected))
      (strip_conj replay_input)
  val _ = if length late = 5 andalso length shared = length (strip_conj roots @ selected)
          then ()
          else raise Fail "C1.16 replay must take the selected witness before the late hypotheses"
  val _ = drule coverage (facts, ordered)
  val _ = drule replay (shared @ late, replay_facts)
  in
    print "C1.16: coverage and filling replay use the same stopped packet\n"
  end
