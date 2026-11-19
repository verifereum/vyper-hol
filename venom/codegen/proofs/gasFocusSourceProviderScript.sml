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
