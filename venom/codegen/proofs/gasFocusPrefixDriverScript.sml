Theory gasFocusPrefixDriver
Ancestors
  o1PipelineCorrect o1SafeUpto o1PassContract o1RequestContract o1PassLift gasEvents
  codegenEntryRel codegenAsmProgOk asmFrameRel frameJointTrace asmSem symbolResolve
  frameOutcome callTrace vfmExecution frameHistoryCfg frameOriginHistory
  frameJointTransition venomExecProps blockSimHelpers fnSimSpec
  asmOptimizer codegenEntrySim codegenSymRel dftDefs unitMemInv finite_map
  list rich_list pred_set words arithmetic

(* Proof goals only. These ML values register no HOL definitions or theorems.
   The packet, CFG cursor and frame-plan conjuncts will be joined here once
   their main-based owner theories are available. *)

val focus_producer_goal : term = ``
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  initial_ctx_rel_tail [] cpl prog out.po_unit.cu_context vs0 es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  (!gs. ?D f extra.
    dead_wf D /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with vs_gas_readings := gs) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      !D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with vs_gas_readings := raw ++ [0w]))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        o1_lowered_inv out.po_unit.cu_context vs0
``;

(* Unproved parent header, kept verbatim with focus_producer_goal. *)
(* Generic finalizers and the unchanged identity boundary share one run. *)
Theorem focus_producer_finalizer:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  (!gs. ?D f extra.
    dead_wf D /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with vs_gas_readings := gs) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      !D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with vs_gas_readings := raw ++ [0w]))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        o1_lowered_inv out.po_unit.cu_context vs0
Proof
  cheat
QED

Theorem focus_producer:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  initial_ctx_rel_tail [] cpl prog out.po_unit.cu_context vs0 es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  (!gs. ?D f extra.
    dead_wf D /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with vs_gas_readings := gs) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      !D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with vs_gas_readings := raw ++ [0w]))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        o1_lowered_inv out.po_unit.cu_context vs0
Proof
  cheat
QED

(* The actual execution component of the simultaneous motive. The empty
   tail belongs to the initial relation; the current tail is explicit. *)
val focus_finalizer_prefix_bridge_goal : term = ``
  \fin rpolicy unit cpl prog prog' vs0 es0 result final.
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_ready unit.cu_context /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?max_cost. !n ast.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n (entry_asm_state vs0 es0) = AsmOK ast /\
      (?ss. sym_steps prog (asm_data_env prog vs0.vs_code) n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
      n <= max_cost /\
      (ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" ==>
        ast.as_gas_readings <> [])
``;

val focus_execution_motive : term = ``
  \vs0 ctx prog data es0 ast0 result final tail q0 evs qs q n ast es.
    joint_trace vs0 ctx q0 evs qs q /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast0 = AsmOK ast /\
    asm_frame_rel_tail tail prog data es0 ast es /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final
``;

val focus_block_rank : term = ``
  \q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => 0
    | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx
``;

(* Explicit component parameters allow owners to fix their interfaces before
   their theories are imported here. Each step below is a goal function:
   instantiate its parameters before attempting a proof. In particular no
   preservation theorem is claimed for arbitrary component predicates. *)
val focus_joint_motive : term = ``
  \packet_rel cursor_rel frame_rel
    fin rpolicy unit cpl prog prog' vs0 es0 ast0 result final
    (C7:venom_context) C8 C9
    (root_sf:ir_function) (root_tf:ir_function) (root_entry:venom_state)
    packet
    (acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap)
    (es_tab : (((num # num) list # num), (string # num) list list) fmap)
    (ks_tab : (((num # num) list # num), gas_event list list) fmap)
    rooted_eval p d cursors
    q8 q0 evs qs q9 n ast ss raw_slots sites unused.
    ?N:num. packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    cursor_rel C8 C9 cursors q8 q9 /\
    frame_rel (asm_data_env prog vs0.vs_code)
      rpolicy unit cpl prog vs0 es0 q9 ast ss /\
    joint_trace vs0 C9 q0 evs qs q9 /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast0 = AsmOK ast /\
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init ast0) = SymOK ss /\
    ast0 = entry_asm_state vs0 es0 /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    codegen_asm_entry_rel cpl prog vs0 ast0 /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (ast0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0)
``;

val focus_dft_packet_step_goal : term = ``
  \packet_rel.
  !(N:num) (C7:venom_context) C8 (root_sf:ir_function) (root_tf:ir_function)
    (root_entry:venom_state) packet
    (acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap)
    (es_tab : (((num # num) list # num), (string # num) list list) fmap)
    (ks_tab : (((num # num) list # num), gas_event list list) fmap)
    rooted_eval p d cpl es0 raw_slots sites unused
    stk PG G tn fn inst s oms om hs h ev q8'.
    packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    (inst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
    joint_transition C8 (JointConfig stk PG G tn fn inst s oms om hs h) ev q8' ==>
    (?N' packet' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d'
      raw_slots' sites' unused'.
      packet_rel N' C7 C8 root_sf root_tf root_entry
        packet' acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d'
        q8' raw_slots' sites' unused' /\
      LENGTH raw_slots' = LENGTH sites' /\
      PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0)) /\
    ( (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
       inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s ==>
      ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z
        cuts levels Mcut Ecut.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        LAST order = d /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE) /\
        q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
          MEM r (TAKE count rho)) /\
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
              ?cid call_h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
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
        LENGTH Mcut = LENGTH Ecut /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            C7 (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\
          ~in_revert_forward sf u /\
          (inv_memory_observation inst.inst_opcode ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
            u.vs_initial_fmp = s.vs_initial_fmp)))
``;

val focus_cfg_cursor_step_goal : term = ``
  \cursor_rel.
  !C8 C9 cursors stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8
    stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9 ev q9'.
    cursor_rel C8 C9 cursors
      (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
    joint_transition C9
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ev q9' ==>
    mem_corr inst8 s8 inst9 s9 /\ call_corr inst8 s8 inst9 s9 /\
    (inst_mem_ranges inst9 s9 <> [] /\ ~in_revert_forward fn9 s9 ==>
      ~in_revert_forward fn8 s8) /\
    ?cursors' q8'.
      ((q8' = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8 /\
        MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] /\
        inst9.inst_opcode <> GAS /\ inst9.inst_opcode <> INVOKE /\
        inst_mem_ranges inst9 s9 = []) \/
       ?ev8. joint_transition C8
         (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8') /\
      cursor_rel C8 C9 cursors' q8' q9'
``;

val focus_s7_frame_step_goal : term = ``
  \frame_rel.
  !rpolicy unit cpl prog vs0 es0 stk PG G tn fn inst s oms om hs h
    ast ev stk' PG' G' tn' fn' inst' t oms' om' hs' h'.
    joint_config_reachable vs0 unit.cu_context
      (JointConfig stk PG G tn fn inst s oms om hs h) /\
    frame_rel rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
    ~in_revert_forward fn s /\
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
      source_memory_reads_disjoint cpl inst s /\
      context_source_memory_writes_disjoint cpl inst s) /\
    joint_transition unit.cu_context
      (JointConfig stk PG G tn fn inst s oms om hs h) ev
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
    ?n ast'.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n ast = AsmOK ast' /\
      frame_rel rpolicy unit cpl prog vs0 es0
        (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast' /\
      (0 < n \/
       (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
        stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = SUC s.vs_inst_idx /\
        ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          LENGTH bb.bb_instructions - t.vs_inst_idx <
            LENGTH bb.bb_instructions - s.vs_inst_idx))
``;

val focus_s7_guard : term = ``
  \cpl q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
    ~in_revert_forward fn s /\
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
      source_memory_reads_disjoint cpl inst s /\
      context_source_memory_writes_disjoint cpl inst s)
``;

(* Every free name is intentional. A missing imported constant must fail
   this check rather than silently becoming a universally bound predicate. *)
val producer_parameters =
  ["rpolicy", "unit", "out", "vs0", "cpl", "prog", "es0", "nm",
   "entryfn", "lbl", "lo", "markf", "project", "result", "final"];

val _ =
  if type_of focus_producer_goal = type_of ``T`` andalso
     HOLset.equal
       (HOLset.fromList String.compare
          (map (fst o dest_var) (free_vars focus_producer_goal)),
        HOLset.fromList String.compare producer_parameters)
  then ()
  else raise Fail "focus producer goal has unexpected type or free names";

val _ =
  if null (free_vars focus_execution_motive) andalso
     type_of (snd (strip_abs focus_execution_motive)) = type_of ``T``
  then ()
  else raise Fail "focus execution motive is not a closed Boolean predicate";

val _ = app
  (fn tm =>
    if null (free_vars tm) andalso
       type_of (snd (strip_abs tm)) = type_of ``T``
    then ()
    else raise Fail "focus component interface has free names or a non-Boolean body")
  [focus_finalizer_prefix_bridge_goal, focus_joint_motive, focus_dft_packet_step_goal,
   focus_cfg_cursor_step_goal, focus_s7_frame_step_goal, focus_s7_guard];

val _ = app
  (fn (thy, name) =>
    if is_const (prim_mk_const {Thy = thy, Name = name}) then ()
    else raise Fail (thy ^ "$" ^ name ^ " is not a constant"))
  [("o1PipelineCorrect", "o1_pipeline"), ("o1SafeUpto", "o1_safe_upto"),
   ("gasEvents", "gas_events_blocks"),
   ("codegenEntryRel", "initial_ctx_rel_tail"),
   ("frameJointTrace", "joint_trace"),
   ("asmFrameRel", "asm_frame_rel_tail")];

(* This bound is uniform over values, not over an unbounded number of slots.
   The execution fold must still establish its bound on the slot count. *)
Theorem focus_mark_lengths_bounded:
  !(markf:bytes32 list -> bool list) max_raw.
    ?bound. !raw.
      LENGTH raw <= max_raw ==> LENGTH (markf (raw ++ [0w])) <= bound
Proof
  rpt gen_tac >>
  `FINITE {raw:bytes32 list | LENGTH raw <= max_raw}` by
    (mp_tac (Q.ISPECL [`UNIV:bytes32 set`, `max_raw:num`] FINITE_BOUNDED_LISTS) >>
     simp[]) >>
  qexists_tac `MAX_SET (IMAGE (\raw. LENGTH (markf (raw ++ [0w])))
    {raw:bytes32 list | LENGTH raw <= max_raw})` >>
  rpt strip_tac >> irule in_max_set >> simp[] >>
  qexists_tac `raw` >> simp[]
QED

(* A zero-assembly edge must spend rank; a positive edge can reset it.
   Costs are indexed by occurrences in this actual joint chain. *)
Theorem focus_joint_chain_length_bound:
  !evs q qs r costs.
    joint_chain ctx q evs qs r /\
    EVERY (\u. rank u <= bound) (q::qs) /\
    LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
      costs (ZIP (q::qs, qs)) ==>
    LENGTH evs <= (bound + 1) * SUM costs + rank q
Proof
  Induct_on `evs` >- simp[] >> rpt gen_tac >>
  Cases_on `qs` >- simp[joint_chain_def] >>
  Cases_on `costs` >- simp[] >>
  rename1 `joint_chain ctx q (_::evs) (next::rest_qs) r` >>
  rename1 `LIST_REL _ (cost::rest_costs) _` >>
  simp[joint_chain_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `!costs. _` (qspec_then `rest_costs` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `cost` >> fs[SUM, LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED

Theorem focus_frame_chain_progress:
  (!q ev next ast.
    joint_config_reachable vs0 ctx q /\ frame_rel q ast /\ guard q /\
    joint_transition ctx q ev next ==>
    ?cost mid.
      asm_steps lo o2pc prog cost ast = AsmOK mid /\ frame_rel next mid /\
      (0 < cost \/ rank next < rank q)) ==>
  !evs q qs r ast.
    joint_config_reachable vs0 ctx q /\ joint_chain ctx q evs qs r /\
    frame_rel q ast /\ EVERY guard (TAKE (LENGTH evs) (q::qs)) ==>
    ?costs final_ast.
      frame_rel r final_ast /\
      asm_steps lo o2pc prog (SUM costs) ast = AsmOK final_ast /\
      LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
        costs (ZIP (q::qs, qs))
Proof
  strip_tac >> Induct
  >- (rpt gen_tac >> Cases_on `qs` >> simp[joint_chain_def] >>
      rpt strip_tac >> qexistsl_tac [`[]`, `ast`] >> simp[asm_steps_def, ZIP_def]) >>
  rpt gen_tac >> Cases_on `qs` >- simp[joint_chain_def] >>
  rename1 `joint_chain ctx q (_::evs) (next::rest_qs) r` >>
  simp[joint_chain_def] >> rpt strip_tac >>
  qpat_x_assum `!q ev next ast. _ /\ _ /\ _ /\ joint_transition _ _ _ _ ==> _`
    drule_all >>
  disch_then (qx_choosel_then [`cost`, `mid`] strip_assume_tac) >>
  `joint_config_reachable vs0 ctx next` by
    metis_tac[joint_transition_reachable] >>
  qpat_x_assum `!q qs r ast. joint_config_reachable _ _ _ /\
    joint_chain _ _ _ _ _ /\ _ ==> _` drule_all >>
  disch_then (qx_choosel_then [`costs`, `final_ast`] strip_assume_tac) >>
  qexistsl_tac [`cost::costs`, `final_ast`] >> simp[] >>
  metis_tac[asm_steps_compose_ok]
QED

Theorem focus_s7_chain_progress:
  ^(focus_s7_frame_step_goal) frame_rel ==>
  !evs q qs r ast.
    joint_config_reachable vs0 unit.cu_context q /\
    joint_chain unit.cu_context q evs qs r /\
    frame_rel rpolicy unit cpl prog vs0 es0 q ast /\
    EVERY (^(focus_s7_guard) cpl) (TAKE (LENGTH evs) (q::qs)) ==>
    ?costs final_ast.
      frame_rel rpolicy unit cpl prog vs0 es0 r final_ast /\
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog (SUM costs) ast = AsmOK final_ast /\
      LIST_REL (\cost pair. 0 < cost \/
        ^(focus_block_rank) (SND pair) < ^(focus_block_rank) (FST pair))
        costs (ZIP (q::qs, qs))
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  ho_match_mp_tac focus_frame_chain_progress >>
  map_every qx_gen_tac [`q`, `ev`, `next`, `ast`] >>
  Cases_on `q` >> Cases_on `next` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!rpolicy unit cpl prog vs0 es0 stk PG G tn fn inst s oms om hs h
    ast ev stk' PG' G' tn' fn' inst' t oms' om' hs' h'. _` drule_all >>
  disch_then (qx_choosel_then [`cost`, `mid`] strip_assume_tac) >>
  qexistsl_tac [`cost`, `mid`] >> simp[] >>
  gvs[] >> simp[]
QED

Theorem focus_joint_block_rank_bound:
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  EVERY wf_function ctx.ctx_functions ==>
  ^(focus_block_rank) (JointConfig stk PG G tn fn inst s oms om hs h) <=
    SUM (MAP (\func. SUM (MAP (\bb. LENGTH bb.bb_instructions) func.fn_blocks))
      ctx.ctx_functions)
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by
    (fs[joint_config_reachable_def] >>
     drule joint_origin_history_projection >> strip_tac >>
     metis_tac[frame_history_cfg_invariant]) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `LENGTH bb.bb_instructions <= context_inst_count ctx` by
    metis_tac[context_inst_count_block] >>
  fs[context_inst_count_def] >> decide_tac
QED

Theorem focus_execution_initial:
  codegen_assembly rpolicy unit = SOME prog /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_initial vs0 unit.cu_context q0 /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ^(focus_execution_motive)
    vs0 unit.cu_context prog vs0.vs_data_section es0
    (entry_asm_state vs0 es0) result final tail
    q0 [] [] q0 0 (entry_asm_state vs0 es0) es0
Proof
  strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  `vs0.vs_call_ctx.cc_created_in_tx \/ account_already_created
    (lookup_account (FST (HD es0.contexts)).msgParams.callee
      es0.rollback.accounts)` by
    (gvs[initial_ctx_rel_tail_def, initial_ctx_rel_def] >> metis_tac[]) >>
  `asm_frame_rel_tail tail prog vs0.vs_data_section es0
    (entry_asm_state vs0 es0) es0` by
    metis_tac[asm_frame_rel_entry_tail] >>
  simp[joint_trace_def, joint_chain_def, asm_steps_def]
QED

(* The concrete fold must supply the cost bound from its same EVM run.
   This lemma only performs the finite frontier search over actual edges. *)
Theorem focus_bounded_frontier_stops:
  joint_initial vs0 ctx q0 /\ frontier q0 [] [] /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs /\
    ~stop q evs qs ==>
    ?ev next. joint_transition ctx q ev next /\
      frontier next (evs ++ [ev]) (qs ++ [next])) /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs ==>
    ?costs.
      EVERY (\u. rank u <= bound) (q0::qs) /\
      LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
        costs (ZIP (q0::qs, qs)) /\ SUM costs <= max_cost) ==>
  ?q evs qs. joint_trace vs0 ctx q0 evs qs q /\
    frontier q evs qs /\ stop q evs qs
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!n. ?q evs qs. joint_trace vs0 ctx q0 evs qs q /\
     frontier q evs qs /\ LENGTH evs = n` by
    (Induct
     >- (qexistsl_tac [`q0`, `[]`, `[]`] >>
         simp[joint_trace_def, joint_chain_def]) >>
     pop_assum (qx_choosel_then [`q`, `evs`, `qs`] strip_assume_tac) >>
     `~stop q evs qs` by metis_tac[] >>
     qpat_x_assum `!q evs qs. _ /\ _ /\ _ ==> _` drule_all >>
     disch_then (qx_choosel_then [`ev`, `next`] strip_assume_tac) >>
     qexistsl_tac [`next`, `evs ++ [ev]`, `qs ++ [next]`] >>
     simp[] >> metis_tac[joint_trace_snoc]) >>
  pop_assum (qspec_then `SUC ((bound + 1) * max_cost + rank q0)`
    (qx_choosel_then [`q`, `evs`, `qs`] strip_assume_tac)) >>
  qpat_x_assum `!q evs qs. _ ==> ?costs. _` drule_all >>
  disch_then (qx_choose_then `costs` strip_assume_tac) >>
  `LENGTH evs <= (bound + 1) * SUM costs + rank q0` by
    (irule focus_joint_chain_length_bound >>
     qexistsl_tac [`ctx`, `qs`, `q`] >>
     gvs[joint_trace_def]) >>
  `(bound + 1) * SUM costs <= (bound + 1) * max_cost` by
    simp[] >> decide_tac
QED
