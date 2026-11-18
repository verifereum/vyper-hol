(* Static-context aborts at supplied offsets, shared by symbolic modes. *)
Theory symControlAbortStaticOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] symControlTerminalSafetyOwn
  codegenSymRel codegenSymOwnRel symEmitSim symInstLogOwn
  fnFrameDeepAbort fnFrameTerminalAbort fnFrameTerminalPrep
  asmSymOwnCode asmSplice asmOpSim genBlockSim stackPlanGen stackPlanTypes
  planExec asmSem asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst symControlTerminalPrepareOwn

(* Parser-only abbreviations for the existing structural relations. *)
val static_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val static_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", static_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", static_bridge_result_tm);

Theorem sym_static_regular_arranged_terminal_mode_kernel:
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr) /\
  MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL] /\
  inst_wf inst /\ vs.vs_call_ctx.cc_static /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  asm_static_wf prog /\ venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL; CREATE; CREATE2]` by
    fs[listTheory.MEM] >>
  drule_all step_inst_static_abort >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnBlockBodyHelpersTheory.label_positions_ok_other >> gvs[listTheory.MEM]) >>
  `compute_operands inst = REVERSE inst.inst_operands /\
   (!op. MEM op (compute_operands inst) ==>
     MEM op inst.inst_operands /\ ~is_label_operand op) /\
   ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET; CODECOPY]` by
    (gvs[listTheory.MEM, compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, venomWfTheory.inst_wf_def,
         listTheory.LENGTH_EQ_NUM_compute] >>
     gvs[label_positions_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
    ?w. sv = Val w` by
    (rpt strip_tac >> irule ordinary_noncopy_operand_word_kind_mode >>
     qexistsl [`allow_own`, `ctx`, `fn`, `inst`, `op`, `ret`] >>
     fs[listTheory.EVERY_MEM, listTheory.MEM] >> metis_tac[]) >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME vals` by
    (`eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) =
      eval_operands inst.inst_operands vs` by
       (irule ordinary_selected_operands_frame_view >> simp[] >>
        qexists `inst` >> fs[listTheory.MEM]) >> simp[]) >>
  `!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  drule_all arranged_word_prepared_symbolic_stack_core >> strip_tac >>
  `LENGTH vals = LENGTH inst.inst_operands` by
    metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length] >>
  `mid.as_call_ctx = vs.vs_call_ctx /\ mid.as_outcomes = vs.vs_outcomes` by
    fs[venom_asm_rel_def, frame_view_def] >>
  `MEM (name,LENGTH vals)
    [("SSTORE",2); ("TSTORE",2); ("SELFDESTRUCT",1); ("CREATE",3);
     ("CREATE2",4); ("CALL",7)] /\
   LENGTH vals = asm_op_arity name /\
   (name = "CALL" ==> EL 2 vals <> 0w \/ mid.as_outcomes = [])` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def,
        venomWfTheory.inst_wf_def, asm_op_arity_def, asm_op_arity_table_def] >>
  `?out. asm_steps lo (build_offset_to_pc prog) prog 1
      (mid with as_stack := mid.as_stack ++ rest) = AsmFault out` by
    (drule_at (Pat `MEM (name, LENGTH vals) _`) static_write_fault_step >>
     disch_then (qspecl_then [`lo`, `build_offset_to_pc prog`, `prog`,
       `mid with as_stack := mid.as_stack ++ rest`,
       `DROP (LENGTH (compute_operands inst)) mid.as_stack ++ rest`, `vs`] mp_tac) >>
     simp[] >> impl_tac >- gvs[listTheory.APPEND_ASSOC] >> metis_tac[]) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp name)
     (mid with as_stack := mid.as_stack ++ rest) = AsmFault out` by
    (`mid.as_pc < LENGTH prog /\ EL mid.as_pc prog = AsmOp name` by
       (qpat_x_assum `asm_block_at _ _ [AsmOp name]` mp_tac >>
        simp_tac (srw_ss()) [asm_block_at_def,
          GSYM arithmeticTheory.ADD1, GSYM arithmeticTheory.LESS_EQ]) >>
     qspecl_then [`lo`, `build_offset_to_pc prog`, `prog`,
       `mid with as_stack := mid.as_stack ++ rest`] mp_tac asmOpSimTheory.asm_step_one >> simp[]) >>
  `!b. asm_op_mem_reads name vals b ==>
     source_memory_read_byte inst vs b \/
     (?rng. MEM rng (source_memory_write_ranges inst vs) /\
            byte_in_memory_range rng b)` by
    (rpt strip_tac >>
     Cases_on `MEM inst.inst_opcode [CALL; CREATE; CREATE2]`
     >- (irule memory_family_source_read_coverage >> metis_tac[listTheory.MEM]) >>
     gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def,
         asm_op_mem_reads_def, asmSemTheory.log_table_def]) >>
  `!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b` by
    fs[sym_kinds_ok_def] >>
  `~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name vals)` by
    (simp[mem_labels_hit_def] >>
     metis_tac[source_read_byte_no_labels, source_write_byte_no_labels]) >>
  `!msg. (if allow_own then sym_step_own prog env own (AsmOp name) ss
           else sym_step prog env (AsmOp name) ss) <> SymBad msg` by
    (`(if allow_own then sym_step_own prog env own (AsmOp name) ss
        else sym_step prog env (AsmOp name) ss) = sym_step_concrete name ss` by
       (qpat_x_assum `MEM (name,LENGTH vals) _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[listTheory.MEM] >> strip_tac >>
        Cases_on `allow_own` >>
        gvs[sym_step_own_def, sym_step_op_own_def, sym_step_def, sym_step_op_def,
            asmSemTheory.dup_table_def, asmSemTheory.swap_table_def]) >>
     simp[] >> metis_tac[sym_step_concrete_word_prefix_not_bad]) >>
  irule sym_terminal_step_transfer_mode_conditional >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`code_ok`, `AsmFault out`,
    `mid with as_stack := mid.as_stack ++ rest`, `AsmOp name`, `lo`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!cs ss ai cr. bridge_core lo code_ok cs ss /\ _ ==> _` mp_tac >> simp_tac (srw_ss()) []) >>
  metis_tac[]
QED

Theorem sym_static_log_arranged_terminal_mode_kernel:
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr) /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  LENGTH selected = w2n tc + 2 /\ w2n tc <= 4 /\
  vs.vs_call_ctx.cc_static /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ selected /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  source_memory_reads_disjoint cplan inst vs /\
  asm_static_wf prog /\
  asm_block_at prog mid.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule sym_log_name_dispatch >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnBlockBodyHelpersTheory.label_positions_ok_other >> simp[]) >>
  `!op. MEM op selected ==> MEM op inst.inst_operands /\ ~is_label_operand op` by
    fs[listTheory.EVERY_MEM] >>
  `LENGTH selected <= LENGTH ss.sym_stack /\
   EVERY (\sv. ?w. sv = Val w) (TAKE (LENGTH selected) ss.sym_stack)` by
    (irule ordinary_prepared_selected_numeric_mode >>
     qexistsl [`allow_own`, `cplan`, `ctx`, `fn`, `inst`, `arranged`, `tail`, `ret`, `srest`] >>
     simp[]) >>
  `eval_operands (REVERSE selected) vs = SOME (TAKE (LENGTH selected) mid.as_stack)` by
    (irule ordinary_prepared_source_evaluation >> simp[] >>
     qexistsl [`fn`, `inst`, `lo`, `m`, `arranged`, `ra`, `tail`] >>
     simp[venomMemPropsTheory.eval_operand_with_memory,
          genFrameSimTheory.operand_val_memory_update]) >>
  `LENGTH selected <= LENGTH mid.as_stack` by
    (drule fnFrameBoundaryInvokeTheory.eval_operands_some_length >>
     simp[listTheory.LENGTH_REVERSE] >>
     metis_tac[rich_listTheory.LENGTH_TAKE_LE]) >>
  `TAKE (LENGTH selected) (mid.as_stack ++ rest) =
   TAKE (LENGTH selected) mid.as_stack` by simp[rich_listTheory.TAKE_APPEND1] >>
  `?off len topics. REVERSE selected = off :: len :: topics` by
    (`2 <= LENGTH (REVERSE selected)` by simp[] >>
     Cases_on `REVERSE selected` >> gvs[] >>
     rename1 `REVERSE selected = h :: t` >> Cases_on `t` >> gvs[]) >>
  `MEM ("LOG" ++ num_to_dec_string (w2n tc))
    ["LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"]` by
    (qpat_x_assum `ALOOKUP log_table _ = SOME _` mp_tac >>
     simp[asmSemTheory.log_table_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b` by
    fs[sym_kinds_ok_def] >>
  `~mem_labels_hit ss.sym_mem_labels
     (asm_op_mem_reads ("LOG" ++ num_to_dec_string (w2n tc))
       (TAKE (LENGTH selected) mid.as_stack))` by
    (pure_rewrite_tac[mem_labels_hit_def] >>
     metis_tac[log_source_read_coverage, source_read_byte_no_labels]) >>
  `!msg. (if allow_own then sym_step_own prog env own
       (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) ss
     else sym_step prog env (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) ss) <> SymBad msg` by
    (`(if allow_own then sym_step_own prog env own
       (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) ss
       else sym_step prog env (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) ss) =
       sym_step_concrete ("LOG" ++ num_to_dec_string (w2n tc)) ss` by
       (qpat_x_assum `MEM _ ["LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"]` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[listTheory.MEM] >> strip_tac >>
        Cases_on `allow_own` >>
        gvs[sym_step_own_def, sym_step_op_own_def, sym_step_def, sym_step_op_def,
            asmSemTheory.dup_table_def, asmSemTheory.swap_table_def]) >>
     gen_tac >> pure_asm_rewrite_tac [] >>
     irule sym_step_concrete_numeric_safe_core >>
     qpat_assum `asm_op_arity _ = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `LENGTH selected = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`mid with as_stack := mid.as_stack ++ rest`, `lo`] >>
     simp_tac (srw_ss()) [] >> gvs[]) >>
  `mid.as_call_ctx = vs.vs_call_ctx /\ mid.as_outcomes = vs.vs_outcomes` by
    fs[venom_asm_rel_def, frame_view_def] >>
  qspecl_then [`lo`, `build_offset_to_pc prog`, `prog`, `mid with as_stack := mid.as_stack ++ rest`,
    `w2n tc`, `vs`] mp_tac static_log_fault_step >>
  (impl_tac >- (gvs[listTheory.LENGTH_APPEND] >>
    metis_tac[arithmeticTheory.LE_ADD, arithmeticTheory.LESS_EQ_TRANS])) >>
  strip_tac >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp ("LOG" ++ num_to_dec_string (w2n tc)))
     (mid with as_stack := mid.as_stack ++ rest) = AsmFault st'` by
    (`mid.as_pc < LENGTH prog /\
      EL mid.as_pc prog = AsmOp ("LOG" ++ num_to_dec_string (w2n tc))` by
       (qpat_x_assum `asm_block_at _ _ [AsmOp _]` mp_tac >>
        simp_tac (srw_ss()) [asm_block_at_def,
          GSYM arithmeticTheory.ADD1, GSYM arithmeticTheory.LESS_EQ]) >>
     qspecl_then [`lo`, `build_offset_to_pc prog`, `prog`, `mid with as_stack := mid.as_stack ++ rest`]
       mp_tac asmOpSimTheory.asm_step_one >> simp[]) >>
  irule sym_terminal_step_transfer_mode_conditional >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`code_ok`, `AsmFault st'`,
    `mid with as_stack := mid.as_stack ++ rest`,
    `AsmOp ("LOG" ++ num_to_dec_string (w2n tc))`, `lo`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!cs ss ai cr. bridge_core lo code_ok cs ss /\ _ ==> _` mp_tac >> simp_tac (srw_ss()) []) >>
  reverse conj_tac
  >- (qpat_x_assum `asm_block_at _ _ [AsmOp _]` mp_tac >> simp[]) >>
  qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Theorem sym_abort_static_regular_terminal_exists_mode_kernel:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr) /\
  o2pc = build_offset_to_pc prog /\
  MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL] /\
  vs.vs_call_ctx.cc_static /\ source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked spillbase ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
   generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final)` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[listTheory.MEM] >> rpt strip_tac >>
     gvs[venomEffectsTheory.is_commutative_def, generate_inst_plan_def,
        is_pre_codegen_opcode_def, is_param_opcode_def,
        is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
        is_unlowered_internal_call_opcode_def]) >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  drule_all sym_regular_abort_frame_prefix_deep_mode_conditional >> strip_tac >>
  `label_positions_ok inst` by
    (fs[fn_shape_ok_def, listTheory.EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_terminal (sym_steps_mode allow_own prog env own 1 ss_mid)` by
    (irule sym_static_regular_arranged_terminal_mode_kernel >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `venom_asm_terminal_rel _ _`)) >>
     qexistsl [`code_ok`, `name`,
       `stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack`] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qexists `m` >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  qexists `LENGTH (execute_plan cplan.cp_initial_fmp pre) + 1` >>
  simp[sym_steps_mode_add]
QED

Theorem sym_abort_static_log_terminal_exists_mode_kernel:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr) /\
  o2pc = build_offset_to_pc prog /\ inst.inst_opcode = LOG /\
  source_memory_reads_disjoint cplan inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked spillbase ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all step_inst_log_abort >> strip_tac >>
  `codegen_ready_inst inst` by metis_tac[codegen_ready_fn_inst] >>
  `?tc lops. inst.inst_operands = Lit tc :: lops /\
    LENGTH lops = w2n tc + 2 /\ w2n tc <= 4` by
    gvs[venomWfTheory.inst_wf_def, codegen_ready_inst_def] >>
  `compute_operands inst = lops` by simp[compute_operands_def] >>
  drule_all genBlockSimTheory.log_inst_plan_decompose >> strip_tac >>
  qpat_x_assum `compute_operands inst = lops`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `ps4.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   ps4.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by
    gvs[allocMonoTheory.release_dead_spills_spill_base,
        allocMonoTheory.release_dead_spills_next_offset] >>
  `LOG <> INVOKE /\ PERM lops lops /\
   LENGTH lops <= LENGTH ps1.ps_stack` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked_mode_conditional >>
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  pop_assum (qx_choose_then `mid` (qx_choose_then `ss_mid` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at prog mid.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]` by
    (qpat_x_assum `mid.as_pc = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
          stackOpSimTheory.asm_block_at_append]) >>
  `label_positions_ok inst` by
    (fs[fn_shape_ok_def, listTheory.EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `EVERY (\op. op <> dead_stack_marker) lops` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_terminal (sym_steps_mode allow_own prog env own 1 ss_mid)` by
    (irule sym_static_log_arranged_terminal_mode_kernel >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `venom_asm_terminal_rel _ _`)) >>
     goal_assum (drule_at (Pat `source_memory_reads_disjoint _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM fn ctx.ctx_functions`)) >>
     goal_assum (drule_at (Pat `inst.inst_operands = _`)) >>
     qexistsl [`code_ok`, `stack_pop (LENGTH lops) ps4.ps_stack`] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qexists `st.as_memory` >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  qexists `LENGTH (execute_plan cplan.cp_initial_fmp (input_ops ++ reorder_ops)) + 1` >>
  simp[sym_steps_mode_add]
QED
