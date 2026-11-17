(* Static-context aborts at supplied offsets, shared by symbolic modes. *)
Theory symControlAbortStaticOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] symControlTerminalSafetyOwn
  codegenSymRel codegenSymOwnRel symEmitSim symInstLogOwn
  fnFrameDeepAbort fnFrameTerminalAbort fnFrameTerminalPrep
  asmSymOwnCode asmSplice asmOpSim genBlockSim stackPlanGen stackPlanTypes
  planExec asmSem asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst

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
  `mid.as_call_ctx = vs.vs_call_ctx` by fs[venom_asm_rel_def, frame_view_def] >>
  `MEM (name,LENGTH vals)
    [("SSTORE",2); ("TSTORE",2); ("SELFDESTRUCT",1); ("CREATE",3);
     ("CREATE2",4); ("CALL",7)] /\
   LENGTH vals = asm_op_arity name /\
   (name = "CALL" ==> EL 2 vals <> 0w)` by
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
