(* Shared terminal safety at supplied offsets, for either symbolic mode. *)
Theory symControlTerminalSafetyOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel codegenSymOwnRel
  symControlWordStackOwn symFrameControlFacts asmSymOwnCode asmSplice frameRel contextCodegenRel
  unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem asmSymSem
  venomExecSemantics venomInst venomState frameViewFacts genFrameSim emitSim fnFrameBoundaryInvoke
  symEmitSim

(* Parser abbreviations for the existing structural bridge interfaces. *)
val terminal_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val terminal_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", terminal_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", terminal_bridge_result_tm);

Theorem source_memory_range_label_free:
  !cp labs inst vs off sz.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  MEM (off,sz) (source_memory_read_ranges inst vs) ==>
  ~mem_labels_hit labs (in_mem_range off sz)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[mem_labels_hit_def, in_mem_range_def] >>
  rename1 `source_memory_reads_disjoint cplan inst vs` >>
  rename1 `byte IN FDOM labs` >>
  `context_spill_byte cplan byte` by metis_tac[] >>
  fs[context_spill_byte_def, source_memory_reads_disjoint_def,
     listTheory.EVERY_MEM] >>
  first_x_assum (qspec_then `(off,sz)` mp_tac) >> simp[] >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem terminal_source_memory_reads_safe:
  !cp.
  MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
    CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\ inst_wf inst /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs ==>
  ~mem_labels_hit labs (asm_op_mem_reads name args)
Proof
  gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL]`
  >- (`MEM inst.inst_opcode [ILOAD; MLOAD; SHA3; MSTORE; MSTORE8; MCOPY;
         CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
         CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by gvs[listTheory.MEM] >>
      `!b. asm_op_mem_reads name args b ==>
        source_memory_read_byte inst vs b \/
        (?rng. MEM rng (source_memory_write_ranges inst vs) /\ byte_in_memory_range rng b)` by
        metis_tac[memory_family_source_read_coverage] >>
      simp[mem_labels_hit_def] >>
      metis_tac[source_read_byte_no_labels, source_write_byte_no_labels]) >>
  fs[listTheory.MEM] >>
  gvs[venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def,
      asm_op_mem_reads_def, asmSemTheory.log_table_def, mem_labels_hit_def,
      listTheory.LENGTH_EQ_NUM_compute, eval_operands_def, AllCaseEqs()] >>
  irule (SRULE [mem_labels_hit_def] source_memory_range_label_free) >>
  goal_assum (drule_at (Pat `source_memory_reads_disjoint _ _ _`)) >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def]
QED

Theorem mem_labels_clear_read_safe:
  ~mem_labels_hit (mem_labels_clear labs P) P
Proof
  simp[mem_labels_hit_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT] >>
  metis_tac[]
QED

Theorem sym_steps_terminal_extend_mode:
  sym_terminal (sym_steps_mode allow_own p env own n ss) ==>
  sym_steps_mode allow_own p env own (n + k) ss =
    sym_steps_mode allow_own p env own n ss
Proof
  simp[sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own p env own n ss` >> simp[sym_terminal_def]
QED

Theorem sym_step_concrete_word_prefix:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss =
    sym_lift (LENGTH args)
      (mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)) ss
      (asm_step_op FEMPTY name (ss.sym_base with as_stack := args))
Proof
  strip_tac >>
  `OPT_MMAP sval_val (MAP Val args) = SOME args` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `args` >> simp[sval_val_def]) >>
  `TAKE (asm_op_arity name) ss.sym_stack = MAP Val args` by
    (qpat_x_assum `LENGTH args = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[rich_listTheory.TAKE_APPEND]) >>
  simp[sym_step_concrete_def]
QED

Theorem sym_step_concrete_word_prefix_not_bad:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss <> SymBad e
Proof
  strip_tac >> drule_all sym_step_concrete_word_prefix >> disch_then SUBST1_TAC >>
  Cases_on `asm_step_op FEMPTY name (ss.sym_base with as_stack := args)` >>
  simp[sym_lift_def]
QED

Theorem bridge_result_terminal:
  bridge_result R sr cr /\ (!e. sr <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal sr
Proof
  Cases_on `sr` >> Cases_on `cr` >> simp[sym_terminal_def]
QED

Theorem sym_terminal_opcode_concrete:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] ==>
  sym_step_op p env name ss = sym_step_concrete name ss
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[sym_step_op_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def]
QED

Theorem sym_terminal_opcode_mode:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] ==>
  (if allow_own then sym_step_own p env own (AsmOp name) ss
   else sym_step p env (AsmOp name) ss) = sym_step_concrete name ss
Proof
  strip_tac >> Cases_on `allow_own` >>
  gvs[listTheory.MEM, sym_step_own_def, sym_step_op_own_def,
      sym_step_def, sym_terminal_opcode_concrete]
QED

Theorem sym_terminal_step_runs_mode:
  asm_block_at p ss.sym_base.as_pc [inst] ==>
  sym_steps_mode allow_own p env own 1 ss =
    (if allow_own then sym_step_own p env own inst ss
     else sym_step p env inst ss)
Proof
  metis_tac[sym_steps_mode_single]
QED

Theorem sym_terminal_opcode_safe_mode:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  !e. (if allow_own then sym_step_own p env own (AsmOp name) ss
       else sym_step p env (AsmOp name) ss) <> SymBad e
Proof
  metis_tac[sym_terminal_opcode_mode, sym_step_concrete_word_prefix_not_bad]
QED

Theorem sym_terminal_step_transfer_mode_conditional:
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc p) ai cs = cr /\
    (!e. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own p env own ai ss else sym_step p env ai ss) cr) /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step lo (build_offset_to_pc p) inst cs = cr /\
  (!e. (if allow_own then sym_step_own p env own inst ss
        else sym_step p env inst ss) <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps_mode allow_own p env own 1 ss)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc [inst]` by simp[] >>
  `sym_steps_mode allow_own p env own 1 ss =
    (if allow_own then sym_step_own p env own inst ss
     else sym_step p env inst ss)` by
    (irule sym_terminal_step_runs_mode >> asm_rewrite_tac[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!cs ss ai cr. _` (drule_all_then assume_tac) >>
  drule_all bridge_result_terminal >> simp[]
QED

Theorem sym_terminal_opcode_transfer_mode_conditional:
  (!cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc p) ai cs = cr /\
    (!e. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own p env own ai ss else sym_step p env ai ss) cr) /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  asm_step lo (build_offset_to_pc p) (AsmOp name) cs = cr /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps_mode allow_own p env own 1 ss)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all sym_terminal_opcode_safe_mode >>
  disch_then (qspecl_then [`p`, `own`, `env`, `allow_own`] assume_tac) >>
  irule sym_terminal_step_transfer_mode_conditional >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl [`code_ok`, `cr`, `cs`, `AsmOp name`, `lo`] >>
  asm_rewrite_tac[]
QED

Theorem label_flow_noncopy_operand_not_code_end_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> CODECOPY /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  Cases_on `allow_own` >> simp[] >> strip_tac >>
  fs[label_flow_ok_def, label_flow_own_ok_def] >>
  first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ordinary_noncopy_operand_word_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >> Cases_on `op` >>
  gvs[op_kind_ok_def, is_label_operand_def] >>
  drule_all frameViewFactsTheory.ordinary_operand_not_retpc >>
  drule_all label_flow_noncopy_operand_not_code_end_mode >> metis_tac[]
QED

Theorem terminal_operand_word_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  MEM op (compute_operands inst) /\ op <> dead_stack_marker /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  `MEM op inst.inst_operands /\ ~is_label_operand op /\
   inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
   inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
   inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY` by
    (gvs[listTheory.MEM, compute_operands_def] >>
     gvs[label_positions_ok_def, listTheory.EVERY_MEM]) >>
  drule_all ordinary_noncopy_operand_word_kind_mode >> simp[]
QED

Theorem arranged_word_prepared_symbolic_stack_core:
  venom_asm_rel lo ps vs mid /\ ps.ps_stack = tail ++ operands /\
  EVERY (\op. op <> dead_stack_marker) operands /\
  (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
  eval_operands (REVERSE operands) vs = SOME values /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) ==>
  mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  ACCEPT_TAC (symControlWordStackOwnTheory.arranged_word_prepared_symbolic_stack_core_split_maps
    |> Q.INST [`bridge_lo` |-> `lo`])
QED
