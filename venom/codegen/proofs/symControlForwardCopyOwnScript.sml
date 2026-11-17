(* Forwarded return-data copy, at supplied offsets and in either mode.
   The preparation run is supplied by the independent preparation subject. *)
Theory symControlForwardCopyOwn
Ancestors
  asmSymBridge codegenSymRel codegenSymOwnRel symEmitSim
  fnFrameStepsRevertForward emitSim frameViewFacts
  stackPlanGen stackPlanTypes planExec asmSem asmSymSem frameRel
  contextCodegenRel unitShapeDefs dfgDefs asmSplice asmSpliceOwn asmSymOwnCode

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem sym_step_concrete_clears_written_labels:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  sym_step_concrete name ss = SymOK ss' ==>
  ss'.sym_mem_labels =
    mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)
Proof
  strip_tac >>
  `OPT_MMAP sval_val (MAP Val args) = SOME args` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `args` >> simp[sval_val_def]) >>
  `TAKE (asm_op_arity name) ss.sym_stack = MAP Val args` by
    (qpat_x_assum `LENGTH args = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[rich_listTheory.TAKE_APPEND]) >>
  gvs[sym_step_concrete_def] >>
  Cases_on `asm_step_op FEMPTY name (ss.sym_base with as_stack := args)` >>
  gvs[sym_lift_def]
QED

Theorem sym_returndatacopy_concrete:
  sym_step p env (AsmOp "RETURNDATACOPY") ss =
    sym_step_concrete "RETURNDATACOPY" ss
Proof
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def]
QED

Theorem sym_returndatacopy_mode_single:
  asm_block_at p ss.sym_base.as_pc [AsmOp "RETURNDATACOPY"] ==>
  sym_steps_mode allow_own p env own 1 ss =
    sym_step p env (AsmOp "RETURNDATACOPY") ss
Proof
  strip_tac >> drule sym_steps_mode_single >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] mp_tac) >>
  simp[sym_step_own_def, sym_step_op_own_def, sym_step_def]
QED

Theorem sym_returndatacopy_clears_range:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  strip_tac >>
  `ss'.sym_mem_labels = mem_labels_clear ss.sym_mem_labels
      (asm_op_mem_writes "RETURNDATACOPY" [dst;src;sz])` by
    (irule sym_step_concrete_clears_written_labels >>
     gvs[sym_returndatacopy_concrete, asm_op_arity_def,
         asm_op_arity_table_def, asm_op_mem_reads_def, log_table_def,
         asm_op_mem_writes_def, mem_labels_hit_def]) >>
  simp[asm_op_mem_writes_def, mem_labels_clear_def, mem_labels_hit_def,
    finite_mapTheory.FDOM_DRESTRICT] >> metis_tac[]
QED

Theorem asm_sym_step_rel_ok_core:
  bridge_result R sr (AsmOK cs') /\ (!e. sr <> SymBad e) ==>
  ?ss'. sr = SymOK ss' /\ R cs' ss'
Proof
  Cases_on `sr` >> simp[]
QED

Theorem sym_ok_step_transfer_mode_conditional:
  (!cs ss. bridge_core lo code_ok cs ss ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own p env own inst ss
       else sym_step p env inst ss)
      (asm_step lo (build_offset_to_pc p) inst cs)) /\
  bridge_core lo code_ok cs ss /\ asm_block_at p cs.as_pc [inst] /\
  asm_step lo (build_offset_to_pc p) inst cs = AsmOK cs' /\
  (!e. (if allow_own then sym_step_own p env own inst ss
         else sym_step p env inst ss) <> SymBad e) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss'
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc [inst]` by simp[] >>
  drule sym_steps_mode_single >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  qpat_x_assum `!cs ss. _` (drule_all_then mp_tac) >>
  Cases_on `if allow_own then sym_step_own p env own inst ss
    else sym_step p env inst ss` >> gvs[] >> metis_tac[]
QED

Theorem sym_returndatacopy_success_inventory:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ss'.sym_stack = tail /\
  (!b. b IN FDOM ss'.sym_mem_labels ==> b IN FDOM ss.sym_mem_labels)
Proof
  strip_tac >>
  `sym_step_concrete "RETURNDATACOPY" ss = SymOK ss'` by
    gvs[sym_returndatacopy_concrete] >>
  gvs[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
      sval_val_def, asm_op_mem_reads_def, log_table_def, mem_labels_hit_def] >>
  gvs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
      asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
      asm_step_extcall_def, asm_step_copy_def, asm_returndatacopy_def] >>
  Cases_on `LENGTH ss.sym_base.as_returndata < w2n src + w2n sz` >>
  Cases_on `sz = 0w` >>
  gvs[sym_lift_def, asm_next_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_returndatacopy_not_bad:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail ==>
  !e. sym_step p env (AsmOp "RETURNDATACOPY") ss <> SymBad e
Proof
  simp[sym_returndatacopy_concrete, sym_step_concrete_def,
    asm_op_arity_def, asm_op_arity_table_def, sval_val_def,
    asm_op_mem_reads_def, log_table_def, mem_labels_hit_def] >>
  strip_tac >>
  Cases_on `asm_step_op FEMPTY "RETURNDATACOPY"
    (ss.sym_base with as_stack := [dst;src;sz])` >> simp[sym_lift_def]
QED

Theorem sym_returndatacopy_success_transfer_core:
  bridge_core lo code_ok cs ss /\
  asm_block_at p cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  asm_step lo (build_offset_to_pc p) (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss'. sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all sym_step_returndatacopy_sim_core >>
  disch_then (qspec_then `build_offset_to_pc p` mp_tac) >>
  `!e. sym_step p env (AsmOp "RETURNDATACOPY") ss <> SymBad e` by
    metis_tac[sym_returndatacopy_not_bad] >>
  Cases_on `sym_step_concrete "RETURNDATACOPY" ss` >>
  gvs[asm_step_def, sym_returndatacopy_concrete] >>
  metis_tac[sym_returndatacopy_clears_range, sym_returndatacopy_concrete]
QED

Theorem sym_rf_copy_operand_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `!x. MEM (Var x) inst.inst_operands ==> ~code_end_var fn x` by
    (qpat_x_assum `label_flow_own_ok ctx`
       (mp_tac o REWRITE_RULE [label_flow_own_ok_def]) >>
     disch_then (qspecl_then [`fn`, `inst`] mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `op` >> gvs[op_kind_ok_def, is_label_operand_def] >>
  `~retpc_var fn s` by
    (irule frameViewFactsTheory.ordinary_operand_not_retpc >>
     simp[] >> qexists `inst` >> simp[]) >> gvs[]
QED

Theorem sym_rf_copy_prepared_stack_core:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  bridge_core lo code_ok cs ss /\ cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;src;sz] ++ suffix
Proof
  strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  rename1 `op_kind_ok fn ret dop sd` >>
  rename1 `op_kind_ok fn ret sop sr` >>
  rename1 `op_kind_ok fn ret zop szv` >>
  `(?w. sd = Val w) /\ (?w. sr = Val w) /\ (?w. szv = Val w)` by
    (rpt conj_tac >> irule sym_rf_copy_operand_kind_mode >> metis_tac[listTheory.MEM]) >>
  gvs[sval_conc_def]
QED

Theorem sym_rf_copy_success_stack_core:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  bridge_core lo code_ok cs ss /\ cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_step prog env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all sym_rf_copy_prepared_stack_core >> strip_tac >>
  `ss.sym_stack = Val dst :: Val src :: Val sz :: suffix` by simp[] >>
  drule_all sym_returndatacopy_success_transfer_core >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all sym_returndatacopy_success_inventory >> strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  metis_tac[listTheory.CONS_11, listTheory.APPEND]
QED

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem sym_rf_copy_prepared_success_mode_core:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel lo current (tail ++ [zop;sop;dop]) stk /\
  operand_val current lo dop = SOME dst /\
  operand_val current lo sop = SOME src /\
  operand_val current lo zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ bridge_core lo code_ok cs ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_steps_mode allow_own prog env own 1 ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?d s z residual. stk = d :: s :: z :: residual /\
    operand_val current lo dop = SOME d /\
    operand_val current lo sop = SOME s /\
    operand_val current lo zop = SOME z` by
    (irule asm_stack_top3_from_plan >> simp[] >> qexists `tail` >> simp[]) >>
  `cs.as_stack = dst :: src :: sz :: (residual ++ rest)` by
    metis_tac[optionTheory.SOME_11, listTheory.APPEND] >>
  drule_all sym_rf_copy_success_stack_core >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    (qpat_x_assum `?m. ss.sym_base = _ /\ _` strip_assume_tac >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc [AsmOp "RETURNDATACOPY"]` by simp[] >>
  drule sym_returndatacopy_mode_single >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  metis_tac[]
QED

Theorem sym_rf_copy_fault_stack_mode_core:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  bridge_core lo code_ok cs ss /\
  cs.as_stack = dst :: src :: sz :: rest /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") cs = AsmFault cs' ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all sym_rf_copy_prepared_stack_core >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by
    (qpat_x_assum `?m. ss.sym_base = _ /\ _` strip_assume_tac >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc [AsmOp "RETURNDATACOPY"]` by simp[] >>
  drule sym_returndatacopy_mode_single >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  `ss.sym_stack = Val dst :: Val src :: Val sz :: suffix` by simp[] >>
  `!e. sym_step_concrete "RETURNDATACOPY" ss <> SymBad e` by
    (rewrite_tac[GSYM sym_returndatacopy_concrete] >>
     irule sym_returndatacopy_not_bad >> simp[]) >>
  drule_all sym_step_returndatacopy_sim_core >>
  disch_then (qspec_then `build_offset_to_pc prog` mp_tac) >>
  Cases_on `sym_step_concrete "RETURNDATACOPY" ss` >>
  gvs[asm_step_def, sym_returndatacopy_concrete, sym_terminal_def]
QED
