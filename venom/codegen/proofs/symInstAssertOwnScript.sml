(* Assertion instruction composition, shared by canonical and own-code runs. *)
Theory symInstAssertOwn
Ancestors symInstPiecesFacts symInstPrefixOwn symEmitOwn symEmitSim
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim fnFrameDeepInst
  asmSymModeOwn

val assert_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", assert_bridge_core_tm);

Theorem sym_assertion_prepared_run_mode_core:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) localtop cs.as_stack /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) ==>
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `?w tail. localtop = Val w :: tail /\ w <> 0w` by
    (drule_all (SRULE [] (Q.INST
       [`ss` |-> `ss with sym_stack := localtop`, `srest` |-> `[]`]
       sym_assert_prepared_nonzero_core)) >> simp[]) >>
  `ss.sym_stack = Val w :: (tail ++ srest)` by simp[] >>
  `?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    full.sym_stack = DROP 1 ss.sym_stack` by
    (Cases_on `inst.inst_opcode = ASSERT` >> gvs[]
     >- (drule_all sym_assert_success_run_mode >> simp[] >> metis_tac[]) >>
     drule_all sym_assert_unreachable_success_run_mode >> simp[] >> metis_tac[]) >>
  `1 <= LENGTH ps.ps_stack` by simp[] >>
  qexists `full` >> simp[] >> irule sym_kinds_ok_release_dead_spills >>
  irule sym_emit_kinds_pop >> qexistsl [`1`, `ps`, `ss`] >> simp[]
QED

Theorem sym_assertion_prepared_run_own:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own lo p env own cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) ==>
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) localtop cs.as_stack` by
    gvs[asmSymBridgeTheory.asm_sym_rel_own_def] >>
  drule_all sym_assertion_prepared_run_mode_core >> simp[]
QED
