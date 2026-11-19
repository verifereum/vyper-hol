(* A staged consuming interface for the checked prepared REVERT theorem. *)
Theory symControlPreparedTerminalOwn
Ancestors
  symControlForwardRunOwn
  asmSymBridge[qualified,ignore_grammar] codegenSymRel codegenSymOwnRel
  asmSymSem asmSymOwnCode asmSem codegenRel stackPlanTypes venomInst venomState

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val control_terminal_tm = let
  val premise = hd (strip_conj (fst (dest_imp (concl sym_revert_prepared_terminal_mode_conditional))))
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars premise) of
      [v] => v | _ => raise Fail ("missing terminal parameter " ^ n)
in list_mk_abs (map named ["allow_own", "prog", "env", "own", "lo", "code_ok"], premise) end;
val _ = Parse.temp_overload_on ("rf_T", control_terminal_tm);

Theorem sym_revert_prepared_terminal_forward_mode_conditional:
  asm_step lo (build_offset_to_pc prog) (AsmOp "REVERT") cs = AsmRevert out ==>
  bridge_core lo code_ok cs ss ==>
  rf_T allow_own prog env own lo code_ok ==>
  MEM fn ctx.ctx_functions ==> MEM inst (fn_insts fn) ==>
  inst.inst_opcode = REVERT ==> inst.inst_operands = [dop;zop] ==>
  opaque_use_ok fn ==>
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) ==>
  EVERY (\op. ~is_label_operand op) inst.inst_operands ==>
  plan_stack_rel lo current (tail ++ [zop;dop]) stk ==>
  operand_val current lo dop = SOME dst ==> operand_val current lo zop = SOME sz ==>
  cs.as_stack = stk ++ rest ==> asm_static_wf prog ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top ==>
  ss.sym_stack = top ++ srest ==>
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  asm_block_at prog cs.as_pc [AsmOp "REVERT"] ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  rpt disch_tac >>
  mp_tac sym_revert_prepared_terminal_mode_conditional >>
  asm_rewrite_tac[]
QED
