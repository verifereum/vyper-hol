(* Terminal operand word prefixes, with independent source and bridge maps. *)
Theory symControlTerminalWordStackOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] symControlWordStackOwn
  symControlTerminalSafetyOwn codegenSymRel frameViewFacts genFrameSim
  fnFrameBoundaryInvoke stackPlanGen

(* Parser abbreviation only for the existing structural bridge interface. *)
val terminal_word_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", terminal_word_bridge_core_tm);

Theorem terminal_operands_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x
Proof
  strip_tac >> irule frameViewFactsTheory.ordinary_operand_not_retpc >>
  conj_tac >- gvs[listTheory.MEM] >>
  qexists `inst` >> gvs[compute_operands_def, listTheory.MEM]
QED

Theorem terminal_arranged_word_stack_mode_split_maps:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  bridge_core bridge_lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
  (mid.as_stack ++ rest = values ++
     DROP (LENGTH (compute_operands inst)) (mid.as_stack ++ rest)) /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `!x. MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x` by
    metis_tac[terminal_operands_not_retpc] >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME values` by
    metis_tac[frameViewFactsTheory.eval_operands_frame_view, listTheory.MEM_REVERSE] >>
  `!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
    ?w. sv = Val w` by
    (rpt strip_tac >>
     `op <> dead_stack_marker` by
       (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        disch_then (qspec_then `op` mp_tac) >> simp[]) >>
     drule_all terminal_operand_word_kind_mode >> simp[]) >>
  drule_all arranged_word_prepared_symbolic_stack_core_split_maps >> strip_tac >>
  `LENGTH values = LENGTH (compute_operands inst)` by
    metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length,
              listTheory.LENGTH_REVERSE] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.as_stack` by
    metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LE_ADD] >>
  `LENGTH (compute_operands inst) - LENGTH mid.as_stack = 0` by decide_tac >>
  simp[listTheory.DROP_APPEND] >>
  qpat_x_assum `mid.as_stack = values ++ _`
    (mp_tac o AP_TERM ``\xs:bytes32 list. xs ++ rest``) >>
  simp[listTheory.APPEND_ASSOC]
QED
