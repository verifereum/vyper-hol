(* Named instruction composition shared by canonical and relocated execution. *)
Theory symInstNamedOwn
Ancestors symInstPiecesFacts symInstPrefixOwn symEmitOwn symEmitDischargeOwn
  symEmitNamedOwn asmSymModeOwn asmSymForwardOwn asmSymOwnStep
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst

(* Syntax for the already existing structural bridge, not a new constant. *)
val named_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", named_bridge_core_tm);

Theorem sym_named_all_steps_suffix_mode:
  venom_to_evm_name opc = SOME name /\
  (opc = CODESIZE ==> allow_own) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 1
    (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> Cases_on `opc = CODESIZE`
  >- (gvs[asmIRTheory.venom_to_evm_name_def] >>
      `asm_block_at p (ss with sym_stack := ss.sym_stack ++ tail).sym_base.as_pc
         [AsmOp "CODESIZE"]` by simp[] >>
      imp_res_tac sym_steps_mode_single >>
      gvs[asmSymOwnCodeTheory.sym_step_own_def,
          asmSymOwnCodeTheory.sym_step_op_own_def,
          asmSymSemTheory.sym_set_stack_def,
          asmSymSemTheory.sym_state_component_equality]) >>
  drule_all named_suffix_dispatch_names >> strip_tac >>
  irule sym_named_steps_ok_stack_suffix_mode >> simp[] >>
  qexists_tac `name` >> gvs[listTheory.MEM]
QED

Theorem sym_named_restore_stack_core:
  venom_to_evm_name opc = SOME name /\
  (opc = CODESIZE ==> allow_own) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
  bridge_core lo code_ok cs' ss' /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  sym_kinds_ok cplan fn ret [] qs ss' ==>
  ?full. sym_steps_mode allow_own p env own 1
      (ss with sym_stack := ss.sym_stack ++ stail) = SymOK full /\
    bridge_core lo code_ok (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail qs full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bridge_core lo code_ok (cs' with as_stack := cs'.as_stack ++ wtail)
    (ss' with sym_stack := ss'.sym_stack ++ stail)` by
    (irule asm_sym_rel_restore_stack_core >> simp[] >> metis_tac[]) >>
  `sym_steps_mode allow_own p env own 1
     (ss with sym_stack := ss.sym_stack ++ stail) =
     SymOK (ss' with sym_stack := ss'.sym_stack ++ stail)` by
    (irule sym_named_all_steps_suffix_mode >> simp[] >> metis_tac[]) >>
  qexists_tac `ss' with sym_stack := ss'.sym_stack ++ stail` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  simp[sym_kinds_ok_restore_stack]
QED
