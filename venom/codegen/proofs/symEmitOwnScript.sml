(* Discharged relocated/own emission interfaces and stack restoration. *)
Theory symEmitOwn
Ancestors symEmitDischargeOwn symEmitSourceOwn symEmitSim symEmitFrameOwn asmSymForwardOwn asmSymOwnStep
  fnPlanPlaceRevertPostamble asmSymBridge codegenSymRel list

Theorem sym_emit_restore_stack_mode:
  sym_steps_mode allow_own p env own n (ss with sym_stack := ss.sym_stack ++ stail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ stail) /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail /\
  asm_sym_rel_own lo p env own cs' ss' /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  sym_kinds_ok cplan fn ret [] qs ss' ==>
  ?full. sym_steps_mode allow_own p env own n
      (ss with sym_stack := ss.sym_stack ++ stail) = SymOK full /\
    asm_sym_rel_own lo p env own (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail qs full
Proof
  strip_tac >> qexists_tac `ss' with sym_stack := ss'.sym_stack ++ stail` >>
  simp[asm_sym_rel_restore_stack_own, sym_kinds_ok_restore_stack]
QED

Theorem sym_named_emit_restore_stack_mode:
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  ~MEM name ["POP"; "JUMP"; "JUMPI"; "CODESIZE"] /\
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
  asm_sym_rel_own lo p env own cs' ss' /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  sym_kinds_ok cplan fn ret [] qs ss' ==>
  ?full. sym_steps_mode allow_own p env own 1
      (ss with sym_stack := ss.sym_stack ++ stail) = SymOK full /\
    asm_sym_rel_own lo p env own (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail qs full
Proof
  strip_tac >> irule sym_emit_restore_stack_mode >> simp[] >>
  qexists_tac `ss'` >> simp[] >>
  irule sym_named_steps_ok_stack_suffix_mode >> simp[] >>
  qexists_tac `name` >> gvs[MEM]
QED

Theorem sym_assert_steps_ok_stack_suffix_mode:
  ss.sym_stack = Val w :: stk /\ w <> 0w /\
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
  sym_steps_mode allow_own p env own 3 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 3 (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> drule_all sym_assert_success_run_mode >> strip_tac >> gvs[] >>
  qspecl_then [`ss with sym_stack := Val w :: (stk ++ tail)`, `stk ++ tail`] mp_tac
    (Q.GENL [`ss`, `tail`] sym_assert_success_run_mode) >> simp[]
QED

Theorem sym_assert_unreachable_steps_ok_stack_suffix_mode:
  ss.sym_stack = Val w :: stk /\ w <> 0w /\
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
  INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3) /\
  sym_steps_mode allow_own p env own 3 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 3 (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> drule_all sym_assert_unreachable_success_run_mode >> strip_tac >> gvs[] >>
  qspecl_then [`ss with sym_stack := Val w :: (stk ++ tail)`, `stk ++ tail`] mp_tac
    (Q.GENL [`ss`, `tail`] sym_assert_unreachable_success_run_mode) >> simp[]
QED

Theorem sym_bump_steps_ok_stack_suffix_mode:
  ss.sym_stack = Val delta :: Val fmp :: stk /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] /\
  sym_steps_mode allow_own p env own 2 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 2 (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> drule_all sym_bump_success_run_mode >> strip_tac >> gvs[] >>
  qspecl_then [`ss with sym_stack := Val delta :: Val fmp :: (stk ++ tail)`,
               `stk ++ tail`] mp_tac
    (Q.GENL [`ss`, `tail`] sym_bump_success_run_mode) >> simp[]
QED

Theorem sym_istore_steps_ok_stack_suffix_mode:
  ss.sym_stack = Val value :: Val off :: stk /\
  (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n off) 32 b) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] /\
  sym_steps_mode allow_own p env own 2 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 2 (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> drule_all sym_istore_success_run_mode >> strip_tac >> gvs[] >>
  qspecl_then [`ss with sym_stack := Val value :: Val off :: (stk ++ tail)`,
               `stk ++ tail`] mp_tac
    (Q.GENL [`ss`, `tail`] sym_istore_success_run_mode) >> simp[]
QED

Theorem sym_initial_fmp_steps_ok_stack_suffix_mode:
  asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes initial_fmp)] /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 1 (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> drule_all sym_initial_fmp_run_mode >> strip_tac >> gvs[] >>
  qspec_then `ss with sym_stack := ss.sym_stack ++ tail` mp_tac
    (Q.GEN `ss` sym_initial_fmp_run_mode) >> simp[]
QED
