(* Relational restore schedules: the cell implementation is supplied once. *)
Theory symControlRestoreScheduleOwn
Ancestors
  codegenSymRel spillSim doSwapSim asmSpliceOwn planExec asmSem

Theorem sym_restore_bulk_from_cell:
  (!off sv cs ss.
    R cs ss /\ off < dimword(:256) /\
    asm_block_at p cs.as_pc (execute_plan fmp [SORestore off]) /\
    mem_sval_at ss.sym_mem_labels off sv /\
    (case sv of Val w => word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP off (asm_expand_memory (off + 32) cs.as_memory))) = w
      | Lab l d => T) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan fmp [SORestore off])) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own
        (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
      R cs' ss' /\ ss'.sym_stack = sv :: ss.sym_stack /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ cs'.as_pc = cs.as_pc + 2 /\
      cs'.as_memory = asm_expand_memory (off + 32) cs.as_memory) ==>
  !offsets vals cs ss.
    R cs ss /\ EVERY (\off. off < dimword(:256)) offsets /\
    LIST_REL (\off sv. mem_sval_at ss.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs.as_memory)) = w | Lab l d => T) offsets vals /\
    asm_block_at p cs.as_pc (execute_plan fmp (MAP SORestore offsets)) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p (2 * LENGTH offsets) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (2 * LENGTH offsets) ss = SymOK ss' /\
      R cs' ss' /\ ss'.sym_stack = REVERSE vals ++ ss.sym_stack /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\
      cs'.as_pc = cs.as_pc + 2 * LENGTH offsets
Proof
  strip_tac >> Induct
  >- simp[execute_plan_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
       asmSpliceOwnTheory.sym_steps_own_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `vals` >> gvs[] >>
  rename1 `mem_sval_at ss.sym_mem_labels h sv` >>
  `asm_block_at p cs.as_pc (execute_plan fmp [SORestore h]) /\
   asm_block_at p (cs.as_pc + 2) (execute_plan fmp (MAP SORestore offsets))` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  `case sv of Val w => word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP h (asm_expand_memory (h + 32) cs.as_memory))) = w
    | Lab l d => T` by simp[spillSimTheory.word_of_bytes_take_drop_expand] >>
  qpat_x_assum `!off sv cs ss. _` (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`t`, `cs'`, `ss'`] mp_tac) >>
  simp[spillSimTheory.word_of_bytes_take_drop_expand] >>
  strip_tac >> qexistsl [`cs''`, `ss''`] >> simp[] >>
  gvs[execute_plan_def, exec_stack_op_def] >> conj_tac
  >- (once_rewrite_tac[arithmeticTheory.MULT_SUC] >>
      irule blockSimHelpersTheory.asm_steps_compose_ok >> qexists `cs'` >> simp[]) >>
  mp_tac (Q.SPECL [`2`, `2 * LENGTH (offsets:num list)`, `ss`] sym_steps_mode_add) >>
  simp[arithmeticTheory.MULT_SUC]
QED
