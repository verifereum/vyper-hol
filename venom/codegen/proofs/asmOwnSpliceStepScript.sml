(* Own-code instruction transport outside an optimizer splice window. *)
Theory asmOwnSpliceStep
Ancestors
  asmSymPcOwn asmSplice asmSymOwnCode asmSymPc asmSymSem asmSem
  finalizerContract

(* Relocation through zero works for deletions as well as insertions. *)
Theorem sym_step_own_from_zero[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" ==>
  sym_step_own p env own inst (sym_with_pc q ss) =
  sym_result_pc_add q (sym_step_own p env own inst (sym_with_pc 0 ss))
Proof
  strip_tac >>
  mp_tac (Q.INST [`ss` |-> `sym_with_pc 0 ss`, `n` |-> `q`]
    sym_step_own_pc_add) >>
  simp[sym_with_pc_def]
QED

Theorem sym_step_own_move_ok[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
  sym_step_own p env own inst ss = SymOK a ==>
  sym_step_own p env own inst (sym_with_pc q ss) =
    SymOK (sym_with_pc (q + 1) a)
Proof
  strip_tac >>
  drule_all sym_step_own_from_zero >>
  disch_then (qspecl_then [`ss`, `q`, `p`, `own`, `env`] assume_tac) >>
  drule_all sym_step_own_from_zero >>
  disch_then (qspecl_then [`ss`, `ss.sym_base.as_pc`, `p`, `own`, `env`] mp_tac) >>
  simp[sym_with_pc_def] >>
  Cases_on `sym_step_own p env own inst (sym_with_pc 0 ss)` >>
  gvs[sym_result_pc_add_def, sym_with_pc_def] >> strip_tac >> gvs[] >>
  drule_all sym_step_own_pc_next >> simp[sym_with_pc_def] >> strip_tac >> gvs[]
QED

Theorem sym_step_own_move_terminal[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
  sym_terminal (sym_step_own p env own inst ss) ==>
  sym_result_rel (sym_step_own p env own inst ss)
    (sym_step_own p env own inst (sym_with_pc q ss))
Proof
  strip_tac >>
  drule_all sym_step_own_from_zero >>
  disch_then (qspecl_then [`ss`, `q`, `p`, `own`, `env`] assume_tac) >>
  drule_all sym_step_own_from_zero >>
  disch_then (qspecl_then [`ss`, `ss.sym_base.as_pc`, `p`, `own`, `env`] mp_tac) >>
  simp[sym_with_pc_def] >> strip_tac >>
  Cases_on `sym_step_own p env own inst (sym_with_pc 0 ss)` >>
  gvs[sym_result_pc_add_def, sym_terminal_def, sym_with_pc_def,
      sym_result_rel_def, sym_obs_def]
QED

Theorem splice_inst_step_own_ok:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ pat ++ sfx))) /\
  sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss /\
  (ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
  sym_step_own (pfx ++ pat ++ sfx) env own inst ss = SymOK a ==>
  (a.sym_base.as_pc <= LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
  sym_step_own (pfx ++ repl ++ sfx) env own inst
    (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       ss.sym_base.as_pc) ss) =
    SymOK (sym_with_pc
      (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `pat <> [] /\ (!l. ~MEM (AsmLabel l) repl)` by fs[asm_splice_ok_def] >>
  Cases_on `inst = AsmOp "JUMP"`
  >- (gvs[sym_step_own_eq, sym_step_def, sym_step_op_def] >>
      drule_all splice_jump_ok >>
      disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc` mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  Cases_on `inst = AsmOp "JUMPI"`
  >- (gnvs[sym_step_own_eq, sym_step_def, sym_step_op_def] >>
      Cases_on `ss.sym_stack` >> gnvs[sym_jumpi_def] >>
      rename1 `ss.sym_stack = dest :: rest` >>
      Cases_on `rest` >> gnvs[sym_jumpi_def] >>
      rename1 `ss.sym_stack = dest :: cond :: stk` >>
      Cases_on `cond` >> gnvs[sym_jumpi_def] >>
      rename1 `Val c` >> Cases_on `c = 0w`
      >- (gvs[] >>
          irule (SRULE [arithmeticTheory.ADD_COMM] splice_fallthrough_ok) >>
          simp[] >> metis_tac[]) >>
      `sym_jump (pfx ++ pat ++ sfx) (ss with sym_stack := dest :: stk) = SymOK a`
        by (gvs[sym_jump_def, sym_jumpi_def, AllCaseEqs()]) >>
      `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx))
         (ss with sym_stack := dest :: stk)`
        by (fs[sym_state_labels_in_def] >> metis_tac[listTheory.MEM]) >>
      drule_all splice_jump_ok >>
      disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc` mp_tac) >>
      gvs[sym_jump_def, sym_jumpi_def, sym_with_pc_def, AllCaseEqs()]) >>
  `0 < LENGTH pat` by (Cases_on `pat` >> gvs[]) >>
  `a.sym_base.as_pc = ss.sym_base.as_pc + 1` by metis_tac[sym_step_own_pc_next] >>
  drule splice_pc_next >>
  disch_then (qspecl_then [`LENGTH repl`, `LENGTH pfx`, `ss.sym_base.as_pc`] mp_tac) >>
  simp[] >> strip_tac >>
  `!x. sym_step_own (pfx ++ repl ++ sfx) env own inst x =
       sym_step_own (pfx ++ pat ++ sfx) env own inst x`
    by (gen_tac >> irule sym_step_own_prog_cong >> simp[splice_headers]) >>
  simp[] >> drule_all sym_step_own_move_ok >>
  disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
    ss.sym_base.as_pc` mp_tac) >> gvs[]
QED

Theorem splice_inst_step_own_terminal:
  asm_splice_ok pat repl /\
  sym_terminal (sym_step_own (pfx ++ pat ++ sfx) env own inst ss) ==>
  sym_result_rel (sym_step_own (pfx ++ pat ++ sfx) env own inst ss)
    (sym_step_own (pfx ++ repl ++ sfx) env own inst (sym_with_pc q ss))
Proof
  strip_tac >>
  `inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI"`
    by (conj_tac >> strip_tac >>
        gvs[sym_step_own_eq, sym_step_def, sym_step_op_def, sym_jumps_not_terminal]) >>
  `!x. sym_step_own (pfx ++ repl ++ sfx) env own inst x =
       sym_step_own (pfx ++ pat ++ sfx) env own inst x`
    by (gen_tac >> irule sym_step_own_prog_cong >> simp[splice_headers]) >>
  simp[] >> irule sym_step_own_move_terminal >> simp[]
QED
