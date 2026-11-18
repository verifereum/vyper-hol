Theory staticAbortOptMergeIszeroOutside
Ancestors
  asmSplice asmSymPc asmSymSem asmSem symbolResolve list arithmetic

Theorem merge_iszero_outside_fetch_ok:
  !pre pat repl tail env u v.
    !r. r = splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ==>
    pat <> [] /\ LENGTH repl <= LENGTH pat /\
    (!l. ~MEM (AsmLabel l) pat /\ ~MEM (AsmLabel l) repl /\
         ~MEM (AsmDataHeader l) pat /\ ~MEM (AsmDataHeader l) repl) /\
    (u.sym_base.as_pc < LENGTH pre \/
     LENGTH pre + LENGTH pat <= u.sym_base.as_pc) /\
    sym_steps (pre ++ pat ++ tail) env 1 u = SymOK v ==>
    sym_steps (pre ++ repl ++ tail) env 1 (sym_with_pc (r u.sym_base.as_pc) u) =
      SymOK (sym_with_pc (r v.sym_base.as_pc) v)
Proof
  ntac 7 gen_tac >> CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.sym_base.as_pc < LENGTH (pre ++ pat ++ tail)` by
    (Cases_on `u.sym_base.as_pc < LENGTH (pre ++ pat ++ tail)` >>
     gvs[sym_steps_compute]) >>
  `sym_step (pre ++ pat ++ tail) env (EL u.sym_base.as_pc (pre ++ pat ++ tail)) u =
     SymOK v` by
    (qpat_x_assum `sym_steps _ _ 1 _ = _` mp_tac >>
     simp[sym_steps_compute, Excl "LENGTH_APPEND"] >> CASE_TAC >> simp[sym_steps_def]) >>
  qpat_x_assum `sym_steps _ _ 1 _ = _` kall_tac >>
  `splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) u.sym_base.as_pc <
     LENGTH (pre ++ repl ++ tail) /\
   EL (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) u.sym_base.as_pc)
     (pre ++ repl ++ tail) = EL u.sym_base.as_pc (pre ++ pat ++ tail)` by
    (irule splice_fetch >> simp[]) >>
  qabbrev_tac `r = splice_pc (LENGTH (pre:asm_inst list)) (LENGTH (pat:asm_inst list)) (LENGTH (repl:asm_inst list))` >>
  `(sym_with_pc (r u.sym_base.as_pc) u).sym_base.as_pc = r u.sym_base.as_pc`
    by simp[sym_with_pc_def] >>
  simp[sym_steps_compute] >>
  qmatch_asmsub_abbrev_tac `sym_step _ _ ins _ = SymOK v` >>
  `!d. sym_jump_dest (pre ++ repl ++ tail) d =
       OPTION_MAP r (sym_jump_dest (pre ++ pat ++ tail) d)` by
    (Cases >> simp[sym_jump_dest_def, Abbr `r`] >>
     rw[] >> irule (cj 1 splice_index_of_label) >> simp[]) >>
  `r (u.sym_base.as_pc + 1) = r u.sym_base.as_pc + 1` by
    (simp[Abbr `r`] >> irule (cj 1 splice_pc_next) >> Cases_on `pat` >> gvs[]) >>
  Cases_on `ins = AsmOp "JUMP"` >- suspend "jump" >>
  Cases_on `ins = AsmOp "JUMPI"` >- suspend "jumpi" >>
  suspend "linear"
QED

Resume merge_iszero_outside_fetch_ok[jump]:
  gvs[sym_step_def, sym_step_op_def, sym_jump_def, CaseEq "list", CaseEq "option"] >>
  simp[sym_jump_def, sym_with_pc_def]
QED

Resume merge_iszero_outside_fetch_ok[jumpi]:
  gvs[sym_step_def, sym_step_op_def, sym_jumpi_def, AllCaseEqs()] >>
  gvs[sym_set_stack_def, sym_with_pc_def, asm_next_def]
QED

Resume merge_iszero_outside_fetch_ok[linear]:
  `v.sym_base.as_pc = u.sym_base.as_pc + 1` by metis_tac[sym_step_pc_next] >>
  `r u.sym_base.as_pc <= u.sym_base.as_pc` by simp[Abbr `r`, splice_pc_def] >>
  `!x. sym_step (pre ++ repl ++ tail) env ins x =
       sym_step (pre ++ pat ++ tail) env ins x` by
    (gen_tac >> irule sym_step_prog_cong >> simp[]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `sym_step _ _ _ low` >>
  `sym_with_pc (low.sym_base.as_pc + (u.sym_base.as_pc - low.sym_base.as_pc)) low = u` by
    simp[Abbr `low`, sym_with_pc_def] >>
  qpat_assum `sym_with_pc _ low = u` (mp_tac o GSYM) >>
  disch_then (fn th =>
    qpat_assum `sym_step _ _ ins u = SymOK v` (mp_tac o ONCE_REWRITE_RULE [th])) >>
  simp[sym_step_pc_add] >>
  Cases_on `sym_step (pre ++ pat ++ tail) env ins low` >>
  simp[sym_result_pc_add_def] >> strip_tac >>
  drule_all sym_step_pc_next >> strip_tac >>
  gvs[Abbr `low`, sym_with_pc_def] >>
  qpat_assum `_.sym_base.as_pc = r _ + 1` (SUBST1_TAC o GSYM) >> simp[]
QED

Finalise merge_iszero_outside_fetch_ok
