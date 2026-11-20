Theory staticAbortOptMergeIszeroOutside
Ancestors
  asmSymPcOwn codegenSymRel
  staticAbortProtectedTraceCoverage staticAbortProtectedStepControl asmSymOwnCode
  asmSplice asmSymPc asmSymSem asmSem symbolResolve list arithmetic

Theorem merge_iszero_outside_fetch_ok_mode:
  !pre pat repl tail env u v.
    !r. r = splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ==>
    pat <> [] /\ LENGTH repl <= LENGTH pat /\
    (!l. ~MEM (AsmLabel l) pat /\ ~MEM (AsmLabel l) repl /\
         ~MEM (AsmDataHeader l) pat /\ ~MEM (AsmDataHeader l) repl) /\
    (u.sym_base.as_pc < LENGTH pre \/
     LENGTH pre + LENGTH pat <= u.sym_base.as_pc) /\
    sym_steps_mode allow_own (pre ++ pat ++ tail) env own 1 u = SymOK v ==>
    sym_steps_mode allow_own (pre ++ repl ++ tail) env own 1 (sym_with_pc (r u.sym_base.as_pc) u) =
      SymOK (sym_with_pc (r v.sym_base.as_pc) v)
Proof
  ntac 7 gen_tac >> CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `sym_steps_mode _ _ _ _ 1 _ = _`
    (strip_assume_tac o REWRITE_RULE [sym_steps_mode_ok_one]) >>
  `splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) u.sym_base.as_pc <
     LENGTH (pre ++ repl ++ tail) /\
   EL (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) u.sym_base.as_pc)
     (pre ++ repl ++ tail) = EL u.sym_base.as_pc (pre ++ pat ++ tail)` by
    (irule splice_fetch >> simp[]) >>
  qabbrev_tac `r = splice_pc (LENGTH (pre:asm_inst list)) (LENGTH (pat:asm_inst list)) (LENGTH (repl:asm_inst list))` >>
  `r u.sym_base.as_pc < LENGTH (pre ++ repl ++ tail) /\
    EL (r u.sym_base.as_pc) (pre ++ repl ++ tail) = EL u.sym_base.as_pc (pre ++ pat ++ tail)`
    by simp[Abbr `r`] >>
  `(sym_with_pc (r u.sym_base.as_pc) u).sym_base.as_pc = r u.sym_base.as_pc`
    by simp[sym_with_pc_def] >>
  simp[sym_steps_mode_ok_one] >>
  qabbrev_tac `ins = EL u.sym_base.as_pc (pre ++ pat ++ tail)` >>
  qpat_assum `Abbrev (ins = _)`
    (fn th => pure_rewrite_tac [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] >>
              rule_assum_tac (PURE_REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
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

Resume merge_iszero_outside_fetch_ok_mode[jump]:
  gvs[sym_step_own_eq, sym_step_def, sym_step_op_def, sym_jump_def, CaseEq "list", CaseEq "option"] >>
  simp[sym_jump_def, sym_with_pc_def]
QED

Resume merge_iszero_outside_fetch_ok_mode[jumpi]:
  gvs[sym_step_own_eq, sym_step_def, sym_step_op_def, sym_jumpi_def, AllCaseEqs()] >>
  gvs[sym_set_stack_def, sym_with_pc_def, asm_next_def]
QED

Resume merge_iszero_outside_fetch_ok_mode[linear]:
  `v.sym_base.as_pc = u.sym_base.as_pc + 1`
    by (drule_all protected_step_pc_next >> simp[]) >>
  `r u.sym_base.as_pc <= u.sym_base.as_pc` by simp[Abbr `r`, splice_pc_def] >>
  `!x. (if allow_own then sym_step_own (pre ++ repl ++ tail) env own ins x
        else sym_step (pre ++ repl ++ tail) env ins x) =
       (if allow_own then sym_step_own (pre ++ pat ++ tail) env own ins x
        else sym_step (pre ++ pat ++ tail) env ins x)` by
    (gen_tac >> irule protected_step_prog_cong >> simp[MEM_APPEND]) >>
  simp[] >>
  mp_tac (Q.INST [`ss` |-> `sym_with_pc (r u.sym_base.as_pc) u`,
    `n` |-> `u.sym_base.as_pc - r u.sym_base.as_pc`, `p` |-> `pre ++ pat ++ tail`,
    `env` |-> `env`, `own` |-> `own`, `inst` |-> `ins`] protected_step_pc_add) >>
  simp[sym_with_pc_def] >>
  Cases_on `(if allow_own then
      sym_step_own (pre ++ pat ++ tail) env own ins (sym_with_pc (r u.sym_base.as_pc) u)
    else sym_step (pre ++ pat ++ tail) env ins (sym_with_pc (r u.sym_base.as_pc) u))` >>
  gvs[sym_with_pc_def, sym_result_pc_add_def] >>
  rename1 `(if _ then _ else _) = SymOK b` >>
  `b.sym_base.as_pc = r u.sym_base.as_pc + 1` by
    (drule_all protected_step_pc_next >> simp[]) >>
  disch_tac >>
  simp[Once sym_state_component_equality, Once asm_state_component_equality]
QED

Finalise merge_iszero_outside_fetch_ok_mode

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
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`] merge_iszero_outside_fetch_ok_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
