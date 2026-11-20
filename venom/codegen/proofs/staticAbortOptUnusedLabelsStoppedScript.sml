Theory staticAbortOptUnusedLabelsStopped
Ancestors
  asmSymOwnCode asmSymPcOwn asmSpliceOwn
  staticAbortProtectedTraceCoverage staticAbortProtectedStepControl
  staticAbortOptMergeIszeroSync codegenSymRel asmSplice asmSymPc asmSymSem
  asmOptimizer asmSem arithmetic list

Theorem unused_label_one_stopped_prefix_mode:
  !p. p = pre ++ [AsmLabel l] ++ tail ==>
  ~MEM l (asm_label_refs p) /\ s.as_pc = 0 /\
  sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss ==>
  ?j. sym_steps_mode allow_own (pre ++ tail) env own j (sym_init s) =
      SymOK (sym_with_pc (splice_pc (LENGTH pre) 1 0 ss.sym_base.as_pc) ss)
Proof
  qx_gen_tac `p` >>
  disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qabbrev_tac `q = pre ++ tail` >>
  qabbrev_tac `r = splice_pc (LENGTH (pre:asm_inst list)) 1 0` >>
  qid_spec_tac `ss` >> Induct_on `n`
  >- (simp[sym_steps_mode_zero] >> rpt strip_tac >> qexists_tac `0` >>
      simp[sym_steps_mode_zero, Abbr `r`, splice_pc_def, sym_init_def, sym_with_pc_def]) >>
  gen_tac >> rewrite_tac[ADD1, sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own p env own n (sym_init s)` >> simp[] >>
  rename1 `sym_steps_mode allow_own p env own n (sym_init s) = SymOK u` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?j. sym_steps_mode allow_own q env own j (sym_init s) = SymOK (sym_with_pc (r u.sym_base.as_pc) u)`
    by metis_tac[] >>
  `u.sym_base.as_pc < LENGTH p /\
   (if allow_own then sym_step_own p env own (EL u.sym_base.as_pc p) u
    else sym_step p env (EL u.sym_base.as_pc p) u) = SymOK ss` by
    fs[sym_steps_mode_ok_one] >>
  Cases_on `u.sym_base.as_pc = LENGTH pre`
  >- suspend "label" >>
  suspend "retained"
QED

Resume unused_label_one_stopped_prefix_mode[label]:
  `EL u.sym_base.as_pc p = AsmLabel l` by simp[Abbr `p`, EL_APPEND_EQN] >>
  `u.sym_base.as_stack = []` by metis_tac[sym_init_prefix_base_stack_mode] >>
  `ss = sym_with_pc (u.sym_base.as_pc + 1) u` by
    (qpat_assum `EL _ p = AsmLabel l` (fn th =>
       qpat_assum `(if allow_own then sym_step_own _ _ _ _ u else sym_step _ _ _ u) = _`
         (mp_tac o PURE_REWRITE_RULE [th])) >>
     simp[sym_step_own_eq, sym_step_def, sym_lift_def, asm_step_def, asm_next_def, sym_with_pc_def,
          sym_state_component_equality, asm_state_component_equality]) >>
  `sym_with_pc (r ss.sym_base.as_pc) ss = sym_with_pc (r u.sym_base.as_pc) u` by
    simp[Abbr `r`, splice_pc_def, sym_with_pc_def] >>
  qexists_tac `j` >> simp[]
QED

Resume unused_label_one_stopped_prefix_mode[retained]:
  Q.SUBGOAL_THEN `u.sym_base.as_pc < LENGTH pre \/ LENGTH pre + 1 <= u.sym_base.as_pc`
    assume_tac >- decide_tac >>
  `r u.sym_base.as_pc < LENGTH q /\ EL (r u.sym_base.as_pc) q = EL u.sym_base.as_pc p` by
    (simp[Abbr `p`, Abbr `q`, Abbr `r`, Excl "LENGTH_APPEND"] >>
     irule (SRULE [Excl "LENGTH_APPEND"]
       (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
         (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch))) >>
     simp[] >> decide_tac) >>
  `!t v. sym_state_labels_in (asm_label_refs p) t /\ sym_jump p t = SymOK v ==>
    sym_jump q (sym_with_pc (r u.sym_base.as_pc) t) = SymOK (sym_with_pc (r v.sym_base.as_pc) v)` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `q`, Abbr `r`] >>
     irule (cj 2 (SRULE [] (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]:asm_inst list`]
       splice_jump_ok))) >> qexists_tac `l` >> fs[Abbr `p`]) >>
  `sym_state_labels_in (asm_label_refs p) u` by
    (`(sym_init s).sym_base.as_stack = []` by simp[sym_init_def] >>
     `sym_state_labels_in (asm_label_refs p) (sym_init s)`
       by simp[sym_state_labels_in_def, sym_init_def, MEM_MAP] >>
     Cases_on `allow_own` >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
     >- (drule_all sym_steps_own_preserves_splice_invariant >> simp[]) >>
     drule_all sym_steps_labels_in >> simp[]) >>
  `(if allow_own then sym_step_own q env own (EL u.sym_base.as_pc p) (sym_with_pc (r u.sym_base.as_pc) u)
    else sym_step q env (EL u.sym_base.as_pc p) (sym_with_pc (r u.sym_base.as_pc) u)) =
     SymOK (sym_with_pc (r ss.sym_base.as_pc) ss)` suffices_by
    (strip_tac >> qexists_tac `j+1` >> simp[sym_steps_mode_add] >>
     qabbrev_tac `v = sym_with_pc (r u.sym_base.as_pc) u` >>
     `v.sym_base.as_pc = r u.sym_base.as_pc` by simp[Abbr `v`, sym_with_pc_def] >>
     simp[sym_steps_mode_ok_one]) >>
  qabbrev_tac `inst = EL u.sym_base.as_pc p` >>
  Cases_on `inst = AsmOp "JUMP"` >- suspend "jump" >>
  Cases_on `inst = AsmOp "JUMPI"` >- suspend "jumpi" >>
  suspend "linear"
QED

Resume unused_label_one_stopped_prefix_mode[jump]:
  fs[sym_step_own_eq, sym_step_def, sym_step_op_def] >> metis_tac[]
QED

Resume unused_label_one_stopped_prefix_mode[jumpi]:
  gns[sym_step_own_eq, sym_step_def, sym_step_op_def] >>
  namedCases_on `u.sym_stack` ["", "dest rest"] >> gns[sym_jumpi_def] >>
  namedCases_on `rest` ["", "cond stk"] >> gns[sym_jumpi_def] >>
  Cases_on `cond` >> gns[sym_jumpi_def] >>
  rename1 `u.sym_stack = dest :: Val c :: stk` >>
  Cases_on `c = 0w`
  >- (gns[] >>
      simp[Abbr `r`] >>
      irule (cj 2 (SRULE [] (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
        (INST_TYPE [alpha |-> ``:asm_inst``] splice_fallthrough_ok)))) >>
      simp[] >> decide_tac) >>
  `sym_jump p (u with sym_stack := dest :: stk) = SymOK ss` by
    (Cases_on `sym_jump_dest p dest` >>
     gs[sym_jump_def, sym_state_component_equality]) >>
  `sym_state_labels_in (asm_label_refs p) (u with sym_stack := dest :: stk)` by
    (fs[sym_state_labels_in_def] >> metis_tac[]) >>
  qpat_assum `!t v. _ /\ sym_jump p t = _ ==> _` drule_all >>
  Cases_on `sym_jump_dest q dest` >>
  gs[sym_jump_def, sym_with_pc_def, sym_state_component_equality]
QED

Resume unused_label_one_stopped_prefix_mode[linear]:
  `ss.sym_base.as_pc = u.sym_base.as_pc + 1` by
    (drule_all protected_step_pc_next >> simp[]) >>
  `r ss.sym_base.as_pc = r u.sym_base.as_pc + 1` by
    (simp[Abbr `r`] >> irule (cj 1 splice_pc_next) >> simp[]) >>
  `!t. (if allow_own then sym_step_own q env own inst t else sym_step q env inst t) =
       (if allow_own then sym_step_own p env own inst t else sym_step p env inst t)` by
    (gen_tac >> irule protected_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  qabbrev_tac `v = sym_with_pc (r u.sym_base.as_pc) u` >>
  qabbrev_tac `delta = u.sym_base.as_pc - r u.sym_base.as_pc` >>
  `v.sym_base.as_pc + delta = u.sym_base.as_pc` by
    simp[Abbr `v`, Abbr `delta`, Abbr `r`, sym_with_pc_def, splice_pc_def] >>
  `sym_with_pc (v.sym_base.as_pc + delta) v = u` by
    simp[Abbr `v`, sym_with_pc_def] >>
  mp_tac (Q.INST [`ss` |-> `v`, `n` |-> `delta`] protected_step_pc_add) >>
  simp[] >>
  Cases_on `(if allow_own then sym_step_own p env own inst v else sym_step p env inst v)` >> simp[sym_result_pc_add_def] >>
  disch_then (assume_tac o SYM) >> simp[] >>
  drule_all protected_step_pc_next >> strip_tac >>
  qpat_assum `sym_with_pc _ _ = ss` (SUBST_ALL_TAC o SYM) >>
  gns[Abbr `v`, sym_with_pc_def, sym_state_component_equality, asm_state_component_equality]
QED

Finalise unused_label_one_stopped_prefix_mode

Theorem unused_label_one_stopped_prefix:
  !p. p = pre ++ [AsmLabel l] ++ tail ==>
  ~MEM l (asm_label_refs p) /\ s.as_pc = 0 /\
  sym_steps p env n (sym_init s) = SymOK ss ==>
  ?j. sym_steps (pre ++ tail) env j (sym_init s) =
      SymOK (sym_with_pc (splice_pc (LENGTH pre) 1 0 ss.sym_base.as_pc) ss)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`] unused_label_one_stopped_prefix_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
