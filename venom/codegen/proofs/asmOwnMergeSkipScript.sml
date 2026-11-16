(* Source-only redirect windows for merge_jumpdests with fixed own bytes. *)
Theory asmOwnMergeSkip
Ancestors
  asmSymPcOwn asmSymOwnCode asmSplice asmSymSem asmSem list rich_list

Theorem rename_skip_own:
  p = pre ++ AsmLabel x :: next :: sfx /\ asm_labels_unique p /\
  (next = AsmLabel y /\ y <> x \/
   next = AsmPushLabel y /\ ?more. sfx = AsmOp "JUMP" :: more) /\
  t.sym_base.as_pc = LENGTH pre /\ t.sym_base.as_stack = [] /\
  sym_terminal (sym_run_own p env own fuel t) ==>
  ?j fuel2. INDEX_OF (AsmLabel y) p = SOME j /\ fuel2 < fuel /\
    sym_run_own p env own fuel t =
    sym_run_own p env own fuel2
      (t with sym_base := t.sym_base with as_pc := j)
Proof
  strip_tac >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `next = _` SUBST_ALL_TAC
  >- (
    `~MEM (AsmLabel y) pre`
      by (irule asm_labels_unique_append_not_mem >>
          qexists_tac `AsmLabel x :: AsmLabel y :: sfx` >> fs[]) >>
    `INDEX_OF (AsmLabel y) (pre ++ AsmLabel x :: AsmLabel y :: sfx) =
     SOME (LENGTH pre + 1)`
      by simp[INDEX_OF_APPEND, INDEX_OF_CONS] >>
    Cases_on `fuel`
    >- gvs[Once sym_run_own_def, sym_terminal_def] >>
    rename1 `SUC remaining` >>
    qexistsl_tac [`LENGTH pre + 1`, `remaining`] >>
    simp[Once sym_run_own_def, EL_APPEND_EQN, sym_step_own_eq,
         sym_step_def, asm_step_def, sym_lift_def, asm_next_def] >>
    AP_TERM_TAC >>
    simp[sym_state_component_equality, asm_state_component_equality]) >>
  qpat_x_assum `sfx = _` SUBST_ALL_TAC >>
  qabbrev_tac `p = pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmLabel x /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmPushLabel y /\
   LENGTH pre + 2 < LENGTH p /\ EL (LENGTH pre + 2) p = AsmOp "JUMP"`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  qabbrev_tac `t1 = t with sym_base := t.sym_base with
                        as_pc := LENGTH pre + 1` >>
  qabbrev_tac `t2 = t1 with <|sym_base := asm_next t1.sym_base;
                              sym_stack := Lab y 0 :: t.sym_stack|>` >>
  `!n. sym_run_own p env own (SUC n) t = sym_run_own p env own n t1`
    by (gen_tac >> simp[Once sym_run_own_def, sym_step_own_eq,
          sym_step_def, asm_step_def, sym_lift_def, asm_next_def] >>
        AP_TERM_TAC >> simp[Abbr `t1`, sym_state_component_equality,
                           asm_state_component_equality]) >>
  `!n. sym_run_own p env own (SUC n) t1 = sym_run_own p env own n t2`
    by simp[Once sym_run_own_def, Abbr `t1`, Abbr `t2`,
            sym_step_own_eq, sym_step_def, sym_set_stack_def, asm_next_def] >>
  Cases_on `fuel`
  >- gvs[Once sym_run_own_def, sym_terminal_def] >>
  rename1 `SUC after_label` >>
  Cases_on `after_label`
  >- gvs[Once sym_run_own_def, sym_terminal_def] >>
  rename1 `SUC (SUC after_push)` >>
  Cases_on `after_push`
  >- gvs[Once sym_run_own_def, sym_terminal_def] >>
  rename1 `SUC (SUC (SUC after_jump))` >>
  Cases_on `INDEX_OF (AsmLabel y) p`
  >- (qpat_x_assum `sym_terminal _` mp_tac >>
      simp[] >> simp[Once sym_run_own_def, Abbr `t2`, Abbr `t1`,
        asm_next_def, sym_step_own_eq, sym_step_def, sym_step_op_def,
        sym_jump_def, sym_jump_dest_def, sym_terminal_def]) >>
  rename1 `SOME j` >> qexistsl_tac [`j`, `after_jump`] >> simp[] >>
  simp[Once sym_run_own_def, Abbr `t2`, Abbr `t1`, asm_next_def,
       sym_step_own_eq, sym_step_def, sym_step_op_def, sym_jump_def,
       sym_jump_dest_def] >>
  AP_TERM_TAC >> simp[sym_state_component_equality, asm_state_component_equality]
QED
