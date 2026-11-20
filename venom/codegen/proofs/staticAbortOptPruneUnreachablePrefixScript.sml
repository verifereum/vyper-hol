Theory staticAbortOptPruneUnreachablePrefix
Ancestors
  staticAbortProtectedTraceCoverage staticAbortProtectedStepControl codegenSymRel
  asmSplice asmSpliceOwn asmSymOwnCode asmSymPcOwn asmSymPc
  asmSymSem asmOptimizer asmSem finite_map list arithmetic

(* Fetch at a retained index after deleting the singleton [x]. *)
Theorem prune_one_fetch[local]:
  !r. r = (\j. if j < LENGTH pre + 1 then j else j-1) ==>
  i <> LENGTH pre + 1 /\ i < LENGTH (pre ++ [t:asm_inst;x] ++ tail) ==>
    r i < LENGTH (pre ++ [t] ++ tail) /\
    EL (r i) (pre ++ [t] ++ tail) = EL i (pre ++ [t;x] ++ tail)
Proof
  SIMP_TAC (pure_ss ++ boolSimps.UNWIND_ss) [] >> BETA_TAC >> strip_tac >> simp[] >>
  Cases_on `i < LENGTH pre`
  >- (`i < LENGTH pre+1` by decide_tac >> simp[EL_APPEND_EQN]) >>
  Cases_on `i = LENGTH pre` >- simp[EL_APPEND_EQN] >>
  `LENGTH pre+2 <= i /\ LENGTH pre+1 <= i-1 /\
   i-1-LENGTH pre = SUC (i-(LENGTH pre+2)) /\
   i-LENGTH pre = SUC (SUC (i-(LENGTH pre+2)))` by decide_tac >>
  `~(i < LENGTH pre+1) /\ ~(i-1 < LENGTH pre)` by decide_tac >>
  fs[EL_APPEND_EQN] >> gvs[]
QED

Theorem prune_one_jump_dest[local]:
  ~asm_reachable_marker x ==>
  sym_jump_dest (pre ++ [t] ++ tail) dst =
    OPTION_MAP (\i. if i < LENGTH pre+1 then i else i-1)
      (sym_jump_dest (pre ++ [t;x] ++ tail) dst)
Proof
  strip_tac >> Cases_on `dst` >> simp[sym_jump_dest_def] >>
  rename1 `(if d = 0 then INDEX_OF (AsmLabel l) _ else _) = _` >>
  Cases_on `d = 0` >> simp[] >>
  mp_tac (Q.INST [`pfx` |-> `pre ++ [t]`, `pat` |-> `[x]`,
                  `repl` |-> `[]`, `sfx` |-> `tail`] splice_index_of_label) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  `AsmLabel l <> x` by (strip_tac >> gvs[asm_reachable_marker_def]) >>
  simp[] >> strip_tac >>
  Cases_on `INDEX_OF (AsmLabel l) (pre ++ t :: x :: tail)` >>
  gvs[splice_pc_def]
QED

Theorem prune_one_step_ok_mode[local]:
  !r. r = (\i. if i < LENGTH pre + 1 then i else i-1) ==>
  p = pre ++ [t;x] ++ tail /\ q = pre ++ [t] ++ tail /\
  ~asm_reachable_marker x /\ u.sym_base.as_pc <> LENGTH pre + 1 /\
  v.sym_base.as_pc <> LENGTH pre + 1 /\ (if allow_own then sym_step_own p env own inst u
     else sym_step p env inst u) = SymOK v ==>
  (if allow_own then sym_step_own q env own inst (sym_with_pc (r u.sym_base.as_pc) u)
     else sym_step q env inst (sym_with_pc (r u.sym_base.as_pc) u)) =
    SymOK (sym_with_pc (r v.sym_base.as_pc) v)
Proof
  SIMP_TAC (pure_ss ++ boolSimps.UNWIND_ss) [] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `d = LENGTH pre + 1` >> simp[] >>
  qabbrev_tac `r = (\i:num. if i < d then i else i - 1)` >>
  `!a. sym_jump_dest q a = OPTION_MAP r (sym_jump_dest p a)`
    by (unabbrev_all_tac >> metis_tac[prune_one_jump_dest]) >>
  `!i. i <> d /\ i + 1 <> d ==> r (i+1) = r i + 1`
    by (rpt strip_tac >> simp[Abbr `r`] >>
        Cases_on `i+1 < d` >> Cases_on `i < d` >> gvs[] >>
        fs[Abbr `d`] >> decide_tac) >>
  Cases_on `inst = AsmOp "JUMP"`
  >- (gvs[sym_step_own_eq, sym_step_def, sym_step_op_def] >>
      Cases_on `u.sym_stack` >> gvs[sym_jump_def, sym_with_pc_def, AllCaseEqs()]) >>
  Cases_on `inst = AsmOp "JUMPI"`
  >- (gvs[sym_step_own_eq, sym_step_def, sym_step_op_def] >>
      Cases_on `u.sym_stack` >> gvs[sym_jumpi_def] >>
      rename1 `u.sym_stack = dest :: rest` >> Cases_on `rest` >> gvs[] >>
      rename1 `u.sym_stack = dest :: cond :: stk` >>
      Cases_on `cond` >> gvs[] >> rename1 `Val w` >>
      Cases_on `w = 0w`
      >- (gvs[sym_set_stack_def, asm_next_def, sym_with_pc_def] >> metis_tac[]) >>
      gvs[sym_with_pc_def, AllCaseEqs()]) >>
  `v.sym_base.as_pc = u.sym_base.as_pc + 1` by (drule_all protected_step_pc_next >> simp[]) >>
  `r v.sym_base.as_pc = r u.sym_base.as_pc + 1` by metis_tac[] >>
  `!z. (if allow_own then sym_step_own q env own inst z
     else sym_step q env inst z) = (if allow_own then sym_step_own p env own inst z
     else sym_step p env inst z)`
    by (gen_tac >> irule protected_step_prog_cong >>
        simp[MEM_APPEND] >> gen_tac >>
        `AsmDataHeader l <> x` by (strip_tac >> gvs[asm_reachable_marker_def]) >>
        simp[]) >>
  simp[] >>
  `r u.sym_base.as_pc <= u.sym_base.as_pc` by simp[Abbr `r`] >>
  mp_tac (Q.INST [`ss` |-> `sym_with_pc (r u.sym_base.as_pc) u`,
    `n` |-> `u.sym_base.as_pc - r u.sym_base.as_pc`] protected_step_pc_add) >>
  simp[sym_with_pc_def] >>
  Cases_on `(if allow_own then sym_step_own p env own inst (sym_with_pc (r u.sym_base.as_pc) u)
     else sym_step p env inst (sym_with_pc (r u.sym_base.as_pc) u))` >>
  gvs[sym_with_pc_def, sym_result_pc_add_def] >>
  rename1 `(if _ then _ else _) = SymOK b` >>
  `b.sym_base.as_pc = r u.sym_base.as_pc + 1` by
    (drule_all protected_step_pc_next >> simp[]) >>
  disch_tac >>
  simp[Once sym_state_component_equality, Once asm_state_component_equality]
QED

Theorem prune_one_stopped_prefix_mode:
  !d i. d = LENGTH pre + 1 ==> i = ss.sym_base.as_pc ==>
  p = pre ++ [t;x] ++ tail /\ q = pre ++ [t] ++ tail /\
  asm_terminal_op t /\ ~asm_reachable_marker x /\ s.as_pc = 0 /\
  sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss ==>
  i <> d /\
  sym_steps_mode allow_own q env own n (sym_init s) = SymOK (sym_with_pc (if i < d then i else i-1) ss) /\
  (!k l. k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0 ==>
    ?j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/
      (?a. EL j q = AsmPushOfst l a) \/ EL j q = AsmDataLabel l))
Proof
  SIMP_TAC (pure_ss ++ boolSimps.UNWIND_ss) [] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `p = pre ++ [t;x] ++ tail` (mk_asm "source_code") >>
  qpat_x_assum `q = pre ++ [t] ++ tail` (mk_asm "dest_code") >> simp[] >>
  `!m a. sym_steps_mode allow_own p env own m (sym_init s) = SymOK a ==>
    a.sym_base.as_pc <> LENGTH pre + 1`
    by (rpt strip_tac >>
        qspecl_then [`m`, `s`, `a`] mp_tac
          (Q.INST [`dead` |-> `[x]`, `term` |-> `t`]
            protected_prefix_excludes_dead_run_mode) >> asm "source_code" (fn th => fs[th])) >>
  conj_tac >- metis_tac[] >>
  qabbrev_tac `r = (\i:num. if i < LENGTH pre + 1 then i else i-1)` >>
  `!m a. sym_steps_mode allow_own p env own m (sym_init s) = SymOK a ==>
         sym_steps_mode allow_own q env own m (sym_init s) = SymOK (sym_with_pc (r a.sym_base.as_pc) a)`
    by (Induct >- simp[sym_steps_mode_zero, sym_init_def, sym_with_pc_def, Abbr `r`] >>
        rpt gen_tac >> rewrite_tac[arithmeticTheory.ADD1, sym_steps_mode_add] >>
        Cases_on `sym_steps_mode allow_own p env own m (sym_init s)` >> simp[] >>
        rename1 `sym_steps_mode allow_own p env own m (sym_init s) = SymOK u` >>
        `sym_steps_mode allow_own q env own m (sym_init s) = SymOK (sym_with_pc (r u.sym_base.as_pc) u)`
          by metis_tac[] >> simp[] >>
        disch_tac >>
        `u.sym_base.as_pc < LENGTH p /\ (if allow_own then sym_step_own p env own (EL u.sym_base.as_pc p) u
     else sym_step p env (EL u.sym_base.as_pc p) u) = SymOK a`
          by (qpat_x_assum `sym_steps_mode allow_own p env own 1 u = SymOK a` mp_tac >>
              simp_tac bool_ss [sym_steps_mode_ok_one]) >>
        `a.sym_base.as_pc <> LENGTH pre+1` by
          (qpat_assum `!m a. _ ==> a.sym_base.as_pc <> _`
             (qspecl_then [`m+1`, `a`] mp_tac) >> simp[sym_steps_mode_add]) >>
        `u.sym_base.as_pc <> LENGTH pre+1` by metis_tac[] >>
        `r u.sym_base.as_pc < LENGTH q /\
         EL (r u.sym_base.as_pc) q = EL u.sym_base.as_pc p`
          by (mp_tac (Q.INST [`i` |-> `u.sym_base.as_pc`] (SIMP_RULE bool_ss [] prune_one_fetch)) >>
              asm "source_code" (fn hp => asm "dest_code" (fn hq => fs[hp,hq,Abbr `r`]))) >>
        `(if allow_own then sym_step_own q env own (EL u.sym_base.as_pc p) (sym_with_pc (r u.sym_base.as_pc) u)
     else sym_step q env (EL u.sym_base.as_pc p) (sym_with_pc (r u.sym_base.as_pc) u)) =
         SymOK (sym_with_pc (r a.sym_base.as_pc) a)`
          by (asm "source_code" assume_tac >> asm "dest_code" assume_tac >>
              drule_all (SIMP_RULE bool_ss [] prune_one_step_ok_mode) >> simp[Abbr `r`]) >>
        ` (sym_with_pc (r u.sym_base.as_pc) u).sym_base.as_pc = r u.sym_base.as_pc`
          by simp[sym_with_pc_def] >>
        PURE_REWRITE_TAC [sym_steps_mode_ok_one] >>
        qpat_assum `(sym_with_pc _ _).sym_base.as_pc = _` SUBST1_TAC >>
        qpat_assum `EL (r u.sym_base.as_pc) q = _` SUBST1_TAC >>
        conj_tac >> first_assum ACCEPT_TAC) >>
  conj_asm1_tac >- metis_tac[] >>
  `sym_state_labels_in (asm_label_refs q) (sym_init s)`
    by simp[sym_state_labels_in_def, sym_init_def, MEM_MAP] >>
  `sym_state_labels_in (asm_label_refs q)
    (sym_with_pc (if ss.sym_base.as_pc < LENGTH pre + 1 then ss.sym_base.as_pc
                  else ss.sym_base.as_pc - 1) ss)` by
    (qpat_assum `sym_steps_mode _ q _ _ n _ = _` mp_tac >>
     Cases_on `allow_own` >> PURE_REWRITE_TAC [sym_steps_mode_def, COND_CLAUSES] >>
     strip_tac
     >- (`(sym_init s).sym_base.as_stack = []` by simp[sym_init_def] >>
         drule_all sym_steps_own_preserves_splice_invariant >> simp[]) >>
     drule_all sym_steps_labels_in >> simp[]) >>
  pop_assum (mp_tac o REWRITE_RULE [sym_state_labels_in_def]) >>
  simp[sym_with_pc_def] >>
  strip_tac >> rpt strip_tac >>
  `MEM (Lab l 0) ss.sym_stack` by metis_tac[EL_MEM] >>
  `MEM l (asm_label_refs q)` by metis_tac[] >>
  qpat_x_assum `MEM l (asm_label_refs q)` mp_tac >>
  simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  gen_tac >> rename1 `MEM inst q` >> strip_tac >>
  qpat_x_assum `MEM inst q` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `inst = EL j q` >> qexists_tac `j` >>
  Cases_on `inst` >> gvs[] >> metis_tac[]
QED

Theorem prune_one_stopped_prefix:
  !d i. d = LENGTH pre + 1 ==> i = ss.sym_base.as_pc ==>
  p = pre ++ [t;x] ++ tail /\ q = pre ++ [t] ++ tail /\
  asm_terminal_op t /\ ~asm_reachable_marker x /\ s.as_pc = 0 /\
  sym_steps p env n (sym_init s) = SymOK ss ==>
  i <> d /\
  sym_steps q env n (sym_init s) = SymOK (sym_with_pc (if i < d then i else i-1) ss) /\
  (!k l. k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0 ==>
    ?j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/
      (?a. EL j q = AsmPushOfst l a) \/ EL j q = AsmDataLabel l))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`]
    prune_one_stopped_prefix_mode |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
