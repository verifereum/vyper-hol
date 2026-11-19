(* Shared own-code splice simulation. Static facts stay in asmSplice. *)
Theory asmSpliceOwn
Ancestors
  asmSymPcOwn asmSplice finalizerContractOwn
  asmOwnSpliceStep asmOwnLabels asmOwnSpliceSimulation
  asmSymOwnCode asmSymPc asmSymSem asmOptimizer asmSem

Definition sym_steps_own_def:
  sym_steps_own p env own 0 ss = SymOK ss ∧
  sym_steps_own p env own (SUC n) ss =
    if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
    else
      case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_steps_own p env own n ss'
      | r => r
End

Theorem sym_steps_own_pos:
  0 < n ∧ ss.sym_base.as_pc < LENGTH p ⇒
  sym_steps_own p env own n ss =
    case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK ss' => sym_steps_own p env own (n - 1) ss'
    | r => r
Proof
  Cases_on `n` >> rw[sym_steps_own_def]
QED

Definition asm_window_refines_own_def:
  asm_window_refines_own pfx pat repl sfx ⇔
    asm_static_wf (pfx ++ pat ++ sfx) ⇒
    ∀env own ss.
      ss.sym_base.as_pc = LENGTH pfx ∧ ss.sym_base.as_stack = [] ⇒
      ∃j j'.
        0 < j ∧
        (∀a. sym_steps_own (pfx ++ pat ++ sfx) env own j ss = SymOK a ⇒
             (a.sym_base.as_pc ≤ LENGTH pfx ∨
              LENGTH pfx + LENGTH pat ≤ a.sym_base.as_pc) ∧
             sym_steps_own (pfx ++ repl ++ sfx) env own j' ss =
               SymOK (sym_with_pc
                        (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
                           a.sym_base.as_pc) a)) ∧
        (sym_terminal (sym_steps_own (pfx ++ pat ++ sfx) env own j ss) ⇒
         sym_result_rel (sym_steps_own (pfx ++ pat ++ sfx) env own j ss)
           (sym_steps_own (pfx ++ repl ++ sfx) env own j' ss))
End

Theorem asm_splice_window_refines_own:
  asm_splice_ok pat repl ∧
  (∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ pat ++ sfx))) ∧
  asm_window_refines_own pfx pat repl sfx ⇒
  asm_refines_own (pfx ++ pat ++ sfx) (pfx ++ repl ++ sfx)
Proof
  strip_tac >> simp[asm_refines_own_def] >> strip_tac >>
  `!l. MEM (AsmLabel l) pat ==>
       ~MEM l (asm_label_refs (pfx ++ repl ++ sfx))`
    by (gvs[asm_splice_ok_def, label_refs_append] >> metis_tac[]) >>
  `asm_static_wf (pfx ++ repl ++ sfx) /\
   FILTER is_data_inst (pfx ++ repl ++ sfx) =
     FILTER is_data_inst (pfx ++ pat ++ sfx)`
    by (irule asm_splice_static_wf >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST
    [`srcSteps` |-> `sym_steps_own (pfx ++ pat ++ sfx) env own`,
     `dstSteps` |-> `sym_steps_own (pfx ++ repl ++ sfx) env own`,
     `state_inv` |-> `\ss. ss.sym_base.as_stack = [] /\
       sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss`]
    splice_run_terminal_own_by_steps)) >>
  impl_tac
  >- (asm_rewrite_tac[sym_steps_own_def] >> rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- metis_tac[sym_step_own_base_stack] >>
          metis_tac[sym_step_own_labels_in])
      >- (rpt gen_tac >> strip_tac >> irule splice_inst_step_own_ok >> simp[] >>
          goal_assum (drule_at Any) >> simp[])
      >- (rpt strip_tac >> irule splice_inst_step_own_terminal >> simp[])
      >> gvs[asm_window_refines_own_def]) >>
  disch_then (qspecl_then [`fuel`, `sym_init s`] mp_tac) >>
  simp[sym_init_def, splice_pc_def, sym_with_pc_def,
       sym_state_labels_in_def, listTheory.MEM_MAP]
QED

Theorem sym_steps_own_add:
  !p env own m n ss. sym_steps_own p env own (m+n) ss =
    case sym_steps_own p env own m ss of
      SymOK mid => sym_steps_own p env own n mid | r => r
Proof
  ntac 3 gen_tac >> Induct >- simp[sym_steps_own_def] >>
  rpt gen_tac >>
  pure_rewrite_tac[arithmeticTheory.ADD_CLAUSES, sym_steps_own_def] >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p` >> simp[] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >> simp[]
QED

Theorem sym_steps_own_eq_without_code_reads:
  !n ss.
    (!i t. i < n /\ sym_steps p env i ss = SymOK t /\
       t.sym_base.as_pc < LENGTH p ==>
       EL t.sym_base.as_pc p <> AsmOp "CODESIZE" /\
       EL t.sym_base.as_pc p <> AsmOp "CODECOPY") ==>
    sym_steps_own p env own n ss = sym_steps p env n ss
Proof
  Induct >- simp[sym_steps_own_def, sym_steps_def] >>
  gen_tac >> strip_tac >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p`
  >- simp[sym_steps_own_def, sym_steps_def] >>
  `sym_step_own p env own (EL ss.sym_base.as_pc p) ss =
   sym_step p env (EL ss.sym_base.as_pc p) ss` by
    (irule sym_step_own_eq >>
     qpat_assum `!i t. _` (qspecl_then [`0`, `ss`] mp_tac) >>
     simp[sym_steps_def]) >>
  simp[sym_steps_own_def, sym_steps_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[] >>
  first_x_assum irule >> rpt gen_tac >> strip_tac >>
  qpat_assum `!i t. _` (qspecl_then [`SUC i`, `t`] mp_tac) >>
  simp[sym_steps_def]
QED

Theorem sym_steps_own_preserves_splice_invariant[local]:
  !n u a. u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs p) u /\
    sym_steps_own p env own n u = SymOK a ==>
    a.sym_base.as_stack = [] /\ sym_state_labels_in (asm_label_refs p) a
Proof
  Induct >- simp[sym_steps_own_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `u.sym_base.as_pc >= LENGTH p` >> fs[sym_steps_own_def] >>
  Cases_on `sym_step_own p env own (EL u.sym_base.as_pc p) u` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  conj_tac >- (drule_all sym_step_own_base_stack >> simp[]) >>
  `MEM (EL u.sym_base.as_pc p) p` by simp[listTheory.EL_MEM] >>
  drule_all sym_step_own_labels_in >> simp[]
QED

Theorem splice_own_steps_outside[local]:
  !env own n u a.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  0 < n /\
  (u.sym_base.as_pc < LENGTH pre \/ LENGTH pre + LENGTH pat <= u.sym_base.as_pc) /\
  u.sym_base.as_stack = [] /\
  sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u /\
  sym_steps_own (pre ++ pat ++ post) env own n u = SymOK a ==>
  ?mid. u.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
    (mid.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= mid.sym_base.as_pc) /\
    sym_steps_own (pre ++ pat ++ post) env own 1 u = SymOK mid /\
    sym_steps_own (pre ++ pat ++ post) env own (n-1) mid = SymOK a /\
    sym_steps_own (pre ++ repl ++ post) env own 1
      (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
        u.sym_base.as_pc) u) =
    SymOK (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
      mid.sym_base.as_pc) mid)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.sym_base.as_pc < LENGTH (pre ++ pat ++ post)` by
    (Cases_on `n` >> fs[sym_steps_own_def] >>
     Cases_on `u.sym_base.as_pc >= LENGTH (pre ++ pat ++ post)` >>
     fs[sym_steps_own_def]) >>
  `?mid. sym_step_own (pre ++ pat ++ post) env own
      (EL u.sym_base.as_pc (pre ++ pat ++ post)) u = SymOK mid /\
     sym_steps_own (pre ++ pat ++ post) env own (n-1) mid = SymOK a` by
    (qpat_x_assum `sym_steps_own _ _ _ n _ = _` mp_tac >>
     simp[Once sym_steps_own_pos] >>
     Cases_on `sym_step_own (pre ++ pat ++ post) env own
       (EL u.sym_base.as_pc (pre ++ pat ++ post)) u` >> simp[]) >>
  drule_all splice_inst_step_own_ok >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pat <> []` by metis_tac[asm_splice_ok_def] >>
  drule_all splice_fetch >> disch_then (qspec_then `repl` strip_assume_tac) >>
  `sym_steps_own (pre ++ repl ++ post) env own 1
      (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
        u.sym_base.as_pc) u) = SymOK
      (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
        mid.sym_base.as_pc) mid)` by
    (rewrite_tac[arithmeticTheory.ONE, sym_steps_own_def] >>
     simp[sym_with_pc_def] >>
     qpat_x_assum `sym_step_own (pre ++ repl ++ post) _ _ _ _ = _` mp_tac >>
     simp[sym_with_pc_def, sym_steps_own_def] >>
     fs[listTheory.LENGTH_APPEND]) >>
  qexists_tac `mid` >> simp[] >>
  simp[Once sym_steps_own_pos, sym_steps_own_def] >> fs[]
QED

Theorem bounded_splice_prefix_transport_own:
  !pre pat repl post D.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==>
       ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  (!env own u. u.sym_base.as_pc = LENGTH pre /\
    u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps_own (pre ++ pat ++ post) env own i u = SymOK a ==>
        !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
          a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp op ==>
          i = 0 /\ repl <> [] /\ HD repl = HD pat) /\
      (!a. sym_steps_own (pre ++ pat ++ post) env own d u = SymOK a ==>
        ?e. sym_steps_own (pre ++ repl ++ post) env own e u =
          SymOK (sym_with_pc
            (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
               a.sym_base.as_pc) a) /\
          (a.sym_base.as_pc <= LENGTH pre \/
            LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
          (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))) ==>
  ?K. 0 < K /\ !env own s n a.
    s.as_pc = 0 /\
    sym_steps_own (pre ++ pat ++ post) env own n (sym_init s) = SymOK a ==>
    (?m b. sym_steps_own (pre ++ repl ++ post) env own m (sym_init s) = SymOK b /\
       n <= K * (m+1)) /\
    (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
      a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
      EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp op ==>
      ?m b. sym_steps_own (pre ++ repl ++ post) env own m (sym_init s) = SymOK b /\
        b.sym_base.as_pc < LENGTH (pre ++ repl ++ post) /\
        EL b.sym_base.as_pc (pre ++ repl ++ post) = AsmOp op /\
        (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
        MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
        FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.ISPECL [`pre:asm_inst list`, `pat:asm_inst list`, `repl:asm_inst list`,
    `post:asm_inst list`, `D:num`,
    `UNCURRY (sym_steps_own (pre ++ pat ++ post))`,
    `UNCURRY (sym_steps_own (pre ++ repl ++ post))`]
    bounded_splice_prefix_transport_by_steps) >>
  simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY, pairTheory.FST,
                    pairTheory.SND, sym_steps_own_def, sym_steps_own_add] >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- metis_tac[sym_steps_own_preserves_splice_invariant] >>
      rpt gen_tac >> strip_tac >>
      rename1 `sym_steps_own _ env own n u = SymOK a` >>
      mp_tac (Q.SPECL [`env`, `own`, `n`, `u`, `a`] splice_own_steps_outside) >> simp[])) >>
  simp[]
QED
