Theory asmFinalizerPrefixUnused
Ancestors
  asmOptPruneUnused asmSplice asmSymPc finalizerContract
  asmSymSem asmOptimizer asmWf asmSem

(* S, U and T are expanded quotations, not logical definitions. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
     ?m b. sym_steps q env m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
       b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

val single_site = ``!pre pat repl post D.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  (!env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ~(a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp "GAS")) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. sym_steps (pre ++ repl ++ post) env e u =
              SymOK (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat)
                                 (LENGTH repl) a.sym_base.as_pc) a) /\
            (a.sym_base.as_pc <= LENGTH pre \/
             LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
            (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))) ==>
  ^transport (pre ++ pat ++ post) (pre ++ repl ++ post)``;
val transitive = ``!p q r. ^transport p q /\ ^transport q r ==> ^transport p r``;

Theorem unused_label_prefix_site[local]:
  ^single_site ==> !pre l post.
    asm_static_wf (pre ++ [AsmLabel l] ++ post) /\
    ~MEM l (asm_label_refs (pre ++ [AsmLabel l] ++ post)) ==>
    ^transport (pre ++ [AsmLabel l] ++ post) (pre ++ post)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`pre`, `[AsmLabel l]`, `[]`, `post`, `1`] mp_tac) >>
  (impl_tac >- (
    simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def] >>
    conj_tac >- gvs[asm_label_refs_def] >>
    rpt gen_tac >> strip_tac >> qexists_tac `1` >> simp[] >>
    `LENGTH pre < LENGTH (pre ++ [AsmLabel l] ++ post) /\
     EL (LENGTH pre) (pre ++ [AsmLabel l] ++ post) = AsmLabel l`
      by simp[listTheory.EL_APPEND_EQN] >>
    conj_tac
    >- (rpt gen_tac >> strip_tac >> gvs[sym_steps_def]) >>
    rpt gen_tac >>
    simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_lift_def,
         asm_step_def, asm_next_def, sym_terminal_def] >>
    strip_tac >> qexists_tac `0` >>
    gvs[sym_steps_def, splice_pc_def, sym_with_pc_def,
        sym_state_component_equality, asm_state_component_equality])) >>
  simp[]
QED

Theorem filter_unused_prefix_under[local]:
  ^single_site /\ ^transitive ==>
  !sfx pre used.
    asm_static_wf (pre ++ sfx) /\
    (!l. MEM l (asm_label_refs (pre ++ sfx)) ==> MEM l used) ==>
    ^transport (pre ++ sfx)
      (pre ++ FILTER ($~ o asm_unused_label used) sfx)
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p. tr p p` by
    (unabbrev_all_tac >> BETA_TAC >> gen_tac >> qexists_tac `1` >> simp[] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LE_ADD]) >>
  `!pre l post.
    asm_static_wf (pre ++ [AsmLabel l] ++ post) /\
    ~MEM l (asm_label_refs (pre ++ [AsmLabel l] ++ post)) ==>
    tr (pre ++ [AsmLabel l] ++ post) (pre ++ post)` by
    (unabbrev_all_tac >> match_mp_tac unused_label_prefix_site >> first_assum ACCEPT_TAC) >>
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> reverse (Cases_on `asm_unused_label used h`) >> simp[]
  >- (first_x_assum (qspecl_then [`pre ++ [h]`, `used`] mp_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      disch_then irule >> simp[]) >>
  Cases_on `h` >> gvs[asm_unused_label_def] >>
  `!l. MEM l (asm_label_refs (pre ++ sfx)) ==> MEM l used` by
    (qpat_assum `!l. MEM l (asm_label_refs (pre ++ AsmLabel s :: sfx)) ==> _`
       mp_tac >> simp[label_refs_append, asm_label_refs_def]) >>
  `~MEM s (asm_label_refs (pre ++ AsmLabel s :: sfx))` by metis_tac[] >>
  `asm_static_wf (pre ++ sfx)` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `pat` |-> `[AsmLabel s]`,
                    `repl` |-> `[]`, `sfx` |-> `sfx`] asm_splice_window_refines) >>
     simp[asm_splice_ok_def, unused_label_window_refines, is_data_inst_def,
          asm_label_refs_def, asm_refines_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
     (impl_tac >- gvs[asm_label_refs_def]) >> simp[]) >>
  metis_tac[listTheory.APPEND, listTheory.APPEND_ASSOC]
QED

Theorem prune_unused_prefix_transport_conditional:
  ^single_site /\ ^transitive ==>
  !p. asm_static_wf p ==> ^transport p (FST (prune_unused_jumpdests p))
Proof
  strip_tac >> gen_tac >>
  mp_tac filter_unused_prefix_under >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`p`, `[]`, `asm_label_refs p`] mp_tac) >>
  simp[prune_unused_jumpdests_def]
QED
