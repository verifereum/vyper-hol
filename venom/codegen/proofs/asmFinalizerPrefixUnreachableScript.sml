Theory asmFinalizerPrefixUnreachable
Ancestors
  asmOptPruneUnreachable asmSplice asmSymPc finalizerContract asmSymSem
  asmOptimizer asmWf asmSem list

(* Quotation abbreviations introduce no logical constants. *)
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

Theorem terminal_site_prefix_conditional[local]:
  ^single_site ==> !pre t x post.
    asm_terminal_op t /\ ~asm_reachable_marker x /\
    asm_static_wf (pre ++ [t;x] ++ post) ==>
    ^transport (pre ++ [t;x] ++ post) (pre ++ [t] ++ post)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`pre`, `[t;x]`, `[t]`, `post`, `1`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- metis_tac[terminal_prefix_splice_ok] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (gvs[asm_terminal_op_def, asm_reachable_marker_def] >>
                rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
    rpt gen_tac >> strip_tac >> qexists_tac `1` >> simp[] >>
    drule_all terminal_prefix_window >>
    disch_then (qspecl_then [`post`, `env`] strip_assume_tac) >>
    conj_tac >- (qpat_x_assum `!i a. _` (qspec_then `0` mp_tac) >> simp[]) >>
    rpt strip_tac >> qexists_tac `1` >> simp[])) >>
  simp[]
QED

Theorem prune_unreachable_prefix_transport_under[local]:
  ^single_site /\ ^transitive ==>
  !sfx d pfx.
    (d ==> ?pre t. pfx = pre ++ [t] /\ asm_terminal_op t) /\
    asm_static_wf (pfx ++ sfx) ==>
    ^transport (pfx ++ sfx) (pfx ++ FST (prune_unreachable_walk d sfx))
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p. tr p p` by
    (unabbrev_all_tac >> BETA_TAC >> gen_tac >> qexists_tac `1` >> simp[] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LE_ADD]) >>
  `!pre t x post. asm_terminal_op t /\ ~asm_reachable_marker x /\
    asm_static_wf (pre ++ [t;x] ++ post) ==>
    tr (pre ++ [t;x] ++ post) (pre ++ [t] ++ post)` by
    (unabbrev_all_tac >> match_mp_tac terminal_site_prefix_conditional >>
     first_assum ACCEPT_TAC) >>
  Induct >- simp[prune_unreachable_walk_def] >>
  rpt gen_tac >> strip_tac >> simp[prune_unreachable_walk_fst] >>
  IF_CASES_TAC
  >- (gvs[] >>
      `asm_static_wf (pre ++ t :: sfx)` by
        (mp_tac (Q.INST [`pfx` |-> `pre`, `rest` |-> `sfx`, `x` |-> `h`]
                       prune_one_refines) >>
         simp[asm_refines_def] >>
         qpat_x_assum `asm_static_wf _` mp_tac >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
         metis_tac[]) >>
      qpat_assum `!p q r. _` irule >>
      qexists_tac `pre ++ t :: sfx` >> conj_tac
      >- (qpat_assum `!pre t x post. _` (qspecl_then [`pre`, `t`, `h`, `sfx`] mp_tac) >>
          gvs[rich_listTheory.APPEND_ASSOC_CONS]) >>
      first_x_assum (qspecl_then [`T`, `pre ++ [t]`] mp_tac) >>
      simp[rich_listTheory.APPEND_ASSOC_CONS] >>
      disch_then irule >> qexistsl_tac [`pre`, `t`] >> simp[]) >>
  first_x_assum (qspecl_then [`asm_terminal_op h`, `pfx ++ [h]`] mp_tac) >>
  simp[rich_listTheory.APPEND_ASSOC_CONS] >>
  disch_then irule >> strip_tac >> qexistsl_tac [`pfx`, `h`] >> simp[]
QED

Theorem prune_unreachable_prefix_transport_conditional:
  ^single_site /\ ^transitive ==>
  !p. asm_static_wf p ==> ^transport p (FST (prune_unreachable_code p))
Proof
  strip_tac >> gen_tac >> simp[prune_unreachable_code_def] >>
  mp_tac prune_unreachable_prefix_transport_under >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`p`, `F`, `[]`] mp_tac) >> simp[]
QED
