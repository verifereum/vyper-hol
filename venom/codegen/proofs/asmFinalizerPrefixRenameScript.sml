Theory asmFinalizerPrefixRename
Ancestors
  list asmOptimizer asmSymSem asmWf asmOptMergeJumpdests asmFinalizerPrefixCompose

(* Lift any reflexive, transitive one-site relation through the syntactic walk. *)
Theorem merge_jumpdests_walk_relation[local]:
  !R. (!p. R p p) /\
      (!p q r. R p q /\ R q r ==> R p r) /\
      (!pre x y next third more.
        (next = AsmLabel y /\ y <> x \/
         next = AsmPushLabel y /\ third = AsmOp "JUMP") ==>
        R (pre ++ AsmLabel x :: next :: third :: more)
          (MAP (rename_push_label x y)
            (pre ++ AsmLabel x :: next :: third :: more))) ==>
      !n done rest changed. LENGTH rest = n ==>
        R (REVERSE done ++ rest) (FST (merge_jumpdests_walk done rest changed))
Proof
  gen_tac >> strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  `!d r c. LENGTH r < LENGTH rest ==>
      R (REVERSE d ++ r) (FST (merge_jumpdests_walk d r c))` by metis_tac[] >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  Cases_on `rest` >- simp[merge_jumpdests_walk_def] >>
  rename1 `h :: t` >> Cases_on `t` >- simp[merge_jumpdests_walk_def] >>
  rename1 `h :: next :: t` >> Cases_on `t` >- simp[merge_jumpdests_walk_def] >>
  rename1 `h :: next :: third :: more` >>
  qpat_x_assum `LENGTH _ = n` kall_tac >>
  Cases_on `?x. h = AsmLabel x`
  >- (pop_assum (qx_choose_then `x` SUBST_ALL_TAC) >>
      Cases_on `?y. next = AsmLabel y /\ y <> x \/
                    next = AsmPushLabel y /\ third = AsmOp "JUMP"`
      >- (pop_assum (qx_choose_then `y` assume_tac) >>
          `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
           merge_jumpdests_walk
             (AsmLabel x :: MAP (rename_push_label x y) done)
             (MAP (rename_push_label x y) (next :: third :: more))
             (changed \/ push_label_used x
               (REVERSE done ++ AsmLabel x :: next :: third :: more))`
            by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
                qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[rename_push_label_def]) >>
          pop_assum SUBST1_TAC >>
          qpat_x_assum `!p q r. _` irule >>
          qexists_tac `MAP (rename_push_label x y)
                        (REVERSE done ++ AsmLabel x :: next :: third :: more)` >>
          conj_tac >- metis_tac[] >>
          qmatch_goalsub_abbrev_tac `merge_jumpdests_walk _ _ cc` >>
          qpat_x_assum `!d r c. _`
            (qspecl_then [`AsmLabel x :: MAP (rename_push_label x y) done`,
                          `MAP (rename_push_label x y) (next :: third :: more)`,
                          `cc`] mp_tac) >>
          simp[MAP_REVERSE, rename_push_label_def] >>
          rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
      `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
       merge_jumpdests_walk (AsmLabel x :: done) (next :: third :: more) changed`
        by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
            Cases_on `next` >> gvs[] >> rw[] >> gvs[]) >>
      pop_assum SUBST1_TAC >>
      qpat_x_assum `!d r c. _`
        (qspecl_then [`AsmLabel x :: done`, `next :: third :: more`, `changed`] mp_tac) >>
      simp[] >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  `merge_jumpdests_walk done (h :: next :: third :: more) changed =
   merge_jumpdests_walk (h :: done) (next :: third :: more) changed`
    by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
        Cases_on `h` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!d r c. _`
    (qspecl_then [`h :: done`, `next :: third :: more`, `changed`] mp_tac) >>
  simp[] >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* Quotation abbreviations expand in the exported statement; no logical constants. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m + 1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
      ?m b. sym_steps q env m (sym_init s) = SymOK b /\
        b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
        b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

Theorem merge_jumpdests_prefix_transport_conditional:
  (!pre x y next third more.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf (pre ++ AsmLabel x :: next :: third :: more) ==>
    ^transport (pre ++ AsmLabel x :: next :: third :: more)
      (MAP (rename_push_label x y)
        (pre ++ AsmLabel x :: next :: third :: more))) /\
  (!p q r. ^transport p q /\ ^transport q r ==> ^transport p r) ==>
  !p. asm_static_wf p ==> ^transport p (FST (merge_jumpdests p))
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p. tr p p` by (unabbrev_all_tac >> MATCH_ACCEPT_TAC prefix_transport_refl) >>
  qspec_then `(\p q. asm_static_wf p ==> asm_static_wf q /\ tr p q)`
    mp_tac merge_jumpdests_walk_relation >> BETA_TAC >>
  (impl_tac >- (rpt conj_tac
    >- simp[]
    >- metis_tac[] >>
    rpt gen_tac >> disch_tac >> disch_tac >> conj_tac
    >- (irule rename_static_wf >>
        simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        (gvs[MEM, MEM_APPEND])) >>
    qpat_x_assum `Abbrev _` kall_tac >> metis_tac[])) >>
  disch_tac >> gen_tac >>
  qpat_x_assum `!n done rest changed. _`
    (qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac) >>
  simp[merge_jumpdests_def]
QED
