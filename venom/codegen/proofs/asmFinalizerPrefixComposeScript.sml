Theory asmFinalizerPrefixCompose
Ancestors
  arithmetic asmOptimizer asmSymSem asmOptFinalizerCorrect asmOptNonemptyCompose
  asmOptPruneUnreachable asmOptMergeIszero asmOptMergeJumpdests
  asmOptPruneJumps asmOptInefficientJumps asmOptPruneUnused asmOptPeephole

(* A quotation abbreviation only: no logical transport constant is introduced. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
       a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
     ?m b. sym_steps q env m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp op /\
       (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
       MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
       FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)``;

Theorem prefix_transport_refl:
  !p. ^transport p p
Proof
  BETA_TAC >> gen_tac >> qexists_tac `1` >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (qexistsl_tac [`n`, `a`] >> simp[]) >>
  rpt strip_tac >> qexistsl_tac [`n`, `a`] >> simp[]
QED

Theorem prefix_transport_trans:
  !p q r. ^transport p q /\ ^transport q r ==> ^transport p r
Proof
  BETA_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `k1` strip_assume_tac)
    (qx_choose_then `k2` strip_assume_tac)) >>
  qexists_tac `k1 * (k2 + 1)` >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!env s n a. _ /\ sym_steps p _ _ _ = _ ==> _`
    (qspecl_then [`env`, `s`, `n`, `a`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >> conj_tac
  >- (qpat_assum `!env s n a. _ /\ sym_steps q _ _ _ = _ ==> _`
        (qspecl_then [`env`, `s`, `m`, `b`] mp_tac) >>
      (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
      qexistsl_tac [`m'`, `b'`] >> simp[] >>
      irule LESS_EQ_TRANS >> qexists_tac `k1 * (m + 1)` >>
      conj_tac >- simp[] >>
      pure_rewrite_tac[GSYM MULT_ASSOC] >> irule LESS_MONO_MULT2 >> simp[] >>
      irule LESS_EQ_TRANS >> qexists_tac `k2 * (m' + 1) + 1` >>
      simp[LEFT_ADD_DISTRIB]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!op. _ ==> ?m b. _` drule_all >>
  disch_then (qx_choosel_then [`m1`, `b1`] strip_assume_tac) >>
  qpat_assum `!env s n a. _ /\ sym_steps q _ _ _ = _ ==> _`
    (qspecl_then [`env`, `s`, `m1`, `b1`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  qpat_x_assum `!op. _ ==> ?m b. _` drule_all >>
  disch_then (qx_choosel_then [`m2`, `b2`] strip_assume_tac) >>
  qexistsl_tac [`m2`, `b2`] >> gvs[]
QED

Theorem accepted_finalizers_prefix_transport_conditional:
  (!p. asm_static_wf p ==> ^transport p (FST (merge_iszero p))) /\
  (!p. asm_static_wf p ==> ^transport p (FST (prune_inefficient_jumps p))) /\
  (!p. asm_static_wf p ==> ^transport p (FST (optimize_inefficient_jumps p))) /\
  (!p q c. asm_static_wf p /\ stack_peephole_opts p = SOME(q,c) ==>
     ^transport p q) /\
  (!p. asm_static_wf p ==> ^transport p (FST (merge_jumpdests p))) /\
  (!p. asm_static_wf p ==> ^transport p (FST (prune_unreachable_code p))) /\
  (!p. asm_static_wf p ==> ^transport p (FST (prune_unused_jumpdests p))) ==>
  !fin rp p q. fin IN accepted_finalizers /\ fin rp p = SOME q /\
    asm_static_wf p ==> ^transport p q
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p q r. tr p q /\ tr q r ==> tr p r`
    by (unabbrev_all_tac >> MATCH_ACCEPT_TAC prefix_transport_trans) >>
  `!p. tr p p`
    by (unabbrev_all_tac >> MATCH_ACCEPT_TAC prefix_transport_refl) >>
  `!p q r. (asm_static_wf p ==> asm_static_wf q /\ tr p q) /\
            (asm_static_wf q ==> asm_static_wf r /\ tr q r) ==>
            (asm_static_wf p ==> asm_static_wf r /\ tr p r)`
    by metis_tac[] >>
  qspec_then `(\p q. asm_static_wf p ==> asm_static_wf q /\ tr p q)`
    mp_tac optimize_round_relation >> BETA_TAC >>
  (impl_tac >- (rpt conj_tac >> rpt gen_tac >> strip_tac >>
    metis_tac[asm_refines_def, prune_unreachable_code_refines,
      merge_iszero_refines, merge_jumpdests_refines,
      prune_inefficient_jumps_refines, optimize_inefficient_jumps_refines,
      prune_unused_jumpdests_refines, stack_peephole_opts_refines])) >>
  strip_tac >>
  qspec_then `(\p q. asm_static_wf p ==> asm_static_wf q /\ tr p q)`
    mp_tac optimize_rounds_relation >> BETA_TAC >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qpat_x_assum `!n p q. optimize_assembly_rounds _ _ = _ ==> _` mp_tac >>
  qpat_x_assum `!p. tr p p` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 2 strip_tac >>
  rw[accepted_finalizers_def] >> gvs[] >>
  gvs[asm_opt_finalizer_def, optimize_assembly_def] >>
  Cases_on `rp.rpol_final_assembly = FAP_Optimize` >> gvs[] >>
  metis_tac[]
QED
