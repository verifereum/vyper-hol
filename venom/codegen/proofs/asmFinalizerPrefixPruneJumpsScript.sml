Theory asmFinalizerPrefixPruneJumps
Ancestors
  asmFinalizerPrefixSplice asmOptPruneJumps asmSplice asmSymPc
  finalizerContract asmSymSem asmOptimizer asmWf

(* S, U and T are quotation abbreviations, not logical definitions. *)
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

Theorem jump_to_next_prefix_transport_conditional[local]:
  ^single_site ==> !pre x rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) ==>
    ^transport (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest)
               (pre ++ AsmLabel x :: rest)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then
    [`pre`, `[AsmPushLabel x; AsmOp "JUMP"]`, `[]`, `AsmLabel x :: rest`, `2`]
    mp_tac) >>
  (impl_tac >- (
    simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
         symbolResolveTheory.asm_inst_size_def] >>
    rpt gen_tac >> strip_tac >>
    qexists_tac `2` >> simp[] >>
    drule_all (SIMP_RULE bool_ss [LET_THM] jump_delete_prefix_chunk) >> strip_tac >> conj_tac
    >- metis_tac[] >>
    rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `0` >>
    simp[sym_steps_def, splice_pc_def, sym_with_pc_def,
         sym_state_component_equality, asmSemTheory.asm_state_component_equality])) >>
  simp[]
QED

Theorem prune_jumps_prefix_transport_under[local]:
  ^single_site /\ ^transitive ==>
  !sfx pre. asm_static_wf (pre ++ sfx) ==>
    ^transport (pre ++ sfx) (pre ++ FST (prune_inefficient_jumps sfx))
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p. tr p p` by
    (unabbrev_all_tac >> BETA_TAC >> gen_tac >> qexists_tac `1` >> simp[] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LE_ADD]) >>
  `!pre x rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) ==>
    tr (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest)
       (pre ++ AsmLabel x :: rest)` by
    (unabbrev_all_tac >> match_mp_tac jump_to_next_prefix_transport_conditional >>
     first_assum ACCEPT_TAC) >>
  ho_match_mp_tac prune_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[prune_inefficient_jumps_def]
  >- simp[prune_inefficient_jumps_def]
  >- simp[prune_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >> simp[prune_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> rpt strip_tac >>
      first_x_assum (qspec_then `pre ++ [a]` mp_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `a` >> gvs[asm_jump_to_next_def] >>
  Cases_on `c` >> gvs[] >> rpt strip_tac >>
  rename1 `AsmPushLabel lbl` >>
  `asm_static_wf (pre ++ AsmLabel lbl :: rest)` by
    (mp_tac (Q.INST [`pfx` |-> `pre`,
                    `pat` |-> `[AsmPushLabel lbl; AsmOp "JUMP"]`,
                    `repl` |-> `[]`, `sfx` |-> `AsmLabel lbl :: rest`]
                   asm_splice_window_refines) >>
     simp[asm_splice_ok_def, jump_to_next_window_refines, is_data_inst_def,
          asm_label_refs_def, symbolResolveTheory.asm_inst_size_def,
          asm_refines_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
     disch_then drule >> simp[]) >>
  metis_tac[listTheory.APPEND, listTheory.APPEND_ASSOC]
QED

Theorem prune_jumps_prefix_transport_conditional:
  ^single_site /\ ^transitive ==>
  !p. asm_static_wf p ==> ^transport p (FST (prune_inefficient_jumps p))
Proof
  strip_tac >> gen_tac >>
  mp_tac prune_jumps_prefix_transport_under >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`p`, `[]`] mp_tac) >> simp[]
QED
