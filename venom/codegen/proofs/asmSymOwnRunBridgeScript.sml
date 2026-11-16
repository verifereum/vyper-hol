(* TOP-LEVEL: asm_sym_run_own_backward_from_step.
   The fetched-step interface keeps the own-code invariant explicit, so
   this fuel induction is independent of the individual opcode proofs. *)
Theory asmSymOwnRunBridge
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem symbolResolve list

Theorem asm_sym_run_own_backward_from_step:
  (!c t. asm_sym_rel p env c t /\ c.as_code = own /\ c.as_pc < LENGTH p ==>
     asm_sym_step_rel p env
       (sym_step_own p env own (EL c.as_pc p) t)
       (asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
          (EL c.as_pc p) c) /\
     (!c'. asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
              (EL c.as_pc p) c = AsmOK c' ==> c'.as_code = own)) ==>
  !fuel cs ss.
    asm_sym_rel p env cs ss /\ cs.as_code = own /\
    sym_terminal (sym_run_own p env own fuel ss) ==>
    ?n. sym_result_rel (sym_run_own p env own fuel ss)
      (asm_result_sym (asm_steps (SND (compute_label_offsets p))
         (build_offset_to_pc p) p n cs))
Proof
  disch_then (mk_asm "step") >> Induct_on `fuel`
  >- simp[Once sym_run_own_def, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_sym_rel_pc >> strip_tac >>
  Cases_on `cs.as_pc < LENGTH p`
  >- (asm "step" (qspecl_then [`cs`, `ss`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `sym_terminal _` mp_tac >>
      simp[Once sym_run_own_def] >>
      Cases_on `sym_step_own p env own (EL cs.as_pc p) ss` >>
      simp[sym_terminal_def]
      >- (strip_tac >> gvs[asm_sym_step_rel_def] >>
          first_x_assum drule_all >> strip_tac >>
          qexists_tac `SUC n` >>
          simp[asm_steps_def, Once sym_run_own_def]) >>
      gvs[asm_sym_step_rel_def] >>
      qexists_tac `SUC 0` >>
      simp[asm_steps_def, Once sym_run_own_def,
           asm_result_sym_def, sym_result_rel_def]) >>
  qpat_x_assum `sym_terminal _` mp_tac >>
  simp[Once sym_run_own_def, sym_terminal_def]
QED
