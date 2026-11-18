(* Complete the byte-copy replay at the actual successful CODECOPY edge. *)
Theory gasFocusLowerDloadBytesCompletion
Ancestors
  lowerDloadMacroBoundary lowerDloadPhaseBoundary lowerDloadSafetyKernel
  lowerDloadPtrPhase ptrDiscipline venomExecSemantics venomInst venomState list

Theorem ld_focus_bytes_actual_completion:
  a.inst_opcode = ADD /\ a.inst_operands = [off; Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst; Var av; sz] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn [a;c] p 1 t0 t /\
  step_inst fuel C' c t = OK u ==>
  ?w x y d k.
    step_inst 0 C' a t0 = OK w /\ t = (w with vs_inst_idx := SUC p) /\
    eval_operand off t0 = SOME x /\ eval_operand (Label "code_end") t0 = SOME y /\
    eval_operand dst t0 = SOME d /\ eval_operand sz t0 = SOME k /\
    (!un0. ld_target_prefix C' [a;c] t0 un0 2
       (u with vs_inst_idx := SUC t.vs_inst_idx)
       (step_taint c t u (step_taint a t0 w un0))) /\
    (!pf PH H0 un0 H un. dload_prefix_match pf C' PH [a;c] 1 t0 H0 un0 t H un ==>
       H = step_prov PH H0 a w /\ un = step_taint a t0 w un0 /\
       dload_prefix_match pf C' PH [a;c] 2 t0 H0 un0
         (u with vs_inst_idx := SUC t.vs_inst_idx) (step_prov PH H c u) (step_taint c t u un))
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  simp[ld_prefix_zero] >> disch_then (qx_choose_then `w` strip_assume_tac) >>
  `!un0. ld_target_prefix C' [a;c] t0 un0 1 t (step_taint a t0 w un0)` by
    (gen_tac >>
     simp[Once (ld_target_prefix_step_iff |> Q.INST [`n` |-> `0`] |> SRULE []),
          ld_target_prefix_empty] >>
     qexistsl_tac [`w`,`0`] >> simp[]) >>
  `!un0. ld_target_prefix C' [a;c] t0 un0 2
      (u with vs_inst_idx := SUC t.vs_inst_idx)
      (step_taint c t u (step_taint a t0 w un0))` by
    (qx_gen_tac `un0` >>
     once_rewrite_tac [ld_target_prefix_step_iff |> Q.INST [`n` |-> `1`] |> SRULE []] >>
     qexistsl_tac [`t`,`step_taint a t0 w un0`,`u`,`fuel`] >> gvs[]) >>
  `?x y d k. eval_operand off t0 = SOME x /\
      eval_operand (Label "code_end") t0 = SOME y /\
      eval_operand dst t0 = SOME d /\ eval_operand sz t0 = SOME k` by
    (drule_all ld_bytes_completed_prefix >> disch_then (assume_tac o SRULE []) >>
     qpat_x_assum `!un0. ld_target_prefix _ _ _ un0 2 _ _` (qspec_then `ARB` mp_tac) >>
     simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`w`,`x`,`y`,`d`,`k`] >> simp[] >>
  rpt gen_tac >> disch_tac >>
  `step_inst pf C' a t0 = OK w /\ step_inst pf C' c t = OK u` by
    gvs[step_inst_non_invoke] >>
  `H = step_prov PH H0 a w /\ un = step_taint a t0 w un0` by
    (qpat_x_assum `dload_prefix_match _ _ _ _ 1 _ _ _ _ _ _` mp_tac >>
     simp[dload_prefix_first]) >>
  gvs[] >>
  drule_all (dload_prefix_extend |> Q.INST [`k` |-> `1`, `emitted` |-> `[a;c]`] |>
    SRULE []) >> simp[]
QED
