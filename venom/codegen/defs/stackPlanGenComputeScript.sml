(* Evaluator-friendly, tail-recursive entry points for stack planning. *)

Theory stackPlanGenCompute
Ancestors stackPlanGen

Definition reduce_depth_plan_acc_def:
  reduce_depth_plan_acc 0 target_ops target_op f target_len ps acc =
    (REVERSE acc, ps) /\
  reduce_depth_plan_acc (SUC fuel) target_ops target_op f target_len ps acc =
    if f + 1 < target_len then (REVERSE acc, ps)
    else
      case stack_get_unfixed_depth target_op f target_len ps.ps_stack of
        NONE => (REVERSE acc, ps)
      | SOME dist =>
          if dist ≤ 16 then (REVERSE acc, ps)
          else
            case select_spill_candidate ps.ps_stack target_ops dist target_len of
              NONE => (REVERSE acc, ps)
            | SOME cand_dist =>
                let (spill_ops,ps') = do_spill_at cand_dist ps in
                reduce_depth_plan_acc fuel target_ops target_op f target_len
                  ps' (REVERSE spill_ops ++ acc)
End

Theorem reduce_depth_plan_acc_eq:
  ∀fuel ps acc.
    reduce_depth_plan_acc fuel target_ops target_op f target_len ps acc =
    let (ops,ps') =
      reduce_depth_plan fuel target_ops target_op f target_len ps in
    (REVERSE acc ++ ops,ps')
Proof
  Induct >>
  simp[reduce_depth_plan_acc_def, stackPlanOpsTheory.reduce_depth_plan_def] >>
  rpt gen_tac >>
  simp[Once reduce_depth_plan_acc_def,
       Once stackPlanOpsTheory.reduce_depth_plan_def, LET_THM] >>
  rpt (CASE_TAC >> gvs[listTheory.REVERSE_APPEND]) >>
  Cases_on `do_spill_at x' ps` >> gvs[listTheory.REVERSE_APPEND] >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len r` >>
  gvs[]
QED

Theorem reduce_depth_plan_compute:
  reduce_depth_plan fuel target_ops target_op f target_len ps =
    reduce_depth_plan_acc fuel target_ops target_op f target_len ps []
Proof
  mp_tac (Q.SPECL [`fuel`,`ps`,`[]`] reduce_depth_plan_acc_eq) >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len ps` >>
  simp[]
QED

Definition generate_block_insts_plan_acc_def:
  generate_block_insts_plan_acc liveness dfg cfg fn bb_label is_halting
      n_params block_len i [] ps acc =
    SOME (REVERSE acc, ps) /\
  generate_block_insts_plan_acc liveness dfg cfg fn bb_label is_halting
      n_params block_len i (inst::rest) ps acc =
    let next_live =
      if rest = [] then live_vars_at liveness bb_label block_len
      else live_vars_at liveness bb_label (i + n_params + 1) in
    let next_is_term =
      case rest of
        [] => F
      | next_i::_ => is_terminator next_i.inst_opcode in
    case generate_inst_plan liveness dfg cfg fn inst next_live is_halting
           next_is_term bb_label ps of
      NONE => NONE
    | SOME (step_ops,ps') =>
        generate_block_insts_plan_acc liveness dfg cfg fn bb_label
          is_halting n_params block_len (i + 1) rest ps'
          (REVERSE step_ops ++ acc)
End

Theorem generate_block_insts_plan_acc_eq:
  ∀insts i ps acc.
    generate_block_insts_plan_acc liveness dfg cfg fn bb_label is_halting
      n_params block_len i insts ps acc =
    OPTION_MAP (λ(ops,ps'). (REVERSE acc ++ ops,ps'))
      (generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
        n_params block_len i insts ps)
Proof
  Induct_on `insts`
  >- simp[generate_block_insts_plan_acc_def,
          stackPlanGenTheory.generate_block_insts_plan_def]
  >> rpt gen_tac >> Cases_on `insts` >>
     simp[generate_block_insts_plan_acc_def,
          stackPlanGenTheory.generate_block_insts_plan_def,
          LET_THM] >>
     CASE_TAC >> gvs[generate_block_insts_plan_acc_def,
       stackPlanGenTheory.generate_block_insts_plan_def] >>
     TRY (Cases_on `x`) >> gvs[listTheory.REVERSE_APPEND] >>
     rpt (CASE_TAC >> gvs[listTheory.REVERSE_APPEND])
QED

Theorem generate_block_insts_plan_compute:
  generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
      n_params block_len i insts ps =
    generate_block_insts_plan_acc liveness dfg cfg fn bb_label is_halting
      n_params block_len i insts ps []
Proof
  mp_tac (Q.SPECL [`insts`,`i`,`ps`,`[]`]
    generate_block_insts_plan_acc_eq) >>
  Cases_on `generate_block_insts_plan liveness dfg cfg fn bb_label
    is_halting n_params block_len i insts ps` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

(* Successful fuel-bounded DFS evaluation is sound for the normative
   well-founded planner. *)
Theorem generate_plan_fuel_some:
  ∀fuel.
    (∀liveness dfg cfg fn worklist visited ps result.
       generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
         SOME result ⇒
       generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
         SOME result) ∧
    (∀liveness dfg cfg fn saved_stack saved_spilled succs visited ps result.
       generate_succs_plan_fuel fuel liveness dfg cfg fn saved_stack
         saved_spilled succs visited ps = SOME result ⇒
       generate_succs_plan liveness dfg cfg fn saved_stack saved_spilled
         succs visited ps = SOME result)
Proof
  Induct
  >- simp[stackPlanGenTheory.generate_fn_plan_aux_fuel_def]
  >> conj_tac >> rpt gen_tac
  >- (Cases_on `worklist` >>
      simp[Once stackPlanGenTheory.generate_fn_plan_aux_fuel_def,
           Once stackPlanGenTheory.generate_fn_plan_aux_def] >>
      rpt (CASE_TAC >> gvs[]) >>
      TRY (qpat_x_assum
        `∀l d c f w v p r. generate_fn_plan_aux_fuel fuel l d c f w v p = SOME r ⇒ _`
        (drule_all_then assume_tac)) >>
      TRY (qpat_x_assum
        `∀l d c f ss sp su v p r. generate_succs_plan_fuel fuel l d c f ss sp su v p = SOME r ⇒ _`
        (drule_all_then assume_tac)) >>
      gvs[])
  >> Cases_on `succs` >>
     simp[Once stackPlanGenTheory.generate_fn_plan_aux_fuel_def,
          Once stackPlanGenTheory.generate_fn_plan_aux_def] >>
     rpt (CASE_TAC >> gvs[]) >>
     TRY (qpat_x_assum
       `∀l d c f w v p r. generate_fn_plan_aux_fuel fuel l d c f w v p = SOME r ⇒ _`
       (drule_all_then assume_tac)) >>
     TRY (qpat_x_assum
       `∀l d c f ss sp su v p r. generate_succs_plan_fuel fuel l d c f ss sp su v p = SOME r ⇒ _`
       (drule_all_then assume_tac)) >>
     gvs[]
QED
