(* TOP-LEVEL: charges track successful source argument evaluation in AST
   order. No native execution or saved-value relation is built into this
   source-only resource bound. *)
Theory logArgumentCharges
Ancestors
  logArgumentSourceExecution vyperInterpreter vyperState list pair arithmetic

Definition log_argument_charges_def:
  log_argument_charges charge cx [] es values es' total =
    (values = [] /\ es' = es /\ total = 0) /\
  log_argument_charges charge cx (e::suffix) es values es' total =
    (?v middle vs rest_charge.
      eval_argument cx e es = (INL v,middle) /\
      log_argument_charges charge cx suffix middle vs es' rest_charge /\
      values = v::vs /\ total = charge e es + rest_charge)
End

Theorem log_argument_charges_source:
  !args charge cx es values es' total.
    log_argument_charges charge cx args es values es' total ==>
    eval_exprs cx args es = (INL values,es')
Proof
  Induct_on `args`
  >- simp[log_argument_charges_def, Once evaluate_def, return_def] >>
  rpt gen_tac >> simp_tac bool_ss [log_argument_charges_def] >>
  disch_then (qx_choose_then `v` (qx_choose_then `middle` (qx_choose_then `vs`
    (qx_choose_then `rest_charge` strip_assume_tac)))) >>
  simp_tac bool_ss [eval_exprs_cons_success] >>
  qexistsl_tac [`v`, `middle`, `vs`] >> simp[] >> first_x_assum irule >> goal_assum drule
QED

Theorem eval_exprs_argument_charges:
  !args charge cx es values es'.
    eval_exprs cx args es = (INL values,es') ==>
    ?total. log_argument_charges charge cx args es values es' total
Proof
  Induct_on `args`
  >- simp[Once evaluate_def, return_def, log_argument_charges_def] >>
  rpt gen_tac >> rename1 `eval_exprs cx (e::suffix) es = (INL values,es')` >>
  simp_tac bool_ss [eval_exprs_cons_success] >>
  disch_then (qx_choose_then `v` (qx_choose_then `middle` (qx_choose_then `vs` strip_assume_tac))) >>
  qpat_x_assum `!charge cx es values es'. _`
    (qspecl_then [`charge`, `cx`, `middle`, `vs`, `es'`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> disch_then (qx_choose_then `rest_charge` ASSUME_TAC) >>
  qexists_tac `charge e es + rest_charge` >> simp_tac bool_ss [log_argument_charges_def] >>
  qexistsl_tac [`v`, `middle`, `vs`, `rest_charge`] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source Log argument charges: " ^ name)
  end) (DB.thms "logArgumentCharges")
