structure entryLabelTacticsLib =
struct
open HolKernel boolLib bossLib

(* Walk the monadic code while each caller supplies its label rules. *)
fun label_tactics return_labels bind_labels ignore_bind_labels label_steps =
  let
    fun step rws =
      FIRST (label_steps @
        [irule bind_labels >> conj_tac,
         irule ignore_bind_labels >> conj_tac,
         FIRST_ASSUM MATCH_ACCEPT_TAC,
         disch_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC]) >>
      rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
      simp (return_labels :: rws)

    fun chain rws = rpt gen_tac >> simp (return_labels :: rws) >> rpt (step rws)
  in
    (step, chain)
  end
end
