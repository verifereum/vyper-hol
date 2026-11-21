(* Goal-directed scalar representation tactics for the Log consumers.
   No theorem values are manufactured or cached here. *)
structure logWidenTacticsLib =
struct
open HolKernel boolLib bossLib
open listTheory vyperEventArgCompatTheory

fun compatible_cases g = (
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def]) g

fun topics_eq scalar g = (
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >> Cases_on `flags` >> Cases_on `vals` >>
  simp[vyperEventTheory.encode_indexed_event_topics_def] >>
  rename1 `encode_indexed_event_topics (flg::_) _ _` >>
  Cases_on `flg` >> simp[vyperEventTheory.encode_indexed_event_topics_def] >>
  drule_all scalar >> simp[]) g

fun abi_eq scalar g = (
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >> drule_all scalar >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  Cases_on `vals` >> simp[]) g

end
