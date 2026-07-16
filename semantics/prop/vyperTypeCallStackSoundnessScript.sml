(*
 * Checked call-stack and callable graph invariants.
 *)

Theory vyperTypeCallStackSoundness
Ancestors
  list rich_list relation vyperTypeCallGraphSoundness

(* ===== Generic stack-path and relation closure infrastructure ===== *)

Definition call_stack_follows_def:
  call_stack_follows R [] = T /\
  call_stack_follows R [current] = T /\
  call_stack_follows R (current::parent::rest) =
    (R parent current /\ call_stack_follows R (parent::rest))
End

Theorem RTC_then_R_TC:
  RTC R x y /\ R y z ==> TC R x z
Proof
  metis_tac[RTC_CASES_TC, TC_RULES]
QED

Theorem call_stack_follows_push:
  call_stack_follows R (owner::ancestors) /\
  R owner callee ==>
  call_stack_follows R (callee::owner::ancestors)
Proof
  simp[call_stack_follows_def]
QED

Theorem call_stack_member_reaches_head:
  call_stack_follows R (owner::ancestors) /\
  MEM node (owner::ancestors) ==>
  RTC R node owner
Proof
  qid_spec_tac `owner` >>
  Induct_on `ancestors`
  >- simp[call_stack_follows_def] >>
  simp[call_stack_follows_def] >>
  rpt strip_tac >>
  gvs[] >>
  first_x_assum (qspec_then `h` mp_tac) >>
  simp[] >>
  metis_tac[RTC_RULES_RIGHT1]
QED

Theorem acyclic_stack_target_not_mem:
  irreflexive (TC R) /\
  call_stack_follows R (owner::ancestors) /\
  R owner callee ==>
  ~MEM callee (owner::ancestors)
Proof
  rpt strip_tac >>
  drule_all call_stack_member_reaches_head >>
  disch_then assume_tac >>
  drule_all RTC_then_R_TC >>
  disch_then assume_tac >>
  gvs[irreflexive_def]
QED

(* ===== Ownership of extracted internal calls ===== *)

Definition calls_follow_call_graph_def:
  calls_follow_call_graph edges owner calls <=>
    EVERY (call_edge_rel edges owner) calls
End

Theorem calls_follow_call_graph_nil[simp]:
  calls_follow_call_graph edges owner []
Proof
  simp[calls_follow_call_graph_def]
QED

Theorem calls_follow_call_graph_cons[simp]:
  calls_follow_call_graph edges owner (callee::calls) <=>
  call_edge_rel edges owner callee /\
  calls_follow_call_graph edges owner calls
Proof
  simp[calls_follow_call_graph_def]
QED

Theorem calls_follow_call_graph_append[simp]:
  calls_follow_call_graph edges owner (xs ++ ys) <=>
  calls_follow_call_graph edges owner xs /\
  calls_follow_call_graph edges owner ys
Proof
  simp[calls_follow_call_graph_def, EVERY_APPEND]
QED

Theorem calls_follow_call_graph_DROP:
  calls_follow_call_graph edges owner xs ==>
  calls_follow_call_graph edges owner (DROP n xs)
Proof
  simp[calls_follow_call_graph_def, EVERY_DROP]
QED
