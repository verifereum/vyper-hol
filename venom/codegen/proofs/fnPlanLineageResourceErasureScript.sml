Theory fnPlanLineageResourceErasure
Ancestors
  stackPlanOps list finite_map

(* Forget only address payloads, not stack actions or symbolic cells. *)
Definition erase_spill_address_def:
  erase_spill_address op =
    case op of SOSpill n => SOSpill 0 | SORestore n => SORestore 0 | _ => op
End

Definition stack_domain_eq_def:
  stack_domain_eq p q <=>
    p.ps_stack = q.ps_stack /\ FDOM p.ps_spilled = FDOM q.ps_spilled
End

Theorem do_spill_tos_resource_erasure:
  !p q os p' ts q'.
    stack_domain_eq p q /\ do_spill_tos p = (os,p') /\
    do_spill_tos q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> simp[do_spill_tos_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[stack_domain_eq_def, erase_spill_address_def]
QED

Theorem do_restore_resource_erasure:
  !op p q os p' ts q'.
    stack_domain_eq p q /\ do_restore op p = (os,p') /\
    do_restore op q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> simp[stack_domain_eq_def, do_restore_def] >>
  Cases_on `FLOOKUP p.ps_spilled op` >>
  Cases_on `FLOOKUP q.ps_spilled op` >>
  strip_tac >> gvs[stack_domain_eq_def, erase_spill_address_def] >>
  fs[FLOOKUP_DEF]
QED

Theorem do_spill_at_resource_erasure:
  !d p q os p' ts q'.
    stack_domain_eq p q /\ do_spill_at d p = (os,p') /\
    do_spill_at d q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def] >>
      MATCH_ACCEPT_TAC do_spill_tos_resource_erasure) >>
  simp[do_spill_at_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `stack_domain_eq
    (p with ps_stack := stack_swap d p.ps_stack)
    (q with ps_stack := stack_swap d q.ps_stack)` by
    fs[stack_domain_eq_def] >>
  drule_all do_spill_tos_resource_erasure >>
  gvs[erase_spill_address_def]
QED

Theorem restore_spilled_plan_resource_erasure:
  !operands p q os p' ts q'.
    stack_domain_eq p q /\ restore_spilled_plan operands p = (os,p') /\
    restore_spilled_plan operands q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  Induct >- simp[restore_spilled_plan_def] >>
  rpt gen_tac >> simp[restore_spilled_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all do_restore_resource_erasure >> strip_tac >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  gvs[]
QED

Theorem reorder_cost_resource_erasure:
  !os. reorder_cost (MAP erase_spill_address os) = reorder_cost os
Proof
  Induct >> simp[reorder_cost_def] >>
  Cases_on `h` >> gvs[erase_spill_address_def, reorder_cost_def]
QED
