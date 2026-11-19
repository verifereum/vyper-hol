Theory focusJointChainBound
Ancestors
  frameJointTrace list arithmetic

(* A zero-assembly edge must spend rank; a positive edge can reset it.
   Costs are indexed by occurrences in this actual joint chain. *)
Theorem focus_joint_chain_length_bound:
  !evs q qs r costs.
    joint_chain ctx q evs qs r /\
    EVERY (\u. rank u <= bound) (q::qs) /\
    LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
      costs (ZIP (q::qs, qs)) ==>
    LENGTH evs <= (bound + 1) * SUM costs + rank q
Proof
  Induct_on `evs` >- simp[] >> rpt gen_tac >>
  Cases_on `qs` >- simp[joint_chain_def] >>
  Cases_on `costs` >- simp[] >>
  rename1 `joint_chain ctx q (_::evs) (next::rest_qs) r` >>
  rename1 `LIST_REL _ (cost::rest_costs) _` >>
  simp[joint_chain_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `!costs. _` (qspec_then `rest_costs` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `cost` >> fs[SUM, LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED
