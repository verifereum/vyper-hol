Theory gasFocusBoundedFrontier
Ancestors
  focusFrontierBudget frameJointTrace list arithmetic

(* All-prefix form of the bounded search. The concrete fold supplies the
   cost certificates from the same EVM run. *)
Theorem focus_bounded_frontier_stops:
  joint_initial vs0 ctx q0 /\ frontier q0 [] [] /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs /\
    ~stop q evs qs ==>
    ?ev next. joint_transition ctx q ev next /\
      frontier next (evs ++ [ev]) (qs ++ [next])) /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs ==>
    ?costs.
      EVERY (\u. rank u <= (bound:num)) (q0::qs) /\
      LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
        costs (ZIP (q0::qs, qs)) /\ SUM costs <= max_cost) ==>
  ?q evs qs. joint_trace vs0 ctx q0 evs qs q /\
    frontier q evs qs /\ stop q evs qs
Proof
  strip_tac >>
  mp_tac focus_frontier_budget_stops >>
  (impl_tac >- metis_tac[]) >>
  metis_tac[]
QED
