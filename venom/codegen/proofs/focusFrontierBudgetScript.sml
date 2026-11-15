Theory focusFrontierBudget
Ancestors
  gasFocusPrefixDriver frameJointTrace list arithmetic

(* Continuation and cost certificates are needed only through the finite
   search horizon. The returned trace carries its explicit length bound. *)
Theorem focus_frontier_budget_stops:
  joint_initial vs0 ctx q0 /\ frontier q0 [] [] /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs /\
    LENGTH evs <= (bound + 1) * max_cost + rank q0 /\
    ~stop q evs qs ==>
    ?ev next. joint_transition ctx q ev next /\
      frontier next (evs ++ [ev]) (qs ++ [next])) /\
  (!q evs qs.
    joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs /\
    LENGTH evs <= SUC ((bound + 1) * max_cost + rank q0) ==>
    ?costs.
      EVERY (\u. rank u <= bound) (q0::qs) /\
      LIST_REL (\cost pair. 0 < cost \/ rank (SND pair) < rank (FST pair))
        costs (ZIP (q0::qs, qs)) /\ SUM costs <= max_cost) ==>
  ?q evs qs. joint_trace vs0 ctx q0 evs qs q /\
    frontier q evs qs /\ stop q evs qs /\
    LENGTH evs <= (bound + 1) * max_cost + rank q0
Proof
  cheat
QED
