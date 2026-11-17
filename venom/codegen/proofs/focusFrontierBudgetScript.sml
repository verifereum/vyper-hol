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
  strip_tac >> spose_not_then assume_tac >>
  qabbrev_tac `H = (bound + 1) * max_cost + rank q0` >>
  `!n. n <= SUC H ==> ?q evs qs.
     joint_trace vs0 ctx q0 evs qs q /\ frontier q evs qs /\
     LENGTH evs = n` by
    (Induct
     >- (strip_tac >> qexistsl_tac [`q0`, `[]`, `[]`] >>
         simp[joint_trace_def, joint_chain_def]) >>
     strip_tac >>
     `n <= SUC H` by decide_tac >>
     first_x_assum drule >>
     disch_then (qx_choosel_then [`q`, `evs`, `qs`] strip_assume_tac) >>
     `LENGTH evs <= H` by decide_tac >>
     `~stop q evs qs` by metis_tac[] >>
     qpat_x_assum `!q evs qs. _ ==> ?ev next. _` drule_all >>
     disch_then (qx_choosel_then [`ev`, `next`] strip_assume_tac) >>
     qexistsl_tac [`next`, `evs ++ [ev]`, `qs ++ [next]`] >>
     simp[] >> metis_tac[joint_trace_snoc]) >>
  pop_assum (qspec_then `SUC H`
    (qx_choosel_then [`q`, `evs`, `qs`] strip_assume_tac o SRULE [])) >>
  `LENGTH evs <= SUC H` by simp[] >>
  qpat_x_assum `!q evs qs. _ ==> ?costs. _` drule_all >>
  disch_then (qx_choose_then `costs` strip_assume_tac) >>
  `LENGTH evs <= (bound + 1) * SUM costs + rank q0` by
    (irule focus_joint_chain_length_bound >>
     qexistsl_tac [`ctx`, `qs`, `q`] >> gvs[joint_trace_def]) >>
  `(bound + 1) * SUM costs <= (bound + 1) * max_cost` by simp[] >>
  gvs[Abbr `H`] >> decide_tac
QED
