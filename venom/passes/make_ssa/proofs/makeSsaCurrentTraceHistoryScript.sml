Theory makeSsaCurrentTraceHistory
Ancestors makeSsaCurrentTreeTrace makeSsaCurrentRenameTrace makeSsaCurrentInduct list alist

Definition current_output_delta_def:
  current_output_delta anns names = MAP (\((t,v),n). (t,v,n)) (ZIP (anns,names))
End

Definition current_local_delta_def:
  current_local_delta aa ys = FLAT (MAP (\(anns,i).
    current_output_delta anns i.inst_outputs) (ZIP (aa,ys)))
End

Definition current_event_delta_def:
  current_event_delta A (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) =
    current_local_delta (A l) ren
End

Theorem current_outputs_trace_delta:
  !anns s rs H E names s' rs' H' E'.
    current_outputs_trace anns s rs H E names s' rs' H' E' ==>
    H' = H ++ current_output_delta anns names /\ LENGTH names = LENGTH anns
Proof
  Induct >> simp[current_outputs_trace_def, current_output_delta_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[current_outputs_trace_def] >> first_x_assum drule >>
  simp[current_output_delta_def, APPEND_ASSOC]
QED

Theorem current_inst_trace_delta:
  current_inst_trace anns i s rs H E j s' rs' H' E' ==>
  H' = H ++ current_output_delta anns j.inst_outputs /\
  LENGTH j.inst_outputs = LENGTH anns
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule current_outputs_trace_delta >> strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> gvs[]
QED

Theorem current_local_trace_delta:
  !aa xs s rs H E ys s' rs' H' E'.
    current_local_trace aa xs s rs H E ys s' rs' H' E' ==>
    H' = H ++ current_local_delta aa ys /\ LENGTH aa = LENGTH ys /\
    LIST_REL (\anns i. LENGTH anns = LENGTH i.inst_outputs) aa ys
Proof
  Induct >> simp[current_local_trace_def, current_local_delta_def] >>
  rpt strip_tac >> gvs[current_local_trace_def] >>
  drule current_inst_trace_delta >> strip_tac >>
  first_x_assum drule >> simp[current_local_delta_def, APPEND_ASSOC]
QED

Theorem current_tree_trace_delta:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    H' = H ++ FLAT (MAP (current_event_delta A) events)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    H' = H ++ FLAT (MAP (current_event_delta A) events))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_delta >> strip_tac >>
      first_x_assum drule >> simp[current_event_delta_def, APPEND_ASSOC])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[FLAT_APPEND, APPEND_ASSOC]
QED
