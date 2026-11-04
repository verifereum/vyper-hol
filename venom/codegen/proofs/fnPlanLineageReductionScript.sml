Theory fnPlanLineageReduction
Ancestors
  planWf stackModel

Theorem reduce_depth_step_height:
  !targets op f n ps dist cand ops ps'.
    stack_get_unfixed_depth op f n ps.ps_stack = SOME dist /\
    16 < dist /\
    select_spill_candidate ps.ps_stack targets dist n = SOME cand /\
    do_spill_at cand ps = (ops, ps') ==>
    0 < LENGTH ps.ps_stack /\
    LENGTH ps'.ps_stack + 1 = LENGTH ps.ps_stack
Proof
  rpt strip_tac >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule do_spill_at_length_exact >>
  disch_then (qspec_then `cand` mp_tac) >> simp[]
QED
