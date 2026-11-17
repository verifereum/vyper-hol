(* Result-sensitive terminal boundaries for CALL-family instructions. *)
Theory stackBoundCallTerminal
Ancestors
  stackBoundCallObs vfmExecution vfmWfState list pair

Theorem sb_call_abort_unuse:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  abort_unuse n s = (r,t) ==>
  r <> INR (SOME StackOverflow) /\
  LENGTH t.contexts = LENGTH s.contexts /\
  (r = INL () ==>
    sb_call_obs t =
      sb_call_context_obs
        (c with <|pc := SUC c.pc; stack := b2w F :: c.stack|>) ::
      MAP (sb_call_context_obs o FST) rest)
Proof
  strip_tac >> Cases_on `n <= c.gasUsed` >>
  gvs[abort_unuse_def,unuse_gas_def,push_stack_def,inc_pc_def,
      get_current_context_def,set_current_context_def,ignore_bind_def,
      bind_def,assert_def,return_def,fail_def,
      sb_call_obs_def,sb_call_context_obs_def]
QED

Theorem sb_call_abort_value:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  abort_call_value n s = (r,t) ==>
  r <> INR (SOME StackOverflow) /\
  LENGTH t.contexts = LENGTH s.contexts /\
  (r = INL () ==>
    sb_call_obs t =
      sb_call_context_obs
        (c with <|pc := SUC c.pc; stack := b2w F :: c.stack|>) ::
      MAP (sb_call_context_obs o FST) rest)
Proof
  strip_tac >> Cases_on `n <= c.gasUsed` >>
  gvs[abort_call_value_def,unuse_gas_def,push_stack_def,inc_pc_def,
      set_return_data_def,get_current_context_def,set_current_context_def,
      ignore_bind_def,bind_def,assert_def,return_def,fail_def,
      sb_call_obs_def,sb_call_context_obs_def]
QED

Theorem sb_call_proceed_observation:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r,t) /\
  s.contexts <> [] ==>
  ?h. sb_call_obs t = h :: sb_call_obs s
Proof
  strip_tac >> drule_all proceed_call_push_structure >> strip_tac >>
  Cases_on `t.contexts` >> gvs[sb_call_obs_def]
QED

Theorem sb_call_proceed_length:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r,t) /\
  s.contexts <> [] ==>
  LENGTH t.contexts = SUC (LENGTH s.contexts)
Proof
  strip_tac >> drule_all sb_call_proceed_observation >>
  strip_tac >> metis_tac[sb_call_obs_length,LENGTH]
QED
