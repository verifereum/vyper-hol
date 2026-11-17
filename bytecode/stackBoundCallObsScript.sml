(* Result-sensitive composition for CALL's observation-preserving prefix. *)
Theory stackBoundCallObs
Ancestors
  vfmExecution vfmConstants list pair rich_list

Definition sb_call_context_obs_def:
  sb_call_context_obs (c:context) =
    (c.msgParams.code,c.pc,c.jumpDest,c.stack)
End

Definition sb_call_obs_def:
  sb_call_obs s = MAP (sb_call_context_obs o FST) s.contexts
End

Definition sb_call_wp_def:
  sb_call_wp (m:execution_state -> 'a execution_result) Q s <=>
    !r t. m s = (r,t) ==> Q r t
End

Definition sb_call_prefix_def:
  sb_call_prefix (m:execution_state -> 'a execution_result) <=>
    !s r t. s.contexts <> [] /\ m s = (r,t) ==>
      sb_call_obs t = sb_call_obs s /\ r <> INR (SOME StackOverflow)
End

Theorem sb_call_obs_length[simp]:
  LENGTH (sb_call_obs s) = LENGTH s.contexts
Proof
  simp[sb_call_obs_def]
QED

Theorem sb_call_obs_empty[simp]:
  (sb_call_obs s = [] <=> s.contexts = [])
Proof
  simp[sb_call_obs_def]
QED

Theorem sb_call_obs_head:
  s.contexts <> [] ==>
  HD (sb_call_obs s) = sb_call_context_obs (FST (HD s.contexts))
Proof
  Cases_on `s.contexts` >> simp[sb_call_obs_def]
QED

Theorem sb_call_obs_equal:
  sb_call_obs t = sb_call_obs s /\ s.contexts <> [] ==>
  t.contexts <> [] /\ LENGTH t.contexts = LENGTH s.contexts /\
  (FST (HD t.contexts)).msgParams.code = (FST (HD s.contexts)).msgParams.code /\
  (FST (HD t.contexts)).pc = (FST (HD s.contexts)).pc /\
  (FST (HD t.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest /\
  (FST (HD t.contexts)).stack = (FST (HD s.contexts)).stack
Proof
  strip_tac >>
  `t.contexts <> []` by metis_tac[sb_call_obs_empty] >>
  `LENGTH t.contexts = LENGTH s.contexts` by metis_tac[sb_call_obs_length] >>
  `sb_call_context_obs (FST (HD t.contexts)) =
   sb_call_context_obs (FST (HD s.contexts))` by metis_tac[sb_call_obs_head] >>
  gvs[sb_call_context_obs_def]
QED

Theorem sb_call_wp_bind:
  sb_call_wp (bind m k) Q s <=>
  sb_call_wp m (\r t. case r of INL x => sb_call_wp (k x) Q t
                             | INR e => Q (INR e) t) s
Proof
  Cases_on `m s` >> Cases_on `q` >>
  simp[sb_call_wp_def,bind_def,sumTheory.FORALL_SUM]
QED

Theorem sb_call_wp_ignore_bind:
  sb_call_wp (ignore_bind m k) Q s <=>
  sb_call_wp m (\r t. case r of INL x => sb_call_wp k Q t
                             | INR e => Q (INR e) t) s
Proof
  simp[ignore_bind_def,sb_call_wp_bind]
QED

Theorem sb_call_prefix_bind:
  sb_call_prefix m /\ (!x. sb_call_prefix (k x)) ==>
  sb_call_prefix (bind m k)
Proof
  rewrite_tac[sb_call_prefix_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `m s` >> rename1 `m s = (res,mid)` >>
  Cases_on `res` >> gvs[bind_def] >>
  `sb_call_obs mid = sb_call_obs s` by metis_tac[] >>
  `mid.contexts <> []` by metis_tac[sb_call_obs_empty] >>
  metis_tac[]
QED

Theorem sb_call_prefix_ignore_bind:
  sb_call_prefix m /\ sb_call_prefix k ==>
  sb_call_prefix (ignore_bind m k)
Proof
  simp[ignore_bind_def,sb_call_prefix_bind]
QED

Theorem sb_call_wp_prefix:
  sb_call_prefix m /\ s.contexts <> [] /\
  (!x t. sb_call_obs t = sb_call_obs s /\ t.contexts <> [] ==>
         sb_call_wp (k x) Q t) /\
  (!e t. sb_call_obs t = sb_call_obs s /\ t.contexts <> [] /\
         e <> SOME StackOverflow ==> Q (INR e) t) ==>
  sb_call_wp (bind m k) Q s
Proof
  rw[sb_call_wp_bind,sb_call_wp_def] >>
  fs[sb_call_prefix_def] >>
  first_x_assum drule >> strip_tac >>
  `t.contexts <> []` by metis_tac[sb_call_obs_empty] >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem sb_call_prefix_return[simp]:
  sb_call_prefix (return x)
Proof
  simp[sb_call_prefix_def,return_def]
QED

Theorem sb_call_prefix_fail[simp]:
  e <> StackOverflow ==> sb_call_prefix (fail e)
Proof
  simp[sb_call_prefix_def,fail_def]
QED

Theorem sb_call_prefix_set_return_data[simp]:
  sb_call_prefix (set_return_data bytes)
Proof
  rw[sb_call_prefix_def,set_return_data_def,bind_def,
     get_current_context_def,set_current_context_def,return_def,fail_def] >>
  Cases_on `s.contexts` >>
  gvs[sb_call_obs_def,sb_call_context_obs_def,AllCaseEqs()]
QED
