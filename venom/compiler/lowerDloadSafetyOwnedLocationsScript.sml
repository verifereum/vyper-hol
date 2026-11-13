(* Correlated structural ownership and location packaging. *)
Theory lowerDloadSafetyOwnedLocations
Ancestors
  lowerDloadSafetyOwnership lowerDloadSafetyOrdinaryCoverage
  lowerDloadSafetyEntry lowerDloadSafetyWriteCoverage
  lowerDloadSafetyRelation lowerDloadSafetyKernel list

Theorem ld_owned_prefix_pack:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
  ld_global lo A frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  fn' = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  strip_tac >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`frames`,`N`,`X`,`p`,`h`] >>
  simp[]
QED

Theorem ld_owned_pair_zero:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = ld_image f /\ active_inst fn' ti t /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  strip_tac >> drule_all ld_pair_zero_witness >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  irule ld_owned_prefix_pack >>
  qexistsl_tac [`A`,`G`,`N`,`PG`,`X`,`fn`,`f::fs`,`0`,`inst`,`p`,`s`,`stk`,`t`,`tn`] >>
  simp[]
QED

(* Saved tail ownership is independent of allocation-map restriction and
   restored state fields. Only the selected fn/Q fields matter. *)
Theorem ld_ownership_pop:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (callee::saved::fs) /\
  restored.lf_fn = saved.lf_fn /\ restored.lf_Q = saved.lf_Q ==>
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (restored::fs)
Proof
  strip_tac >> irule ld_ownership_replace >>
  goal_assum (drule_at Any) >> fs[ld_ownership_cons]
QED

Theorem ld_ownership_push_saved:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (caller::fs) /\
  saved.lf_fn = caller.lf_fn /\ saved.lf_Q = caller.lf_Q /\
  ld_vars P A caller /\ ptr_use_ok P (fn_pv P caller.lf_fn) inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  callee.lf_fn.fn_name = nm /\
  callee.lf_Q = MAP (op_prov caller.lf_H) args ==>
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (callee::saved::fs)
Proof
  strip_tac >>
  `EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (saved::fs)` by
    (irule ld_ownership_replace >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all ld_ownership_push >> simp[]
QED
