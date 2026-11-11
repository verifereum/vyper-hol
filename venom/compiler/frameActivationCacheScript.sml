Theory frameActivationCache
Ancestors
  frameJointTransition frameJointTrace frameOriginCache ptrDisciplineEmptyTaint
  ptrDiscipline venomExecSemantics venomState venomInst venomMemProps
  finite_map list

(* Depth is stable only while the slot survives; it is not an activation ID. *)
Definition activation_depth_def:
  activation_depth (JointConfig stk PG G tn current inst s oms om hs h) = LENGTH stk
End

Definition activation_cache_def:
  activation_cache (JointConfig stk PG G tn current inst s oms om hs h) d fn aid site <=>
    (d = LENGTH stk /\ fn = current /\ FLOOKUP s.vs_allocas aid = SOME site) \/
    (d < LENGTH stk /\ fn = (EL (LENGTH stk - SUC d) stk).cf_fn /\
     FLOOKUP (EL (LENGTH stk - SUC d) stk).cf_state.vs_allocas aid = SOME site)
End

Theorem activation_cache_current:
  activation_cache (JointConfig stk PG G tn current inst s oms om hs h)
    (LENGTH stk) fn aid site <=>
  fn = current /\ FLOOKUP s.vs_allocas aid = SOME site
Proof
  simp[activation_cache_def]
QED

Theorem activation_cache_saved:
  k < LENGTH stk ==>
  (activation_cache (JointConfig stk PG G tn current inst s oms om hs h)
    (LENGTH stk - SUC k) fn aid site <=>
   fn = (EL k stk).cf_fn /\ FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site)
Proof
  strip_tac >>
  `LENGTH stk - SUC k < LENGTH stk /\
   LENGTH stk - SUC (LENGTH stk - SUC k) = k` by decide_tac >>
  simp[activation_cache_def]
QED

Theorem activation_cache_depth:
  activation_cache q d fn aid site ==> d <= activation_depth q
Proof
  Cases_on `q` >> simp[activation_cache_def, activation_depth_def] >>
  rpt strip_tac >> simp[]
QED

Theorem activation_cache_same_stack:
  activation_cache (JointConfig stk PG G tn current inst s oms om hs h) d fn aid site /\
  (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP s'.vs_allocas aid = SOME site) ==>
  activation_cache (JointConfig stk PG' G' tn' current inst' s' oms' om' hs' h') d fn aid site
Proof
  simp[activation_cache_def] >> metis_tac[]
QED

Theorem activation_cache_push:
  activation_cache (JointConfig stk PG G tn current inst s oms om hs h) d fn aid site ==>
  activation_cache
    (JointConfig
      (<|cf_fn := current; cf_inst := inst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      PG' G' tn' current' inst' s' oms' om' hs' h') d fn aid site
Proof
  simp[activation_cache_def] >> strip_tac
  >- simp[] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  simp[]
QED

Theorem activation_cache_pop:
  activation_cache (JointConfig (f::stk) PG G tn current inst s oms om hs h) d fn aid site /\
  d <= LENGTH stk /\ s'.vs_allocas = f.cf_state.vs_allocas ==>
  activation_cache (JointConfig stk PG' G' tn' f.cf_fn inst' s' oms' om' hs' h') d fn aid site
Proof
  simp[activation_cache_def] >> strip_tac >>
  Cases_on `d = LENGTH stk` >> gvs[] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  gvs[]
QED

Theorem joint_activation_cache_step:
  !ctx q ev q'. joint_transition ctx q ev q' ==>
  !d fn aid site. activation_cache q d fn aid site /\ d <= activation_depth q' ==>
    activation_cache q' d fn aid site
Proof
  ho_match_mp_tac joint_transition_ind >> rpt conj_tac
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume joint_activation_cache_step[next]:
  rpt strip_tac >> irule activation_cache_same_stack >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[step_inst_cache_preserved]
QED

Resume joint_activation_cache_step[block]:
  rpt strip_tac >> irule activation_cache_same_stack >>
  goal_assum (drule_at Any) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  metis_tac[enters_block_allocas]
QED

Resume joint_activation_cache_step[call]:
  rpt strip_tac >> metis_tac[activation_cache_push]
QED

Resume joint_activation_cache_step[ret]:
  rpt strip_tac >> irule activation_cache_pop >>
  fs[activation_depth_def] >> conj_tac
  >- (drule return_bind_cache >> simp[]) >>
  goal_assum (drule_at Any)
QED

Finalise joint_activation_cache_step

Theorem joint_activation_cache_interval:
  !j n. joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_cache (EL n (q0::qs)) d fn aid site /\
  (!i. n <= i /\ i <= j ==> d <= activation_depth (EL i (q0::qs))) ==>
  activation_cache (EL j (q0::qs)) d fn aid site
Proof
  Induct
  >- (rpt strip_tac >> `n = 0` by decide_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `n = SUC j`
  >- gvs[] >>
  `n <= j /\ j < LENGTH es` by decide_tac >>
  `activation_cache (EL j (q0::qs)) d fn aid site` by
    (first_x_assum irule >> simp[] >> qexists_tac `n` >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `joint_transition ctx (EL j (q0::qs)) (EL j es) (EL (SUC j) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  drule joint_activation_cache_step >>
  disch_then irule >> simp[] >> first_x_assum irule >> simp[]
QED

(* On return the departing current slot is absent.  Hence an interval
   containing that edge cannot preserve it merely by reusing its depth. *)
Theorem joint_return_depth_drops:
  joint_transition ctx p (SOME (OriginResume fuel fn rinst s ret send post)) q ==>
  activation_depth p = SUC (activation_depth q) /\
  ~(activation_depth p <= activation_depth q)
Proof
  rewrite_tac[joint_transition_return] >> rpt strip_tac >>
  gvs[activation_depth_def]
QED
