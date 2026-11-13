Theory concretizePtrDallocaChronoJoint
Ancestors
  concretizePtrChronologicalHistory frameJointTrace frameJointTransition
  frameOriginHistory list rich_list arithmetic

(* This erasure avoids repeating eleven-field case expressions in the
   occurrence-indexed lift. It forgets origin bookkeeping, not occurrences. *)
Definition ptr_dalloca_joint_observe_def:
  ptr_dalloca_joint_observe
    (JointConfig stk PG G tn fn inst s oms om hs h) =
    ptr_observe stk PG G tn fn inst s
End

Theorem ptr_dalloca_chrono_joint_step:
  !C a b. ptr_chrono_step C a b ==>
  !stk PG G tn fn inst s oms om hs h.
    a = ptr_observe stk PG G tn fn inst s /\
    LENGTH oms = LENGTH stk /\ LENGTH hs = LENGTH stk ==>
    ?ev q. joint_transition C
      (JointConfig stk PG G tn fn inst s oms om hs h) ev q /\
      b = ptr_dalloca_joint_observe q
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[ptr_observe_def]
  >- (simp[ptr_dalloca_joint_observe_def] >>
      metis_tac[joint_transition_rules, ptr_dalloca_joint_observe_def, ptr_observe_def])
  >- (metis_tac[joint_transition_rules, ptr_dalloca_joint_observe_def, ptr_observe_def])
  >- (metis_tac[joint_transition_rules, ptr_dalloca_joint_observe_def, ptr_observe_def]) >>
  Cases_on `oms` >> Cases_on `hs` >> gvs[] >>
  metis_tac[joint_transition_rules, ptr_dalloca_joint_observe_def, ptr_observe_def]
QED

Theorem ptr_dalloca_chrono_joint_reachable_step:
  ptr_chrono_step C a b /\ a = ptr_dalloca_joint_observe q /\
  joint_config_reachable vs0 C q ==>
  ?ev r. joint_transition C q ev r /\ b = ptr_dalloca_joint_observe r
Proof
  Cases_on `q` >> simp[ptr_dalloca_joint_observe_def,
    joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_endpoints >> strip_tac >>
  metis_tac[ptr_dalloca_chrono_joint_step]
QED

Theorem ptr_dalloca_chrono_joint_lift:
  !vs0 C hist endpoint. ptr_chrono_history vs0 C hist endpoint ==>
  ?q0 es qs q. joint_trace vs0 C q0 es qs q /\
    LENGTH hist = SUC (LENGTH es) /\
    LIST_REL (\obs cfg. obs = ptr_dalloca_joint_observe cfg) hist (q0::qs) /\
    endpoint = ptr_dalloca_joint_observe q
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- (rpt strip_tac >>
      `?q. joint_initial vs0 C q /\
        ptr_observe [] [] FEMPTY entry_taint fn inst s1 =
          ptr_dalloca_joint_observe q` by
        metis_tac[joint_initial_rules, ptr_dalloca_joint_observe_def] >>
      qexistsl [`q`,`[]`,`[]`,`q`] >>
      simp[joint_trace_def, joint_chain_def]) >>
  rpt gen_tac >> strip_tac >>
  `joint_config_reachable vs0 C q` by metis_tac[joint_trace_reachable] >>
  drule_all ptr_dalloca_chrono_joint_reachable_step >> strip_tac >>
  qexistsl [`q0`,`es ++ [ev]`,`qs ++ [r]`,`r`] >>
  conj_tac >- metis_tac[joint_trace_snoc] >>
  conj_tac >- simp[] >> reverse conj_tac >- simp[] >>
  `q0::(qs ++ [r]) = (q0::qs) ++ [r]` by simp[] >>
  pop_assum SUBST1_TAC >> irule LIST_REL_APPEND_suff >> simp[]
QED
