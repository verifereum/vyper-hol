Theory concretizeLayoutCanonicalDeferred
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutCanonicalResume
  frameSelectedSimulation frameSelectedDecoration frameFiniteJointDecoration
  frameJointTransition list arithmetic

(* A call returns before its enclosing block consumes OriginResume. *)
Definition layout_deferred_OS_def:
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' <=>
    if i.inst_opcode = INVOKE then
      case (r,r') of
        (OK post,OK post') =>
          !a ev qn.
            layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
              q n i s j t a /\
            decoration_consumes C i q post qe ev qn /\
            selected_segment C q0 path m qe [(ev,qn)] qn ==>
            layout_canonical_success D lo vs0 C C' q0 es qs ass qend
              m T a post post'
      | _ => layout_canonical_OS D lo vs0 C C' q0 es qs ass qend q n qe m i s j t r r'
    else layout_canonical_OS D lo vs0 C C' q0 es qs ass qend q n qe m i s j t r r'
End

Theorem layout_deferred_noninvoke:
  i.inst_opcode <> INVOKE ==>
  (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' <=>
   layout_canonical_OS D lo vs0 C C' q0 es qs ass qend q n qe m i s j t r r')
Proof
  simp[layout_deferred_OS_def]
QED

Theorem layout_deferred_nonOK:
  (!post. r <> OK post) ==>
  (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t r r' <=>
   layout_canonical_OS D lo vs0 C C' q0 es qs ass qend q n qe m i s j t r r')
Proof
  Cases_on `r` >> Cases_on `r'` >> simp[layout_deferred_OS_def]
QED

Theorem layout_deferred_consume:
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n qe m i s j t
    (OK post) (OK post') /\ i.inst_opcode = INVOKE /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a /\
  decoration_consumes C i q post qe ev qn /\
  selected_segment C q0 path m qe [(ev,qn)] qn ==>
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m T a post post'
Proof
  simp[layout_deferred_OS_def] >> metis_tac[]
QED

(* The enclosing next constructor, unlike the call step, contains the edge. *)
Theorem layout_deferred_next_consume:
  selected_segment C q0 path n q (ws ++ [(ev,qn)] ++ wb) qend /\
  joint_segment C q ws qm /\ joint_segment C qn wb qend /\
  decoration_consumes C i q post qm ev qn /\ i.inst_opcode = INVOKE /\
  layout_deferred_OS D lo vs0 C C' q0 path es qs ass qfinal q n qm
    (n + LENGTH ws) i s j t (OK post) (OK post') /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qfinal
    q n i s j t a ==>
  layout_canonical_success D lo vs0 C C' q0 es qs ass qfinal
    (n + LENGTH ws) T a post post'
Proof
  strip_tac >>
  `joint_transition C qm ev qn` by fs[decoration_consumes_def] >>
  `selected_segment C q0 path (n + LENGTH ws) qm ([(ev,qn)] ++ wb) qend` by
    (irule (cj 2 selected_segment_parts) >>
     simp[joint_segment_def] >> metis_tac[APPEND_ASSOC]) >>
  `selected_segment C q0 path (n + LENGTH ws) qm [(ev,qn)] qn` by
    (irule (cj 1 selected_segment_parts) >>
     simp[joint_segment_def] >> qexistsl [`qend`, `wb`] >> fs[]) >>
  drule_all layout_deferred_consume >> simp[]
QED

(* At a concrete RET endpoint, consumption identifies the exact source payload. *)
Theorem layout_deferred_resume_event:
  i.inst_opcode = INVOKE /\ inst.inst_opcode = RET /\
  qe = JointConfig stk PG G tn callee inst sc oms om hs h /\
  local_pending C qe (IntRet ret sc) /\
  decoration_consumes C i q post qe ev qn /\
  selected_segment C q0 path m qe [(ev,qn)] qn ==>
  ?fuel. m < LENGTH path /\
    EL m (MAP FST path) = SOME (OriginResume fuel callee inst sc ret sc post)
Proof
  strip_tac >>
  `step_inst_base inst sc = IntRet ret sc` by
    (gvs[local_pending_def] >>
     qpat_x_assum `finite_step _ _ _ _` mp_tac >>
     simp[Once frameFiniteExecutionTheory.finite_step_cases]) >>
  `joint_transition C qe ev qn /\
   ?fuel fn ri sr rv send.
     ev = SOME (OriginResume fuel fn ri sr rv send post)` by
    (gvs[decoration_consumes_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_return] >> strip_tac >> gvs[] >>
  gvs[venomExecSemanticsTheory.step_inst_def] >>
  drule selected_singleton_event >>
  drule selected_segment_indices >> simp[] >> metis_tac[]
QED

val _ = export_theory();
