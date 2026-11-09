(* Natural allocation intervals and ordered saved-frame cuts.
   No machine-word representability is required by this geometry. *)
Theory occurrenceGeometry
Ancestors
  o1LowerDloadOccurrence finite_map list pred_set arithmetic

Definition occurrence_natural_geometry_def:
  occurrence_natural_geometry lo a U B stk s <=>
    (!id b z. FLOOKUP B id = SOME (b,z) ==>
       lo <= b /\ b + z <= s.vs_alloca_next) /\
    (!id jd b z c w.
       FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (c,w) /\
       id <> jd /\ 0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b) /\
    LENGTH U = LENGTH stk /\
    (!j. j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= s.vs_alloca_next /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          MEM (FST id) (MAP (\u. u.of_owner) (DROP j U)) ==>
          b + z <= (EL j stk).cf_state.vs_alloca_next) /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          (FST id = a \/ MEM (FST id) (MAP (\u. u.of_owner) (TAKE j U))) ==>
          (EL j stk).cf_state.vs_alloca_next <= b)) /\
    (!i j. i < j /\ j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= (EL i stk).cf_state.vs_alloca_next)
End

Theorem occurrence_natural_geometry_empty:
  occurrence_natural_geometry lo a [] FEMPTY [] s
Proof
  simp[occurrence_natural_geometry_def]
QED

Theorem occurrence_natural_geometry_same_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  strip_tac >> gvs[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_natural_geometry_grow_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  rw[occurrence_natural_geometry_def] >> metis_tac[LESS_EQ_TRANS]
QED

