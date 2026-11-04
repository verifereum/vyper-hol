Theory lowerDloadPhaseBoundary
Ancestors
  lowerDloadPairedBoundary lowerDloadAllocation ptrDiscipline venomExecSemantics
  venomState list arithmetic

Inductive ld_target_prefix:
[~zero:]
  (!C code t0 u0. ld_target_prefix C code t0 u0 0 t0 u0)
[~succ:]
  (!C code t0 u0 n t u z fuel.
    ld_target_prefix C code t0 u0 n t u /\ n < LENGTH code /\
    step_inst fuel C (EL n code) t = OK z ==>
    ld_target_prefix C code t0 u0 (SUC n)
      (z with vs_inst_idx := SUC t.vs_inst_idx)
      (step_taint (EL n code) t z u))
End

Theorem ld_target_prefix_bound:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u ==> n <= LENGTH code
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[]
QED

Theorem ld_target_prefix_empty:
  ld_target_prefix C code t0 u0 0 t u <=> t = t0 /\ u = u0
Proof
  once_rewrite_tac[ld_target_prefix_cases] >> simp[]
QED

Theorem ld_target_prefix_step_iff:
  ld_target_prefix C code t0 u0 (SUC n) t u <=>
  ?v w z fuel. ld_target_prefix C code t0 u0 n v w /\
    n < LENGTH code /\ step_inst fuel C (EL n code) v = OK z /\
    t = z with vs_inst_idx := SUC v.vs_inst_idx /\
    u = step_taint (EL n code) v z w
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [ld_target_prefix_cases])) >>
  simp[] >> metis_tac[]
QED

Theorem ld_target_prefix_index:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u ==>
    t.vs_inst_idx = t0.vs_inst_idx + n
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[ADD_CLAUSES]
QED

Theorem ld_target_prefix_source_witness:
  P s /\ ld_target_prefix C code t0 u0 n t u /\ n < LENGTH code /\
  step_inst fuel C (EL n code) t = OK z ==>
  P s /\ ld_target_prefix C code t0 u0 (SUC n)
    (z with vs_inst_idx := SUC t.vs_inst_idx)
    (step_taint (EL n code) t z u)
Proof
  metis_tac[ld_target_prefix_rules]
QED

(* Interface probes for the four-step and two-step configured expansions. *)
Theorem ld_target_prefix_expansion_bounds[local]:
  (ld_target_prefix C [a;b;c;d] t0 u0 n t u ==> n <= 4) /\
  (ld_target_prefix C [a;b] t0 u0 n t u ==> n <= 2)
Proof
  conj_tac >> strip_tac >> drule ld_target_prefix_bound >> simp[]
QED
