Theory frameActivationLifetime
Ancestors frameJointTrace frameJointTransition frameActivationCache
  frameOriginHistory list arithmetic

Definition lifetime_step_def:
  lifetime_step n ev (ids:num list) =
    case ev of NONE => SUC n :: ids
    | SOME (OriginResume fuel fn inst s ret send post) => TL ids
    | _ => ids
End

Definition lifetime_annotations_def:
  lifetime_annotations n ids [] = [ids] /\
  lifetime_annotations n ids (ev::es) =
    ids :: lifetime_annotations (SUC n) (lifetime_step n ev ids) es
End

Definition lifetime_ok_def:
  lifetime_ok (n:num) (ids:num list) q <=>
    LENGTH ids = SUC (activation_depth q) /\
    ALL_DISTINCT ids /\ EVERY (\birth. birth <= n) ids
End

Theorem lifetime_annotations_length[simp]:
  !es n ids. LENGTH (lifetime_annotations n ids es) = SUC (LENGTH es)
Proof
  Induct >> simp[lifetime_annotations_def]
QED

Theorem lifetime_annotations_zero[simp]:
  !es n ids. EL 0 (lifetime_annotations n ids es) = ids
Proof
  Cases >> simp[lifetime_annotations_def]
QED

Theorem lifetime_step_call[simp]:
  lifetime_step n NONE ids = SUC n :: ids
Proof
  simp[lifetime_step_def]
QED

Theorem lifetime_step_return[simp]:
  lifetime_step n (SOME (OriginResume fuel fn inst s ret send post)) (callee::caller) = caller
Proof
  simp[lifetime_step_def]
QED

Theorem lifetime_transition:
  joint_transition C q ev q' /\ lifetime_ok n ids q ==>
  lifetime_ok (SUC n) (lifetime_step n ev ids) q'
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[lifetime_ok_def, lifetime_step_def, activation_depth_def]
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac)
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac)
  >- (conj_tac
      >- (strip_tac >> gvs[EVERY_MEM] >> res_tac >> decide_tac) >>
      gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac)
  >> Cases_on `ids` >> gvs[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem lifetime_chain_prefix:
  !es n ids q qs r k.
  joint_chain C q es qs r /\ lifetime_ok n ids q /\ k <= LENGTH es ==>
  lifetime_ok (n+k) (EL k (lifetime_annotations n ids es)) (EL k (q::qs))
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def]
  >- (rpt strip_tac >> gvs[lifetime_annotations_def]) >>
  rpt strip_tac >> Cases_on `k`
  >- gvs[] >>
  gvs[lifetime_annotations_def] >>
  rename1 `joint_transition C q ev next` >>
  `lifetime_ok (SUC n) (lifetime_step n ev ids) next` by
    metis_tac[lifetime_transition] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`SUC n`, `lifetime_step n ev ids`, `n'`] mp_tac) >>
  simp[ADD_CLAUSES, ADD_COMM]
QED

Theorem lifetime_initial:
  joint_initial vs0 C q ==> lifetime_ok 0 [0] q
Proof
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  gvs[lifetime_ok_def, activation_depth_def]
QED

Theorem joint_trace_lifetimes:
  joint_trace vs0 C q0 es qs q /\ k <= LENGTH es ==>
  lifetime_ok k (EL k (lifetime_annotations 0 [0] es)) (EL k (q0::qs))
Proof
  simp[joint_trace_def] >> strip_tac >>
  drule lifetime_initial >> strip_tac >>
  drule_all lifetime_chain_prefix >> simp[]
QED

Theorem lifetime_annotations_edge:
  !es n ids k. k < LENGTH es ==>
  EL (SUC k) (lifetime_annotations n ids es) =
    lifetime_step (n+k) (EL k es) (EL k (lifetime_annotations n ids es))
Proof
  Induct >> simp[lifetime_annotations_def] >> rpt gen_tac >>
  Cases_on `k` >> simp[lifetime_annotations_def, ADD_CLAUSES] >>
  metis_tac[ADD_CLAUSES]
QED

Theorem lifetime_annotations_fresh_call:
  k < LENGTH es /\ EL k es = NONE ==>
  EL (SUC k) (lifetime_annotations 0 [0] es) =
    SUC k :: EL k (lifetime_annotations 0 [0] es)
Proof
  strip_tac >> drule lifetime_annotations_edge >>
  disch_then (qspecl_then [`0`, `[0]`] mp_tac) >> simp[]
QED

Theorem lifetime_annotations_pop:
  k < LENGTH es /\ EL k es = SOME (OriginResume fuel fn inst s ret send post) ==>
  EL (SUC k) (lifetime_annotations 0 [0] es) =
    TL (EL k (lifetime_annotations 0 [0] es))
Proof
  strip_tac >> drule lifetime_annotations_edge >>
  disch_then (qspecl_then [`0`, `[0]`] mp_tac) >> simp[lifetime_step_def]
QED

Theorem lifetime_reused_depth_probe[local]:
  lifetime_annotations 0 [0]
    [NONE; SOME (OriginResume fuel fn inst s ret send post); NONE] =
  [[0]; [1;0]; [0]; [3;0]]
Proof
  simp[lifetime_annotations_def, lifetime_step_def]
QED
