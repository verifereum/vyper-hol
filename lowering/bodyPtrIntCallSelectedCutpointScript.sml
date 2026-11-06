(* Normal-fragment design algebra. PC equality is not branch alignment.
   A future producer must construct this certificate on the pointer-selected
   execution, including source branch/history alignment. Abnormal and exempt
   outcomes still require the existing gas_outcome_ptr interface; this normal
   probe does not discard them or normalize source gas observations. *)
Theory bodyPtrIntCallSelectedCutpoint
Ancestors
  bodyPtrIntCallSelectedPayload fragGasPathPtr compileEnv venomState

Definition intcall_cut_def:
  intcall_cut sa s <=>
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition intcall_selected_segment_def:
  intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 <=>
    intcall_cut sa s0 /\
    gas_path_ptr D lo ctx func PG G0 tn0 s0 n G1 tn1 (OK s1) /\
    intcall_cut sb s1
End

Definition intcall_selected_fragment_def:
  intcall_selected_fragment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1
    source es0 result es1 mode cenv cx t op capture v <=>
    intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 /\
    source es0 = (INL result,es1) /\
    intcall_selected_payload mode cenv cx t result op capture v es1 s1
End

Theorem intcall_segment_entry:
  intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 ==>
  intcall_cut sa s0
Proof
  simp[intcall_selected_segment_def]
QED

Theorem intcall_segment_exit:
  intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 ==>
  intcall_cut sb s1
Proof
  simp[intcall_selected_segment_def]
QED

Theorem intcall_segment_path:
  intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 ==>
  gas_path_ptr D lo ctx func PG G0 tn0 s0 n G1 tn1 (OK s1)
Proof
  simp[intcall_selected_segment_def]
QED

Theorem intcall_segment_refl:
  intcall_cut sa s /\ ~s.vs_halted ==>
  intcall_selected_segment D lo ctx func PG sa sa G tn s 0 G tn s
Proof
  simp[intcall_selected_segment_def] >>
  metis_tac[gas_path_ptr_rules]
QED

Theorem intcall_segment_then:
  intcall_selected_segment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1 /\
  intcall_selected_segment D lo ctx func PG sb sc G1 tn1 s1 m G2 tn2 s2 ==>
  intcall_selected_segment D lo ctx func PG sa sc G0 tn0 s0 (n+m) G2 tn2 s2
Proof
  simp[intcall_selected_segment_def] >> strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem intcall_fragment_elim:
  intcall_selected_fragment D lo ctx func PG sa sb G0 tn0 s0 n G1 tn1 s1
    source es0 result es1 mode cenv cx t op capture v ==>
  intcall_cut sa s0 /\
  gas_path_ptr D lo ctx func PG G0 tn0 s0 n G1 tn1 (OK s1) /\
  intcall_cut sb s1 /\ source es0 = (INL result,es1) /\
  intcall_selected_payload mode cenv cx t result op capture v es1 s1
Proof
  simp[intcall_selected_fragment_def, intcall_selected_segment_def]
QED

val _ = export_theory ();
