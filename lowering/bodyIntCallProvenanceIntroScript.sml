(* Representation boundaries strengthen the already selected success witness. *)
Theory bodyIntCallProvenanceIntro
Ancestors
  bodyIntCallProducerInterface loweringPosts

Theorem intcall_vv_provenance_owned:
  vv_own cenv cx ty sa sb es raw vv s /\
  (!t p. vv = LocatedValue t p ==> p.ptr_location <> LocCode) ==>
  intcall_vv_provenance cenv cx ty sa sb es raw vv s
Proof
  Cases_on `vv` >>
  simp[vv_own_def, expr_val_own_def, intcall_vv_provenance_def] >>
  metis_tac[]
QED

Theorem intcall_vv_provenance_nonmemory:
  p.ptr_location <> LocMemory /\ p.ptr_location <> LocCode ==>
  intcall_vv_provenance cenv cx ty sa sb es raw (LocatedValue t p) s
Proof
  simp[intcall_vv_provenance_def]
QED

Theorem gas_outcome_owned_provenance:
  gas_outcome memory tops p source start Q R /\
  (!marks res ee r.
    gas_marked_exec memory p source start marks res ee r ==>
    !s. r = OK s /\ Q res (ee with gas_obs := []) s ==>
      vv_own cenv cx ty sa sb (ee with gas_obs := []) (raw res) vv s /\
      (!t ptr. vv = LocatedValue t ptr ==> ptr.ptr_location <> LocCode)) ==>
  gas_outcome memory tops p source start
    (\res ee s. Q res ee s /\
      intcall_vv_provenance cenv cx ty sa sb ee (raw res) vv s) R
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_strengthen_witness >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all intcall_vv_provenance_owned >> simp[]
QED
