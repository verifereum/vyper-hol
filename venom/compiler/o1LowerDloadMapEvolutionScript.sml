(* Transport the existing relocation kernels across live occurrence domains. *)
Theory o1LowerDloadMapEvolution
Ancestors
  o1LowerDloadRelocationKernel finite_map pred_set

Theorem ld_memory_agree_extend:
  ld_memory_agree sites lo mask sm tm /\ id NOTIN FDOM sites ==>
  ld_memory_agree (sites |+ (id,(b,c,z))) lo
    (mask UNION {b+j | j < z}) sm tm
Proof
  simp[ld_memory_agree_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_memory_agree_restrict:
  ld_memory_agree sites lo mask sm tm ==>
  ld_memory_agree (DRESTRICT sites keep) lo mask sm tm
Proof
  simp[ld_memory_agree_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_value_agree_extend:
  ld_value_agree sites h m x y /\ id NOTIN FDOM sites ==>
  ld_value_agree (sites |+ (id,(b,c,z))) h m x y
Proof
  Cases_on `h` >> simp[ld_value_agree_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_value_agree_restrict:
  ld_value_agree sites h m x y /\ (!id. h = SOME id ==> id IN keep) ==>
  ld_value_agree (DRESTRICT sites keep) h m x y
Proof
  Cases_on `h` >> simp[ld_value_agree_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED
