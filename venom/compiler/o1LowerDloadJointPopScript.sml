(* Owner deletion preserves suspended local relations, including exact credit. *)
Theory o1LowerDloadJointPop
Ancestors
  o1LowerDloadJointRelation o1LowerDloadMapEvolution
  o1LowerDloadEnvironment o1LowerDloadOccurrence
  finite_map pred_set list

Theorem ld_joint_credit_drop_owner:
  ~MEM a owners ==>
  {id | id IN FDOM (DRESTRICT X {id | FST id <> a}) /\ MEM (FST id) owners} =
  {id | id IN FDOM X /\ MEM (FST id) owners}
Proof
  simp[EXTENSION, FDOM_DRESTRICT] >> metis_tac[]
QED

Theorem ld_joint_erasure_restrict:
  ld_joint_erasure sites B ==>
  ld_joint_erasure (DRESTRICT sites keep) (DRESTRICT B keep)
Proof
  simp[ld_joint_erasure_def, FDOM_DRESTRICT, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_joint_geometry_drop_owner:
  ld_joint_geometry sites X lo (a::owners) ==>
  ld_joint_geometry (DRESTRICT sites {id | FST id <> a})
    (DRESTRICT X {id | FST id <> a}) lo owners
Proof
  simp[ld_joint_geometry_def, FDOM_DRESTRICT, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_env_agree_restrict:
  ld_env_agree sites fn H tn s t /\
  (!v id. FLOOKUP H v = SOME id ==> id IN keep) ==>
  ld_env_agree (DRESTRICT sites keep) fn H tn s t
Proof
  simp[ld_env_agree_def] >> rpt strip_tac >>
  irule ld_value_agree_restrict >> metis_tac[]
QED

Theorem ld_params_agree_restrict:
  ld_params_agree sites HP s t /\
  (!id. MEM (SOME id) HP ==> id IN keep) ==>
  ld_params_agree (DRESTRICT sites keep) HP s t
Proof
  simp[ld_params_agree_def] >> rpt strip_tac >>
  irule ld_value_agree_restrict >> simp[] >>
  metis_tac[MEM_EL]
QED

Theorem ld_joint_frame_drop_owner:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv s t /\
  ~MEM a (owner::older) /\
  (!v id. FLOOKUP H v = SOME id ==> MEM (FST id) (owner::older)) /\
  (!id. MEM (SOME id) HP ==> MEM (FST id) (owner::older)) ==>
  ld_joint_frame (DRESTRICT sites {id | FST id <> a})
    (DRESTRICT X {id | FST id <> a}) lo owner older u fn fn' H HP tv s t
Proof
  strip_tac >>
  `ld_env_agree (DRESTRICT sites {id | FST id <> a}) fn H
     (entry_taint with t_var := tv) s t` by
    (irule ld_env_agree_restrict >>
     fs[ld_joint_frame_def] >> metis_tac[]) >>
  `ld_params_agree (DRESTRICT sites {id | FST id <> a}) HP s t` by
    (irule ld_params_agree_restrict >>
     fs[ld_joint_frame_def] >> metis_tac[]) >>
  `{id | id IN FDOM (DRESTRICT X {id | FST id <> a}) /\
          MEM (FST id) (owner::older)} =
   {id | id IN FDOM X /\ MEM (FST id) (owner::older)}` by
    (irule ld_joint_credit_drop_owner >> simp[]) >>
  fs[ld_joint_frame_def] >>
  simp[ld_joint_frame_def, ld_joint_allocas_def, FLOOKUP_DRESTRICT] >>
  fs[ld_joint_allocas_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_joint_saved_drop_owner:
  !U stk ts.
  ld_joint_saved C' sites X lo U stk ts /\
  occurrence_saved_ok B U stk /\
  ~MEM a (MAP (\u. u.of_owner) U) ==>
  ld_joint_saved C' (DRESTRICT sites {id | FST id <> a})
    (DRESTRICT X {id | FST id <> a}) lo U stk ts
Proof
  Induct_on `U` >> simp[ld_joint_saved_def, occurrence_saved_ok_def] >>
  rpt strip_tac >> gvs[] >>
  simp[ld_joint_saved_def] >>
  qexists_tac `u` >> simp[] >>
  irule ld_joint_frame_drop_owner >>
  fs[occurrence_env_ok_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  gvs[LIST_REL_EL_EQN] >>
  qpat_x_assum `MEM (SOME id) _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qpat_x_assum `!n. n < LENGTH _ ==> occurrence_param_ok _ _ _ _`
    (qspec_then `n` mp_tac) >>
  strip_tac >> gvs[occurrence_param_ok_def]
QED
