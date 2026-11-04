(* Selected allocation instances; numeric source sites need not be functional. *)
Theory lowerDloadLifetime
Ancestors
  lowerDloadAllocation lowerDloadRelocation venomExecSemantics venomState
  finite_map pred_set arithmetic

Definition ld_site_entry_def:
  ld_site_entry (E:((num # num), num # num # num) fmap) owner bs bt sz <=>
    FLOOKUP E owner = SOME (bs,bt,sz)
End

Theorem ld_site_entry_update:
  ld_site_entry (E |+ (owner,(bs,bt,sz))) selected a b n <=>
  if selected = owner then (a = bs /\ b = bt /\ n = sz)
  else ld_site_entry E selected a b n
Proof
  simp[ld_site_entry_def, FLOOKUP_UPDATE] >>
  Cases_on `selected = owner` >> simp[] >> metis_tac[]
QED

Theorem ld_site_entry_empty_aliases:
  !frame.
  let E = FEMPTY |+ ((frame,0),(0,0,0)) |+ ((frame,1),(0,32,0)) in
    ld_site_entry E (frame,0) 0 0 0 /\
    ld_site_entry E (frame,1) 0 32 0
Proof
  simp[ld_site_entry_def, FLOOKUP_UPDATE]
QED

Theorem ld_site_entry_empty_range:
  ld_site_entry E owner bs bt 0 ==>
  ~(?d. d < 0 /\ a = bs+d /\ b = bt+d)
Proof
  simp[]
QED

Theorem ld_site_entry_endpoint:
  ld_site_entry E owner bs bt sz /\ ld_ptr_rel bs bt (n2w (bs+d)) y ==>
  y = n2w (bt+d)
Proof
  metis_tac[ld_ptr_rel_offset]
QED

Theorem ld_site_entry_alloca:
  ld_alloc_account keys d0 A s t /\ i.inst_id = j.inst_id /\
  i.inst_id NOTIN keys /\ i.inst_outputs = [out] /\
  j.inst_outputs = [out'] /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' ==>
  ?bs bt sz.
    ld_site_entry (E |+ ((frame,i.inst_id),(bs,bt,sz)))
      (frame,i.inst_id) bs bt sz /\
    FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas j.inst_id = SOME (bt,sz) /\
    lookup_var out s' = SOME (n2w bs) /\
    lookup_var out' t' = SOME (n2w bt) /\
    ld_ptr_rel bs bt (n2w bs) (n2w bt)
Proof
  strip_tac >> drule_all ld_alloc_account_outputs >>
  strip_tac >> qexistsl [`bs`, `bt`, `sz`] >>
  simp[ld_site_entry_def, FLOOKUP_UPDATE]
QED

(* A repeated instruction uses its saved selected instance: no fresh owner. *)
Theorem ld_site_entry_alloca_repeated:
  ld_site_entry E (frame,i.inst_id) bs bt sz /\
  i.inst_id = j.inst_id /\ i.inst_outputs = [out] /\
  j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t.vs_allocas j.inst_id = SOME (bt,sz) /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' ==>
  ld_site_entry E (frame,i.inst_id) bs bt sz /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t'.vs_allocas j.inst_id = SOME (bt,sz) /\
  lookup_var out s' = SOME (n2w bs) /\
  lookup_var out' t' = SOME (n2w bt)
Proof
  strip_tac >> gvs[exec_alloca_def, update_var_def, lookup_var_def,
                    FLOOKUP_UPDATE]
QED

(* Target-only scratch cannot overwrite a paired ordinary allocation. *)
Theorem ld_site_entry_scratch:
  ld_alloc_account keys d0 A s t /\ j.inst_id IN keys /\
  j.inst_outputs = [out] /\ exec_alloca j t (32w:bytes32) = OK t' /\
  (!id bs bt sz. ld_site_entry E (frame,id) bs bt sz ==>
    FLOOKUP s.vs_allocas id = SOME (bs,sz) /\
    FLOOKUP t.vs_allocas id = SOME (bt,sz)) ==>
  (!id bs bt sz. ld_site_entry E (frame,id) bs bt sz ==>
    FLOOKUP s.vs_allocas id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas id = SOME (bt,sz)) /\
  (!bs bt sz. ~ld_site_entry E (frame,j.inst_id) bs bt sz) /\
  (?bt. FLOOKUP t'.vs_allocas j.inst_id = SOME (bt,32))
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas j.inst_id = NONE` by
    (drule ld_alloc_account_disjoint >>
     simp[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >>
      `id <> j.inst_id` by (strip_tac >> gvs[]) >>
      gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE,
          AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  drule_all ld_alloc_account_scratch >> strip_tac >>
  irule ld_alloc_account_scratch_entry >>
  goal_assum (drule_at Any) >> simp[]
QED
