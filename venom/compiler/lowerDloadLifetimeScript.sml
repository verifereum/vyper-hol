(* Selected allocation instances; numeric source sites need not be functional. *)
Theory lowerDloadLifetime
Ancestors
  lowerDloadAllocation lowerDloadRelocation venomExecSemantics venomState
  finite_map pred_set arithmetic ptrDiscipline words venomLayout list

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

(* Natural DALLOCA provenance needs a no-wrap bound, not static-map ownership. *)
Theorem ld_dalloca_provenance:
  i.inst_opcode = DALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ eval_operand op s = SOME n /\
  step_inst_base i s = OK s' /\
  w2n s.vs_fmp + ceil32 (w2n n) < dimword (:256) ==>
  out_prov PG G i s' = SOME (w2n s.vs_fmp, ceil32 (w2n n))
Proof
  strip_tac >>
  gvs[step_inst_base_def, out_prov_def, update_var_def, lookup_var_def] >>
  simp[word_add_def, w2n_n2w] >>
  `ceil32 (w2n n) < dimword (:256)` by decide_tac >>
  simp[LESS_MOD, FLOOKUP_UPDATE]
QED

Theorem ld_dalloca_static_separation:
  allocas_below_fmp s /\ FLOOKUP s.vs_allocas id = SOME (b,sz) /\
  a < b + sz ==> a < w2n s.vs_fmp
Proof
  simp[allocas_below_fmp_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

(* Inherited owners are indexed with PARAM, not recovered from local allocas. *)
Theorem ld_site_entry_param:
  LIST_REL (\p q. (p = NONE /\ q = NONE) \/
    ?owner bs bt sz. p = SOME (owner,bs,sz) /\ q = SOME (bt,sz) /\
      ld_site_entry E owner bs bt sz) APG TPG /\
  w2n idx < LENGTH APG /\ EL (w2n idx) APG = SOME (owner,bs,sz) /\
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] ==>
  out_prov (MAP (OPTION_MAP SND) APG) G i s = SOME (bs,sz) /\
  ?bt. out_prov TPG H i t = SOME (bt,sz) /\
       ld_site_entry E owner bs bt sz
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `w2n idx` mp_tac) >>
  simp[] >> strip_tac >>
  simp[out_prov_def, EL_MAP] >> metis_tac[]
QED

(* Selection follows the same first-pointer rule as affine provenance. *)
Theorem ld_site_entry_first_prov:
  LIST_REL (\op op'.
    (op_prov G op = NONE /\ op_prov H op' = NONE) \/
    ?owner bs bt sz. op_prov G op = SOME (bs,sz) /\
      op_prov H op' = SOME (bt,sz) /\ ld_site_entry E owner bs bt sz) ops ops' ==>
  (first_prov G ops = NONE /\ first_prov H ops' = NONE) \/
  ?owner bs bt sz. first_prov G ops = SOME (bs,sz) /\
    first_prov H ops' = SOME (bt,sz) /\ ld_site_entry E owner bs bt sz
Proof
  qid_spec_tac `ops'` >> Induct_on `ops` >>
  Cases_on `ops'` >> simp[first_prov_def] >> rpt strip_tac >>
  gvs[first_prov_def] >> metis_tac[]
QED

Theorem ld_site_entry_affine:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB \/ i.inst_opcode = ASSIGN) /\
  j.inst_opcode = i.inst_opcode /\
  LIST_REL (\op op'.
    (op_prov G op = NONE /\ op_prov H op' = NONE) \/
    ?owner bs bt sz. op_prov G op = SOME (bs,sz) /\
      op_prov H op' = SOME (bt,sz) /\ ld_site_entry E owner bs bt sz)
    i.inst_operands j.inst_operands ==>
  (out_prov PG G i s = NONE /\ out_prov QG H j t = NONE) \/
  ?owner bs bt sz. out_prov PG G i s = SOME (bs,sz) /\
    out_prov QG H j t = SOME (bt,sz) /\ ld_site_entry E owner bs bt sz
Proof
  strip_tac >> drule ld_site_entry_first_prov >>
  gvs[out_prov_def]
QED

(* Empty dynamic intervals may coincide with a static empty site's base. *)
Theorem ld_dalloca_zero_alias:
  i.inst_opcode = DALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ eval_operand op s = SOME (0w:bytes32) /\
  step_inst_base i s = OK s' /\
  FLOOKUP s.vs_allocas id = SOME (w2n s.vs_fmp,0) ==>
  out_prov PG G i s' = FLOOKUP s'.vs_allocas id /\
  s'.vs_fmp = s.vs_fmp
Proof
  simp[step_inst_base_def, ceil32_def] >> strip_tac >>
  gvs[out_prov_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      WORD_ADD_0]
QED

Theorem ld_site_entry_dalloca:
  i.inst_opcode = DALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ eval_operand op s = SOME n /\
  step_inst_base i s = OK s' /\
  j.inst_opcode = DALLOCA /\ j.inst_operands = [op'] /\
  j.inst_outputs = [out'] /\ eval_operand op' t = SOME n /\
  step_inst_base j t = OK t' /\
  w2n s.vs_fmp + ceil32 (w2n n) < dimword (:256) /\
  w2n t.vs_fmp + ceil32 (w2n n) < dimword (:256) ==>
  ?bs bt sz.
    out_prov PG G i s' = SOME (bs,sz) /\
    out_prov QG H j t' = SOME (bt,sz) /\
    ld_site_entry (E |+ (owner,(bs,bt,sz))) owner bs bt sz
Proof
  strip_tac >>
  qexistsl [`w2n s.vs_fmp`, `w2n t.vs_fmp`, `ceil32 (w2n n)`] >>
  conj_tac >- (irule ld_dalloca_provenance >> metis_tac[]) >>
  conj_tac >- (irule ld_dalloca_provenance >> metis_tac[]) >>
  simp[ld_site_entry_def, FLOOKUP_UPDATE]
QED
