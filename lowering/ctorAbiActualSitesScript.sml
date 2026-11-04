(* Only actual ALLOCA instruction sites permit scratch memory effects.
   Old allocation-map entries at other instruction IDs remain unrestricted. *)
Theory ctorAbiActualSites
Ancestors
  ctorAbiActualFrame venomInst venomState venomMemDefs finite_map pred_set list

Definition ctor_actual_sites_def:
  ctor_actual_sites fn ids =
    {i | i IN ids /\ ?inst. MEM inst (fn_insts fn) /\
      inst.inst_opcode = ALLOCA /\ inst.inst_id = i}
End

Theorem ctor_actual_sites_subset:
  ctor_actual_sites fn ids SUBSET ids
Proof
  simp[ctor_actual_sites_def, SUBSET_DEF]
QED

Theorem ctor_actual_sites_mono:
  child SUBSET ids ==>
  ctor_actual_sites fn child SUBSET ctor_actual_sites fn ids
Proof
  simp[ctor_actual_sites_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ctor_actual_sites_idempotent[simp]:
  ctor_actual_sites fn (ctor_actual_sites fn ids) = ctor_actual_sites fn ids
Proof
  simp[ctor_actual_sites_def, EXTENSION] >> metis_tac[]
QED

Theorem ctor_actual_sites_empty[simp]:
  ctor_actual_sites fn {} = {}
Proof
  simp[ctor_actual_sites_def]
QED

Theorem ctor_actual_sites_exclude:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    inst.inst_id <> i) ==>
  i NOTIN ctor_actual_sites fn ids
Proof
  simp[ctor_actual_sites_def] >> metis_tac[]
QED

Theorem ctor_actual_sites_scratch:
  ctor_actual_scratch fn ids d n s /\ i IN ctor_actual_sites fn ids /\
  FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
  sz = 32 /\ regions_disjoint (d,n) (b,sz)
Proof
  simp[ctor_actual_sites_def, ctor_actual_scratch_def] >> metis_tac[]
QED

Theorem ctor_actual_sites_scratch_contained:
  ctor_actual_scratch fn ids d n s /\ child SUBSET ids /\
  i IN ctor_actual_sites fn child /\ FLOOKUP s.vs_allocas i = SOME (b,sz) /\
  d <= p /\ p+k <= d+n ==>
  sz = 32 /\ regions_disjoint (p,k) (b,sz)
Proof
  strip_tac >>
  `i IN ctor_actual_sites fn ids` by metis_tac[ctor_actual_sites_mono, SUBSET_DEF] >>
  drule_all ctor_actual_sites_scratch >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  irule ctor_actual_region_contained >> qexistsl [`d`, `n`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem ctor_actual_scratch_sites[simp]:
  ctor_actual_scratch fn (ctor_actual_sites fn ids) d n s <=>
  ctor_actual_scratch fn ids d n s
Proof
  simp[ctor_actual_scratch_def, ctor_actual_sites_def] >> metis_tac[]
QED
