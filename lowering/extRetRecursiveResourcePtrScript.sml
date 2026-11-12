Theory extRetRecursiveResourcePtr
Ancestors
  extRetScratchResourcePtr extRetEncoderScratchSitesPtr allocaSiteResource
  allocationPtr venomState venomMemDefs finite_map pred_set list arithmetic

Definition encoder_resource_def:
  encoder_resource ctx fn sites q len protected s <=>
    scratch_resource ctx fn sites q len s /\
    (!id b n. MEM (id,b,n) protected ==>
      FLOOKUP s.vs_allocas id = SOME (b,n) /\ id NOTIN sites /\
      scratch_resource ctx fn sites b n s)
End

Theorem encoder_resource_restrict:
  encoder_resource ctx fn sites q len protected s /\ children SUBSET sites ==>
  encoder_resource ctx fn children q len protected s
Proof
  simp[encoder_resource_def] >> strip_tac >>
  conj_tac >- (irule scratch_resource_restrict >> qexistsl_tac [`len`,`q`,`sites`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[SUBSET_DEF] >>
  irule scratch_resource_restrict >> qexistsl_tac [`n`,`b`,`sites`] >> simp[]
QED

Theorem encoder_resource_fields:
  encoder_resource ctx fn sites q len protected s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  encoder_resource ctx fn sites q len protected t
Proof
  simp[encoder_resource_def] >> strip_tac >>
  conj_tac >- (irule scratch_resource_fields >> qexists_tac `s` >> simp[]) >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  irule scratch_resource_fields >> qexists_tac `s` >> simp[]
QED

Theorem encoder_resource_registered_intro:
  scratch_resource ctx fn sites q len s /\
  (!id b n. MEM (id,b,n) protected ==>
    FLOOKUP s.vs_allocas id = SOME (b,n) /\ id NOTIN sites) ==>
  encoder_resource ctx fn sites q len protected s
Proof
  strip_tac >> simp[encoder_resource_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[scratch_resource_def] >>
  conj_tac >- metis_tac[alloca_site_registered_below] >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  strip_tac >> irule alloca_site_registered_disjoint >>
  metis_tac[]
QED

Theorem encoder_resource_push:
  encoder_resource ctx fn sites q len protected s /\
  children SUBSET sites /\ id NOTIN children /\
  FLOOKUP s.vs_allocas id = SOME (b,n) ==>
  encoder_resource ctx fn children q len ((id,b,n)::protected) s
Proof
  strip_tac >> drule_all encoder_resource_restrict >> strip_tac >>
  irule encoder_resource_registered_intro >>
  gvs[encoder_resource_def] >> metis_tac[]
QED

Theorem encoder_resource_protected:
  encoder_resource ctx fn sites q len protected s /\ MEM (id,b,n) protected ==>
  FLOOKUP s.vs_allocas id = SOME (b,n) /\ id NOTIN sites /\
  scratch_resource ctx fn sites b n s
Proof
  simp[encoder_resource_def] >> metis_tac[]
QED
