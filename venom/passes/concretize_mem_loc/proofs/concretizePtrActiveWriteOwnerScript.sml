Theory concretizePtrActiveWriteOwner
Ancestors
  concretizePtrPairedFields concretizePtrActivationBirths concretizePtrOwnerSeeds
  concretizePtrAllocationOwnership concretizePtrOwnerPath
  ptrDiscipline list finite_map

Theorem ptr_paired_write_owner_relocation:
  ptr_paired_write_owner lo positions (reloc:num -> num) xs
    (tokens,registry,births,PT,TG,saved,entries) /\
  x IN xs /\ lo <= x /\
  ptr_birth_slices post tokens births /\
  LENGTH tokens = SUC (LENGTH post.po_stack) /\
  ptr_active_alloc_geometry
    (post.po_state :: MAP (\f. f.cf_state) post.po_stack) /\
  d <= LENGTH post.po_stack /\
  FLOOKUP (ptr_owner_view d post).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b + sz /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
  reloc x = pa + (x-b)
Proof
  strip_tac >> drule_all ptr_paired_write_owner_byte >> strip_tac
  >- decide_tac >>
  rename1 `MEM token tokens` >>
  gvs[MEM_EL] >>
  `LENGTH post.po_stack - n <= LENGTH post.po_stack /\
   LENGTH post.po_stack - (LENGTH post.po_stack - n) = n` by decide_tac >>
  `FLOOKUP (ptr_owner_view (LENGTH post.po_stack - n) post).cf_state.vs_allocas
     aid' = SOME (base',sz')` by
    (qpat_x_assum `ptr_birth_slices _ _ _` mp_tac >>
     simp[ptr_birth_slices_def] >>
     disch_then (qspecl_then [`LENGTH post.po_stack - n`,`aid'`] mp_tac) >>
     simp[]) >>
  `d = LENGTH post.po_stack - n /\ aid = aid'` by
    (irule ptr_owner_overlap_unique >>
     goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >>
     qexistsl_tac [`b`,`base'`,`sz`,`sz'`,`base' + k`] >> simp[]) >>
  gvs[] >> decide_tac
QED

Theorem ptr_paired_write_owner_fixed:
  ptr_paired_write_owner lo positions (reloc:num -> num) xs
    (tokens,registry,births,PT,TG,saved,entries) /\
  x IN xs /\ x < lo /\ ptr_birth_slices post tokens births /\
  LENGTH tokens = SUC (LENGTH post.po_stack) /\
  (!d. d <= LENGTH post.po_stack ==>
    allocas_from lo (ptr_owner_view d post).cf_state) ==>
  reloc x = x
Proof
  strip_tac >> drule_all ptr_paired_write_owner_byte >> strip_tac >>
  rename1 `FLOOKUP births (token,aid) = SOME (b0,sz)` >>
  gvs[MEM_EL] >>
  `LENGTH post.po_stack - n <= LENGTH post.po_stack /\
   LENGTH post.po_stack - (LENGTH post.po_stack - n) = n` by decide_tac >>
  `FLOOKUP (ptr_owner_view (LENGTH post.po_stack - n) post).cf_state.vs_allocas
     aid = SOME (b0,sz)` by
    (qpat_x_assum `ptr_birth_slices _ _ _` mp_tac >>
     simp[ptr_birth_slices_def] >>
     disch_then (qspecl_then [`LENGTH post.po_stack - n`,`aid`] mp_tac) >>
     simp[]) >>
  first_x_assum (qspec_then `LENGTH post.po_stack - n` mp_tac) >>
  simp[allocas_from_def] >>
  disch_then drule >> decide_tac
QED
