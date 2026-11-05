Theory externalReturnReuseResource
Ancestors
  allocaSiteResource abiAllocationHistory venomMemDefs venomState finite_map
  words arithmetic

Theorem return_owner_subwindow_below:
  alloca_inv s /\ FLOOKUP s.vs_allocas owner = SOME (p,n) /\
  p <= q /\ q + len <= p + n ==> q + len <= s.vs_alloca_next
Proof
  strip_tac >> drule_all alloca_site_registered_below >> decide_tac
QED

Theorem return_owner_subwindow_disjoint:
  alloca_inv s /\ FLOOKUP s.vs_allocas owner = SOME (p,n) /\
  p <= q /\ q + len <= p + n /\ owner <> site /\
  FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (q,len) (b,sz)
Proof
  strip_tac >> drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem return_optional_owner_subwindow_below:
  alloca_inv s /\
  (case owner of NONE => p+n <= s.vs_alloca_next
   | SOME aid => FLOOKUP s.vs_allocas aid = SOME (p,n)) /\
  p <= q /\ q+len <= p+n ==> q+len <= s.vs_alloca_next
Proof
  Cases_on `owner` >> simp[] >> strip_tac >>
  drule_all alloca_site_registered_below >> decide_tac
QED

Theorem return_optional_owner_subwindow_disjoint:
  alloca_inv s /\
  (case owner of
     NONE => !site b sz. FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
       venomMemDefs$regions_disjoint (p,n) (b,sz)
   | SOME aid => FLOOKUP s.vs_allocas aid = SOME (p,n)) /\
  p <= q /\ q+len <= p+n /\ owner <> SOME site /\
  FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (q,len) (b,sz)
Proof
  Cases_on `owner` >> simp[] >> strip_tac
  >- (first_x_assum drule >>
      simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem return_registered_literal32_size:
  abi_alloca_history (fn_insts func) s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_operands = [Lit 32w] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==> sz = 32
Proof
  strip_tac >> drule_all abi_alloca_history_function_size >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED
