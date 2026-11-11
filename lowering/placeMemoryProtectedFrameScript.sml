Theory placeMemoryProtectedFrame
Ancestors
  placeMemoryCopyEffect exprSimAlloc exprLoweringProps compileEnv
  venomInst finite_map

(* A protected slice survives both writes, relative to the allocation-only
   reference state rather than to the scratch-copy state. *)
Theorem staging_copy_protected_bytes:
  r.vs_memory = s.vs_memory /\
  (!a k. a+k <= tmp \/ tmp+sz <= a ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  typed_copy_effect ctx func sn sb u t d n /\
  (a+k <= tmp \/ tmp+sz <= a) /\
  (a+k <= d \/ d+n <= a) ==>
  mem_bytes_at a k t.vs_memory = mem_bytes_at a k r.vs_memory
Proof
  strip_tac >> drule typed_copy_effect_bytes >>
  disch_then (qspecl_then [`k`, `a`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Reused allocation-map entries are protected only because the emitted
   ALLOCA is actually present in this function. *)
Theorem compile_alloc_buffer_immutable_disjoint:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  immutable_alloca_sep func cenv cx ee s /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
    SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables cenv.ce_module imms) name =
    SOME (tv,v) /\
  ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ tmp = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (tmp,n)) ==>
  off + type_memory_size tv <= tmp \/ tmp+n <= off
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >>
  disch_then (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[regions_disjoint_def] >>
  first_x_assum drule >> simp[mk_inst_def]
QED
