Theory placeMemoryProtectedFrame
Ancestors
  valueEncodingDefs placeMemoryCopyEffect exprSimAlloc exprLoweringProps compileEnv loweringStateRelDefs
  venomInst finite_map option alist

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
  disch_then (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac o CONJUNCT2) >>
  simp[] >> strip_tac >>
  gvs[regions_disjoint_def] >>
  first_x_assum drule >> simp[mk_inst_def]
QED

Theorem stmt_state_rel_immutable_alloca_sep_source:
  stmt_state_rel H ctx func cenv cx ee s /\
  (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) ==>
  immutable_alloca_sep func (cenv with ce_module := src) cx ee s
Proof
  rw[stmt_state_rel_def, IS_SOME_EXISTS] >-
    gvs[compile_env_component_equality] >>
  metis_tac[]
QED

Theorem immutable_local_slice_disjoint:
  stmt_state_rel H ctx func cenv cx ee s /\ cenv.ce_is_ctor /\
  (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
  FLOOKUP cenv.ce_module_vars (src,nm) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) nm = SOME (tv,iv) /\
  local_region cenv ee.scopes s name b len /\ b <= d /\ d+n <= b+len ==>
  off + type_memory_size tv <= d \/ d+n <= off
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx ee s` by
    metis_tac[stmt_state_rel_immutable_alloca_sep_source] >>
  pop_assum mp_tac >>
  simp[immutable_alloca_sep_def] >>
  disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac o CONJUNCT2) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _`
    (qspecl_then [`name`, `b`, `len`] mp_tac) >>
  fs[local_region_def, regions_disjoint_def] >> decide_tac
QED
