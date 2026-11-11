(* Reusable-site staging frames.  Ownership concerns the value footprint,
   not padding or the address age of an allocation. *)
Theory bodyPtrIntCallStagingFrame
Ancestors
  bodyPtrMakeArrayMemoryFrame bodyPtrIfExpAllocSource
  bodyPtrIntCallConfinement allocationPtr loweringPosts
  bodyPtrDefs compileEnv finite_map pred_set words list
  exprSimPtrTopLevelStorageFrame

Theorem intcall_located_footprint_separation:
  vv_at ce cx ty sa sb es raw (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  (!aid a k. aid < sb.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,k) ==> regions_disjoint b n a k) /\
  (!name a k. local_region ce es.scopes s name a k ==>
    regions_disjoint b n a k) ==>
  val_wf tv v /\
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    ~(b <= i /\ i < b+n)
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[] >>
  fs[regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule_all >> decide_tac
QED

(* Only the represented footprint must survive; padding is not read.  The
   general shrinking-taint frame is imported rather than duplicated here. *)
Theorem intcall_located_robust_confined_write:
  vv_at ce cx ty sa sb es raw (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  (!aid a k. aid < sb.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,k) ==> regions_disjoint b n a k) /\
  (!name a k. local_region ce es.scopes s name a k ==>
    regions_disjoint b n a k) /\
  (!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 mem' = mem_bytes_at i 1 s.vs_memory) /\
  (!i. ~(b <= i /\ i < b+n) /\ i IN T' ==> i IN dirty) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==>
    val_in_memory tv v (w2n w) m) ==>
  !m. mem_agree_outside T' mem' m ==> val_in_memory tv v (w2n w) m
Proof
  strip_tac >>
  drule_all intcall_located_footprint_separation >> strip_tac >>
  rpt strip_tac >> irule toplevel_robust_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `mem'`, `dirty`, `T'`,
                 `{i | b <= i /\ i < b+n}`] >> simp[]
QED

(* Whole-site separation publishes the fixed protected-set interface even
   when the staging ALLOCA reuses an address below the runtime frontier. *)
Theorem intcall_separated_site_outside:
  (!aid a k. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,k) ==> regions_disjoint b n a k) /\
  (!name a k. local_region ce es.scopes s name a k ==>
    regions_disjoint b n a k) ==>
  intcall_site_outside (intcall_protected ce es sa s) (b,n)
Proof
  strip_tac >>
  rewrite_tac[intcall_site_outside_def, IN_DISJOINT] >>
  strip_tac >>
  fs[intcall_protected_def] >>
  gvs[regions_disjoint_def] >>
  first_x_assum drule_all >> decide_tac
QED
