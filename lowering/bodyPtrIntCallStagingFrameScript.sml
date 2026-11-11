(* Reusable-site staging frames.  Ownership concerns the value footprint,
   not padding or the address age of an allocation. *)
Theory bodyPtrIntCallStagingFrame
Ancestors
  bodyPtrMakeArrayMemoryFrame bodyPtrIfExpAllocSource
  bodyPtrIntCallConfinement allocationPtr loweringPosts
  bodyPtrDefs compileEnv finite_map pred_set words list

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
