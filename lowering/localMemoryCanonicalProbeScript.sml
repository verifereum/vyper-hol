(* Memory values retain their semantic posts when pointer metadata is erased. *)
Theory localMemoryCanonicalProbe
Ancestors
  localMemoryRhsProbe valueCopyBytes bodyPtrDefs loweringPosts exprSimMemDefs
  exprLowering compileEnv context venomState

Theorem memory_vv_canonical_resources:
  p.ptr_location = LocMemory /\ p.ptr_operand = Var xs ==>
  (ptr_vv_ok cx ty raw (LocatedValue ann p) es G tn s <=>
   ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) es G tn s) /\
  (vv_store_bound cx ty lt es raw (LocatedValue ann p) s <=>
   vv_store_bound cx ty lt es raw
     (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s)
Proof
  simp[ptr_vv_ok_def,vv_store_bound_def,mk_ptr_def]
QED

Theorem memory_vv_canonical_post:
  vv_post H ctx func cenv cx e origin sa0 sa1 s0 es raw
    (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var xs /\
  post_value_type cenv e = ty /\ ~is_word_type ty ==>
  vv_post H ctx func cenv cx e origin sa0 sa1 s0 es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  unwrap_value cenv (LocatedValue ann p) sa = (Var xs,sa)
Proof
  strip_tac >>
  `~is_word_type ann` by
    (fs[vv_post_def,vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  conj_tac
  >- (gvs[vv_post_def,vv_holds_def,vv_at_def,vv_own_def,vv_place_ptr_def,
          vv_storage_live_def,mk_ptr_def] >> metis_tac[]) >>
  simp[unwrap_value_def,comp_return_def]
QED
