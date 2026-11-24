(* Typed widening of the selected ternary arm, at its actual store cursor. *)
Theory bodyIfExpTypedArmMods
Ancestors
  bodyIfExpAllocMods bodyIfExpArmUnwrapMods bodyFullIfExpWidenCall
  typedCopyOriginPtr wideningZeroLayout exprSimIfExpWidenedPosts
  bodyFullPathHistory exprOperandVar exprLowering exprLoweringProps
  compileEnv loweringHalt fragExec loweringPosts vyperTypeSystem
  valueEncoding vyperValue arithmetic context typedMemoryCopy
  exprSimIfExpWidenedArm exprSimAggregateChildren allocaSiteResource
  venomMemDefs venomState finite_map words
Libs
  monadsyntax

Theorem ifexp_typed_arm_layout[local]:
  compile_ifexp_arm ce t sty vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout ce sty t /\
  type_widens_to tenv sty t /\ fn_has_code sm sb func ==>
  ?buf k src sc.
    compile_alloc_buffer (type_memory_bytes ce t) sm = (buf,k) /\
    unwrap_value ce vv k = (src,sc) /\
    compile_store_memory_typed ce buf.buf_operand t src sty sc = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm k func /\
    fn_has_code k sc func /\ fn_has_code sc sb func /\
    sm.cs_next_var <= k.cs_next_var /\ k.cs_next_var <= sc.cs_next_var /\
    sm.cs_next_id < k.cs_next_id /\ k.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >>
  drule_all_then assume_tac ifexp_widened_call_store_normalize >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce t) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,k)` >>
  Cases_on `unwrap_value ce vv k` >>
  rename1 `unwrap_value ce vv k = (src,sc)` >>
  Cases_on `compile_store_memory_typed ce buf.buf_operand t src sty sc` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (u,sf)` >>
  Cases_on `u` >>
  `op = buf.buf_operand /\ sb = sf` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     simp[compile_ifexp_arm_def,comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  qpat_x_assum `sb = sf` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sm k /\ ci_mono k sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
      cj 1 ci_mono_typed_memory_family,pairTheory.SND] >>
  `sm.cs_next_id < k.cs_next_id` by
    (drule_then strip_assume_tac compile_alloc_buffer_parts >> simp[]) >>
  qexistsl [`buf`,`k`,`src`,`sc`] >> simp[] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

Theorem ifexp_typed_arm_source_size[local]:
  expr_type e = t /\ post_value_type ce e = lowered_value_type ce e /\
  ~same_memory_layout ce (lowered_value_type ce e) t /\
  type_widens_to tenv (lowered_value_type ce e) t /\
  evaluate_type tenv (lowered_value_type ce e) = SOME rt /\
  evaluate_type tenv t = SOME dt /\ value_has_type rt v ==>
  post_value_type ce e <> expr_type e /\ ~is_bytestring_type t /\
  0 < type_memory_size rt /\ val_footprint rt v = type_memory_size rt
Proof
  strip_tac >>
  `lowered_value_type ce e <> t` by
    (strip_tac >> fs[same_memory_layout_def,punnable_reflexive]) >>
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `0 < type_memory_size rt` by
    (Cases_on `type_memory_size rt = 0` >> simp[] >>
     drule_all_then assume_tac type_widens_to_zero_layout >> fs[]) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  simp[] >> irule evaluated_nonbytes_footprint >> metis_tac[]
QED

Theorem ifexp_typed_arm_window_disjoint[local]:
  alloca_inv s /\ src_id <> dst_id /\
  FLOOKUP s.vs_allocas src_id = SOME (a,cap) /\
  FLOOKUP s.vs_allocas dst_id = SOME (b,n) /\
  0 < m /\ 0 < n /\ a <= w /\ w + m <= a + cap ==>
  w + m <= b \/ b + n <= w
Proof
  strip_tac >> drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
