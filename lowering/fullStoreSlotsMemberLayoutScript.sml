(* Robust tuple resources for recursive sparse stores. *)
Theory fullStoreSlotsMemberLayout
Ancestors
  typedCopyLayoutPtr exprSimAggregateEncoding valueTypingMemoryProps
  valueEncoding valueEncodingDefs vyperTyping loweringPosts exprSimProps
  bodyPtrDefs vyperLookupStorage list rich_list arithmetic

Theorem store_slots_member_head_resources:
  values_have_types (tv::tvs) (v::vs) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    tuple_in_memory (v::vs) (tv::tvs) (addr+mo) m) /\
  mo + type_memory_size_list (tv::tvs) <= capacity /\
  addr + mo + type_memory_size_list (tv::tvs) <= frontier /\
  addr + mo + type_memory_size_list (tv::tvs) < dimword(:256) /\
  slot + so + type_slot_size_list (tv::tvs) <= dimword(:256) ==>
  value_has_type tv v /\
  mo + val_store_size tv v <= capacity /\
  addr + mo + val_store_size tv v <= frontier /\
  addr + mo + type_memory_size tv < dimword(:256) /\
  slot + so + type_slot_size tv <= dimword(:256) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory tv v (addr+mo) m)
Proof
  strip_tac >>
  `val_store_size tv v <= type_memory_size_list (tv::tvs)` by
    (qspecl_then [`tv::tvs`,`v::vs`,`0`] mp_tac
      tuple_child_store_size_contained >>
     simp[valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  gvs[value_has_type_def,valueEncodingDefsTheory.val_in_memory_def,
    type_memory_size_def,vyperValueTheory.type_slot_size_def] >>
  rpt conj_tac >> decide_tac
QED

Theorem store_slots_member_tail_resources:
  values_have_types (tv::tvs) (v::vs) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    tuple_in_memory (v::vs) (tv::tvs) (addr+mo) m) /\
  mo = 32*so /\
  mo + type_memory_size_list (tv::tvs) <= capacity /\
  addr + mo + type_memory_size_list (tv::tvs) <= frontier /\
  addr + mo + type_memory_size_list (tv::tvs) < dimword(:256) /\
  slot + so + type_slot_size_list (tv::tvs) <= dimword(:256) ==>
  values_have_types tvs vs /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    tuple_in_memory vs tvs (addr+mo+type_memory_size tv) m) /\
  mo + type_memory_size tv = 32*(so+type_slot_size tv) /\
  mo + type_memory_size tv + type_memory_size_list tvs <= capacity /\
  addr + (mo+type_memory_size tv) + type_memory_size_list tvs <= frontier /\
  addr + (mo+type_memory_size tv) + type_memory_size_list tvs < dimword(:256) /\
  slot + (so+type_slot_size tv) + type_slot_size_list tvs <= dimword(:256)
Proof
  strip_tac >>
  gvs[value_has_type_def,valueEncodingDefsTheory.val_in_memory_def,
    type_memory_size_def,vyperValueTheory.type_slot_size_def] >>
  simp[valueEncodingPropsTheory.type_memory_size_slots,LEFT_ADD_DISTRIB] >>
  decide_tac
QED

Theorem store_slots_member_support_cons:
  (!k. MEM k hs <=> ?writes j. encode_value tv v = SOME writes /\
    MEM j (MAP FST writes) /\ k = so+j) /\
  (!k. MEM k ts <=> ?i writes j. i < LENGTH tvs /\
    encode_value (EL i tvs) (EL i vs) = SOME writes /\
    MEM j (MAP FST writes) /\
    k = (so+type_slot_size tv) + tuple_prefix_slot_size i tvs + j) ==>
  (!k. MEM k (hs++ts) <=> ?i writes j. i < LENGTH (tv::tvs) /\
    encode_value (EL i (tv::tvs)) (EL i (v::vs)) = SOME writes /\
    MEM j (MAP FST writes) /\
    k = so + tuple_prefix_slot_size i (tv::tvs) + j)
Proof
  strip_tac >> gen_tac >> simp[MEM_APPEND] >>
  qpat_x_assum `!k. MEM k hs <=> _` kall_tac >>
  qpat_x_assum `!k. MEM k ts <=> _` kall_tac >> eq_tac
  >- (strip_tac
      >- (qexists_tac `0` >> simp[vyperStateTheory.tuple_prefix_slot_size_def] >> metis_tac[]) >>
      qexistsl_tac [`SUC i`,`writes`,`j`] >>
      pure_rewrite_tac [EL,HD,TL,vyperStateTheory.tuple_prefix_slot_size_def] >>
      metis_tac[LESS_MONO_EQ]) >>
  strip_tac >> Cases_on `i` >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE
    [EL,HD,TL,vyperStateTheory.tuple_prefix_slot_size_def,ADD_CLAUSES]) >>
  metis_tac[LESS_MONO_EQ,ADD_ASSOC]
QED
