(* Exact heterogeneous tuple prefixes across registered decoder effects. *)
Theory entryReachBodyMemberPrefix
Ancestors
  valueEncodingDefs tupleMemoryLayout entryReachBodyOwnedRegion entryReachBodyRegisteredChild
  abiDecoderMemberInfos entryReachBodyCanonicalMemberEntry
  list rich_list arithmetic valueEncoding valueEncodingProps

Theorem entry_member_memory_indexed:
  !vs tvs d mem.
    LENGTH vs = LENGTH tvs ==>
    (tuple_in_memory vs tvs d mem <=>
     !i. i < LENGTH tvs ==>
       val_in_memory (EL i tvs) (EL i vs)
         (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- metis_tac[tuple_in_memory_element] >>
  qpat_x_assum `LENGTH vs = LENGTH tvs` mp_tac >>
  map_every qid_spec_tac [`mem`,`d`,`tvs`,`vs`] >>
  Induct >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> asm_rewrite_tac[] >> rpt strip_tac >>
  `SUC i <> 0` by decide_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
  asm_simp_tac std_ss [EL, TL, TAKE_def, MAP, SUM, LESS_MONO_EQ, ADD_ASSOC]
QED

Theorem entry_member_memory_preserved:
  LENGTH vs = LENGTH tvs /\ tuple_in_memory vs tvs d s.vs_memory /\
  LIST_REL val_wf tvs vs /\ entry_owned_region oid root extent d outsz s /\
  SUM (MAP type_memory_size tvs) <= outsz /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP type_memory_size tvs),sz)] s t /\ alloca_inv t ==>
  tuple_in_memory vs tvs d t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [entry_member_memory_indexed] >> rpt strip_tac >>
  `val_wf (EL i tvs) (EL i vs)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum irule >> simp[]) >>
  `val_in_memory (EL i tvs) (EL i vs)
     (d + SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory` by
    metis_tac[tuple_in_memory_element] >>
  drule tuple_element_interval >> strip_tac >>
  qpat_x_assum `entry_owned_region _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_region_def]) >>
  `mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
      (type_memory_size (EL i tvs)) t.vs_memory =
   mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
      (type_memory_size (EL i tvs)) s.vs_memory` by
    (irule entry_registered_child_slice >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
     asm_rewrite_tac[] >> rpt conj_tac >> decide_tac) >>
  irule val_in_memory_mem_agree >> conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`type_memory_size (EL i tvs)`,`s.vs_memory`] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem entry_member_memory_extend:
  LENGTH vs = LENGTH tvs /\ tuple_in_memory vs tvs d s.vs_memory /\
  LIST_REL val_wf tvs vs /\ entry_owned_region oid root extent d outsz s /\
  SUM (MAP type_memory_size tvs) <= outsz /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP type_memory_size tvs),sz)] s t /\ alloca_inv t /\
  val_in_memory tv v (d + SUM (MAP type_memory_size tvs)) t.vs_memory ==>
  tuple_in_memory (vs ++ [v]) (tvs ++ [tv]) d t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `tuple_in_memory vs tvs d t.vs_memory` by
    (irule entry_member_memory_preserved >> metis_tac[]) >>
  asm_simp_tac bool_ss [entry_member_memory_indexed, LENGTH_APPEND, LENGTH] >>
  rpt strip_tac >> Cases_on `i < LENGTH tvs`
  >- (`i - LENGTH tvs = 0` by decide_tac >>
      asm_simp_tac std_ss [EL_APPEND1, TAKE_APPEND, TAKE_0, APPEND_NIL] >>
      irule tuple_in_memory_element >> simp[]) >>
  `i = LENGTH tvs` by decide_tac >> gvs[EL_APPEND2, TAKE_APPEND1]
QED
