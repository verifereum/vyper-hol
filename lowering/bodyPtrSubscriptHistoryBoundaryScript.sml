(* Source-owner elimination only: memory representation is a separate premise. *)
Theory bodyPtrSubscriptHistoryBoundary
Ancestors
  bodyPtrSubscriptCurrentMemory vyperState rich_list loweringPosts
  exprSimProps pair arithmetic

Theorem read_popped_owner:
  !history tv path v.
    read_popped tv path history = SOME v ==>
    ?prefix owner ptv suffix.
      MEM (prefix,owner) history /\ path = prefix ++ suffix /\
      subscripts_type tv prefix = SOME ptv /\
      evaluate_subscripts ptv owner suffix = INL v
Proof
  Induct >> simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[read_popped_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem mem_path_offset_append_decompose:
  !prefix tv suffix k ctv.
    mem_path_offset tv (prefix ++ suffix) = SOME (k,ctv) ==>
    ?d ptv r.
      mem_path_offset tv prefix = SOME (d,ptv) /\
      mem_path_offset ptv suffix = SOME (r,ctv) /\ k = d + r
Proof
  Induct >> simp[mem_path_offset_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  first_x_assum drule >> strip_tac >>
  simp[mem_path_offset_def] >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED

(* This sufficient owner premise is not a consequence of ghost_inv. *)
Theorem read_popped_in_memory:
  !tv path history v k ctv base mem.
    read_popped tv path history = SOME v /\
    mem_path_offset tv path = SOME (k,ctv) /\
    (!prefix owner d ptv.
      MEM (prefix,owner) history /\
      mem_path_offset tv prefix = SOME (d,ptv) ==>
      value_has_type ptv owner /\ well_formed_type_value ptv /\
      val_in_memory ptv owner (base + d) mem) ==>
    val_in_memory ctv v (base + k) mem
Proof
  rpt strip_tac >> drule read_popped_owner >> strip_tac >>
  gvs[] >> drule mem_path_offset_append_decompose >> strip_tac >>
  qpat_assum `mem_path_offset tv prefix = SOME _`
    (mp_then Any strip_assume_tac mem_path_offset_sound) >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all mem_path_offset_current_value >>
  pure_rewrite_tac[ADD_ASSOC] >> disch_then ACCEPT_TAC
QED

Theorem read_memory_path_in_memory:
  !entry path v k ctv base mem.
    read_memory_path entry path = INL v /\
    mem_path_offset entry.type path = SOME (k,ctv) /\
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    val_in_memory entry.type entry.value base mem /\
    (!prefix owner d ptv.
      MEM (prefix,owner) entry.popped /\
      mem_path_offset entry.type prefix = SOME (d,ptv) ==>
      value_has_type ptv owner /\ well_formed_type_value ptv /\
      val_in_memory ptv owner (base + d) mem) ==>
    val_in_memory ctv v (base + k) mem
Proof
  rpt gen_tac >>
  pure_rewrite_tac[read_memory_path_def, AllCaseEqs()] >>
  strip_tac >> FULL_SIMP_TAC (std_ss) []
  >- (drule_all mem_path_offset_current_value >> disch_then ACCEPT_TAC) >>
  FULL_SIMP_TAC std_ss [AllCaseEqs()] >>
  drule_all read_popped_in_memory >> disch_then ACCEPT_TAC
QED
