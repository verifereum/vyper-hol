(* Caller-derived and recursively stable resources for sparse store entry. *)
Theory fullStoreSlotsTypedEntry
Ancestors
  abiCallerTypeEnv vyperTypeSystem vyperTypeInvariants exprSimHypsDefs
  valueEncodingProps vyperValue finite_map list pred_set arithmetic words

Theorem store_slots_well_formed_submap[local]:
  small SUBMAP large /\ well_formed_type small ty ==> well_formed_type large ty
Proof
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[abi_caller_type_submap]
QED

Theorem store_slots_assignable_submap:
  !small ty. assignable_type small ty ==>
    !large. small SUBMAP large ==> assignable_type large ty
Proof
  recInduct assignable_type_ind >> rpt strip_tac >>
  gvs[Once assignable_type_def]
  >~ [`assignable_type large (StructT nsid)`]
  >- (Cases_on `FLOOKUP tenv nsid` >> gvs[] >>
      rename1 `FLOOKUP tenv nsid = SOME args` >>
      Cases_on `args` >> gvs[] >>
      drule_all FLOOKUP_SUBMAP >> strip_tac >>
      simp[assignable_type_def] >>
      conj_tac >- metis_tac[store_slots_well_formed_submap] >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum irule >> fs[EVERY_MEM] >>
      metis_tac[abi_caller_submap_delete])
  >~ [`assignable_type large (TupleT tys)`]
  >- (simp[assignable_type_def] >>
      conj_tac >- metis_tac[store_slots_well_formed_submap] >>
      fs[EVERY_MEM] >> metis_tac[])
  >~ [`assignable_type large (ArrayT elem bd)`]
  >- (simp[assignable_type_def] >> metis_tac[store_slots_well_formed_submap]) >>
  simp[assignable_type_def] >> metis_tac[store_slots_well_formed_submap]
QED

Theorem store_slots_assign_typed_entry:
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign tgt e) = SOME env' /\ expr_type e = ty ==>
  assignable_type (get_tenv cx) ty
Proof
  simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
    Once type_stmt_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem store_slots_assignable_memory_positive:
  assignable_type tenv ty /\ evaluate_type tenv ty = SOME tv ==>
  0 < type_memory_size tv
Proof
  strip_tac >> drule_all assignable_type_slot_size_pos >>
  simp[type_memory_size_slots]
QED

Theorem store_slots_assignable_struct_child:
  assignable_type tenv (StructT nsid) /\
  FLOOKUP tenv nsid = SOME (StructArgs fields) /\ MEM fld fields ==>
  assignable_type tenv (SND fld)
Proof
  strip_tac >>
  `assignable_type (tenv \\ nsid) (SND fld)` by
    gvs[assignable_type_def, EVERY_MEM] >>
  drule store_slots_assignable_submap >>
  disch_then irule >> simp[SUBMAP_DEF, FLOOKUP_DEF, FDOM_DOMSUB, DOMSUB_FAPPLY_THM]
QED

Theorem store_slots_positive_prefix:
  !xs f i. i < LENGTH xs /\ EVERY (\x. 0 < f x) xs ==>
    SUM (MAP f (TAKE i xs)) < SUM (MAP f xs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i` >> simp[]
QED

Theorem store_slots_positive_stride_count:
  !n k b limit. 0 < k /\ b + n * k < limit ==> n < limit
Proof
  rpt strip_tac >> `n <= n * k` by
    (Cases_on `k` >> gvs[arithmeticTheory.MULT_CLAUSES]) >> decide_tac
QED
