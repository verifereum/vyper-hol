(* Static source types encode every word of their storage region. *)
Theory vyperStorageCoverage
Ancestors
  vyperABI vyperStorage vyperTyping vyperValue vyperTypeDefaults list

Theorem evaluate_static_encoding_coverage[local]:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv /\ ~vyper_is_dynamic tenv ty ==>
    !v writes i. encode_value tv v = SOME writes /\ i < type_slot_size tv ==>
      MEM i (MAP FST writes)) /\
  (!tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs /\
    ~vyper_any_dynamic tenv ts /\
    EVERY (\tv. !v writes i. encode_value tv v = SOME writes /\
      i < type_slot_size tv ==> MEM i (MAP FST writes)) acc ==>
    EVERY (\tv. !v writes i. encode_value tv v = SOME writes /\
      i < type_slot_size tv ==> MEM i (MAP FST writes)) tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >- (Cases_on `bt`
      >> gvs[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs()]
      >> rpt strip_tac
      >> gvs[encode_value_def, type_slot_size_def, AllCaseEqs()]
      >> gvs[vyper_is_dynamic_def])
  >- (simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs()]
      >> rpt strip_tac >> gvs[]
      >> Cases_on `v` >> gvs[Once encode_value_def]
      >> rename1 `ArrayV av` >> Cases_on `av` >> gvs[Once encode_value_def]
      >> gvs[type_slot_size_def, EVERY_MEM]
      >> drule_all encode_tuple_coverage >> simp[])
  >- (Cases_on `bd` >> simp[vyper_is_dynamic_def]
      >> simp[evaluate_type_def, AllCaseEqs()]
      >> rpt strip_tac >> gvs[type_slot_size_def]
      >> irule encode_fixed_array_coverage >> metis_tac[])
  >- (simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs()]
      >> rpt strip_tac >> gvs[]
      >> `LENGTH tvs = LENGTH args` by (drule evaluate_types_length >> simp[])
      >> Cases_on `v` >> gvs[Once encode_value_def, type_slot_size_def]
      >> `!nm tv. MEM (nm,tv) (ZIP (MAP FST args,tvs)) ==>
            !v ws j. encode_value tv v = SOME ws /\ j < type_slot_size tv ==>
              MEM j (MAP FST ws)` by
         (rpt strip_tac
          >> gvs[MEM_ZIP, EVERY_MEM]
          >> metis_tac[MEM_EL])
      >> drule_all encode_struct_coverage >> simp[])
  >- (simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs()]
      >> rpt strip_tac >> gvs[encode_value_def, type_slot_size_def, AllCaseEqs()])
  >- simp[evaluate_type_def, vyper_is_dynamic_def, type_slot_size_def]
  >- (rpt strip_tac >> gvs[evaluate_type_def, vyper_is_dynamic_def, EVERY_MEM]
      >> metis_tac[])
  >> simp[Once evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem encode_value_live_written:
  !tenv ty tv v writes i.
    evaluate_type tenv ty = SOME tv /\ ~vyper_is_dynamic tenv ty /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    i < type_slot_size tv ==>
    MEM i (MAP FST writes)
Proof
  metis_tac[evaluate_static_encoding_coverage]
QED
