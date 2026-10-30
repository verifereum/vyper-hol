Theory vyperEventCompatibility
Ancestors
  vyperTypeSystem vyperTypeContract vyperABI vyperEvent vyperTyping vyperValue list

Theorem event_arg_compatible_abi_type:
  (!fty aty. event_arg_compatible fty aty ==>
    !tenv. vyper_to_abi_type tenv fty = vyper_to_abi_type tenv aty) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !tenv. vyper_to_abi_types tenv fts = vyper_to_abi_types tenv ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def, vyper_to_abi_type_def,
     vyper_base_to_abi_type_def] >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def]
QED

Theorem event_arg_compatible_topic:
  event_indexable_type fty /\ event_arg_compatible fty aty ==>
  encode_event_topic fty v = encode_event_topic aty v
Proof
  Cases_on `fty` >> Cases_on `aty` >>
  gvs[event_indexable_type_def, event_arg_compatible_def] >>
  rename1 `event_arg_compatible (BaseT fb) (BaseT ab)` >>
  Cases_on `fb` >> Cases_on `ab` >>
  gvs[event_arg_compatible_def, encode_event_topic_def,
      is_event_bytestring_type_def, event_topic_word_def] >>
  Cases_on `b` >> Cases_on `b'` >>
  gvs[event_arg_compatible_def, encode_event_topic_def,
      is_event_bytestring_type_def, event_topic_word_def]
QED

Theorem event_arg_compatible_defaults:
  (!fty aty. event_arg_compatible fty aty ==>
    !tenv ftv atv. evaluate_type tenv fty = SOME ftv /\
      evaluate_type tenv aty = SOME atv ==>
      default_to_abi ftv = default_to_abi atv /\
      default_value ftv = default_value atv) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !tenv ftvs atvs. OPT_MMAP (evaluate_type tenv) fts = SOME ftvs /\
      OPT_MMAP (evaluate_type tenv) ats = SOME atvs ==>
      MAP default_to_abi ftvs = MAP default_to_abi atvs /\
      MAP default_value ftvs = MAP default_value atvs)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def, evaluate_type_def,
     evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  gvs[default_to_abi_def, default_value_def, default_to_abi_list_MAP] >>
  res_tac >> gvs[evaluate_type_def, evaluate_types_OPT_MMAP,
    default_to_abi_def, default_value_def, default_value_tuple_MAP]
QED

Theorem vyper_to_abi_same_cong:
  (!v. vyper_to_abi tenv ft v = vyper_to_abi tenv at v) ==>
  !vs. vyper_to_abi_same tenv ft vs = vyper_to_abi_same tenv at vs
Proof
  strip_tac >> Induct >> simp[vyper_to_abi_def]
QED

Theorem vyper_to_abi_sparse_cong:
  (!v. vyper_to_abi tenv ft v = vyper_to_abi tenv at v) /\
  default_to_abi ftv = default_to_abi atv ==>
  !n sparse. vyper_to_abi_sparse tenv ft ftv n sparse =
             vyper_to_abi_sparse tenv at atv n sparse
Proof
  strip_tac >> Induct >> simp[vyper_to_abi_def]
QED

Theorem event_arg_compatible_abi_value:
  (!fty aty. event_arg_compatible fty aty ==>
    !tenv. well_formed_type tenv fty /\ well_formed_type tenv aty ==>
    !v. vyper_to_abi tenv fty v = vyper_to_abi tenv aty v) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !tenv. EVERY (well_formed_type tenv) fts /\ EVERY (well_formed_type tenv) ats ==>
    !vs. vyper_to_abi_list tenv fts vs = vyper_to_abi_list tenv ats vs)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def] >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS, evaluate_type_def,
      evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  (Cases_on `v` ORELSE Cases_on `vs`) >>
  gvs[vyper_to_abi_def, vyper_to_abi_base_def] >>
  Cases_on `a` >> gvs[vyper_to_abi_def] >>
  TRY (rename1 `event_arg_compatible fty aty` >>
    `!v. vyper_to_abi tenv fty v = vyper_to_abi tenv aty v` by metis_tac[] >>
    `default_to_abi tv = default_to_abi tv'` by
      metis_tac[cj 1 event_arg_compatible_defaults] >>
    `!vs. vyper_to_abi_same tenv fty vs = vyper_to_abi_same tenv aty vs` by
      (irule vyper_to_abi_same_cong >> simp[]) >>
    `!n sparse. vyper_to_abi_sparse tenv fty tv n sparse =
       vyper_to_abi_sparse tenv aty tv' n sparse` by
      (irule vyper_to_abi_sparse_cong >> simp[]) >> simp[] >> NO_TAC) >>
  `EVERY (well_formed_type tenv) fts /\ EVERY (well_formed_type tenv) ats` by
    (`EVERY IS_SOME (MAP (evaluate_type tenv) fts) /\
      EVERY IS_SOME (MAP (evaluate_type tenv) ats)` by
       metis_tac[IS_SOME_OPT_MMAP, optionTheory.IS_SOME_DEF] >>
     gvs[EVERY_MAP, EVERY_MEM, well_formed_type_def, combinTheory.o_DEF]) >>
  simp[]
QED

Theorem sparse_has_type_mono:
  (!v. value_has_type atv v ==> value_has_type ftv v) /\
  default_value ftv = default_value atv ==>
  !sparse n. sparse_has_type atv n sparse ==> sparse_has_type ftv n sparse
Proof
  strip_tac >> Induct >> simp[value_has_type_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[value_has_type_def]
QED

Theorem event_arg_compatible_value_has_type:
  (!fty aty. event_arg_compatible fty aty ==>
    !tenv ftv atv. evaluate_type tenv fty = SOME ftv /\
      evaluate_type tenv aty = SOME atv ==>
      !v. value_has_type atv v ==> value_has_type ftv v) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !tenv ftvs atvs. OPT_MMAP (evaluate_type tenv) fts = SOME ftvs /\
      OPT_MMAP (evaluate_type tenv) ats = SOME atvs ==>
      !vs. values_have_types atvs vs ==> values_have_types ftvs vs)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def, evaluate_type_def,
     evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  (Cases_on `v` ORELSE Cases_on `vs`) >>
  gvs[value_has_type_def] >>
  TRY (Cases_on `a` >> gvs[value_has_type_def, all_have_type_EVERY,
         EVERY_MEM] >>
    metis_tac[sparse_has_type_mono, cj 1 event_arg_compatible_defaults] >> NO_TAC) >>
  metis_tac[]
QED

(* The sparse-array path needs both types to evaluate: an unchecked bound
   can make evaluate_type fail even though ABI types erase that bound. *)
Theorem event_arg_compatible_nested_widening:
  event_arg_compatible
    (ArrayT (BaseT (UintT 256)) (Dynamic 5))
    (ArrayT (BaseT (UintT 256)) (Dynamic 3)) /\
  event_arg_compatible
    (ArrayT (BaseT (StringT 5)) (Dynamic 2))
    (ArrayT (BaseT (StringT 3)) (Dynamic 2)) /\
  event_arg_compatible
    (TupleT [BaseT (UintT 256); BaseT (BytesT (Dynamic 5))])
    (TupleT [BaseT (UintT 256); BaseT (BytesT (Dynamic 3))]) /\
  event_arg_compatible
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 5)) (Fixed 2))
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Fixed 2))
Proof
  EVAL_TAC
QED

Theorem event_arg_compatible_nested_sparse_conversion:
  vyper_to_abi FEMPTY
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 5)) (Fixed 2)) v =
  vyper_to_abi FEMPTY
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Fixed 2)) v
Proof
  irule (cj 1 event_arg_compatible_abi_value) >>
  simp[well_formed_type_def, evaluate_type_def, event_arg_compatible_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >> CONV_TAC (wordsLib.WORD_CONV) >> simp[vyperValueTheory.type_slot_size_def]
QED
