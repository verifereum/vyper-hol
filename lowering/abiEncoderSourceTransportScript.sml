(* Indexed source conversion and memory boundaries for uniform representatives. *)
Theory abiEncoderSourceTransport
Ancestors
  valueEncoding valueEncodingProofs vyperABI vyperABIRoundtrip vyperValue vyperTyping
  vyperTypeValues vyperTypeDefaults vyperValueOperation vyperMisc list rich_list arithmetic

Theorem abi_encoder_same_conversion:
  !vs avs. vyper_to_abi_same env t vs = SOME avs ==>
    LENGTH avs = LENGTH vs /\
    !i. i < LENGTH vs ==>
      vyper_to_abi env t (EL i vs) = SOME (EL i avs)
Proof
  simp[vyper_to_abi_same_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  rpt strip_tac >> gvs[EVERY_MAP, EVERY_EL, EL_MAP] >>
  first_x_assum drule >> Cases_on `vyper_to_abi env t (EL i vs)` >> simp[]
QED

Theorem abi_encoder_elems_memory:
  !vs sb. elems_in_memory vs sb tv mem ==>
    !i. i < LENGTH vs ==>
      val_in_memory tv (EL i vs) (sb+i*type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac >>
  Cases_on `i` >> gvs[ADD_CLAUSES, MULT_CLAUSES] >>
  rename1 `k < LENGTH vs` >> first_x_assum drule >>
  disch_then (qspec_then `k` mp_tac) >>
  asm_rewrite_tac[ADD_ASSOC]
QED

Theorem abi_encoder_dense_source:
  elems_in_memory vs sb tv mem /\ vyper_to_abi_same env t vs = SOME avs /\
  EVERY (value_has_type tv) vs ==>
  LENGTH avs = LENGTH vs /\
  !i. i < LENGTH vs ==>
    value_has_type tv (EL i vs) /\
    val_in_memory tv (EL i vs) (sb+i*type_memory_size tv) mem /\
    vyper_to_abi env t (EL i vs) = SOME (EL i avs)
Proof
  strip_tac >> drule abi_encoder_same_conversion >> strip_tac >>
  drule abi_encoder_elems_memory >> strip_tac >>
  gvs[EVERY_EL]
QED

Theorem abi_encoder_list_conversion:
  !ts vs avs. vyper_to_abi_list env ts vs = SOME avs ==>
    LENGTH avs = LENGTH ts /\ LENGTH vs = LENGTH ts /\
    !i. i < LENGTH ts ==>
      vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs)
Proof
  rpt strip_tac >> drule vyper_to_abi_list_EL >> simp[]
QED

Theorem abi_encoder_tuple_memory:
  !vs tvs sb. LENGTH vs = LENGTH tvs /\ tuple_in_memory vs tvs sb mem ==>
    !i. i < LENGTH tvs ==>
      val_in_memory (EL i tvs) (EL i vs)
        (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem
Proof
  Induct >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  rpt strip_tac >> Cases_on `i` >> gvs[] >>
  rename1 `k < LENGTH rest_tvs` >>
  rename1 `val_in_memory head_tv head_v sb mem` >>
  first_x_assum (qspecl_then [`rest_tvs`, `sb + type_memory_size head_tv`] mp_tac) >>
  asm_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_tuple_source:
  LENGTH ts = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  (!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs)) /\
  tuple_in_memory vs tvs sb mem /\ vyper_to_abi_list env ts vs = SOME avs ==>
  LENGTH avs = LENGTH ts /\
  !i. i < LENGTH ts ==>
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem /\
    vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs)
Proof
  strip_tac >> drule abi_encoder_list_conversion >> strip_tac >>
  simp[] >> rpt strip_tac >> irule abi_encoder_tuple_memory >> simp[]
QED

Theorem abi_encoder_sparse_conversion:
  !n avs. evaluate_type env t = SOME tv /\
    vyper_to_abi_sparse env t tv n kvs = SOME avs ==>
    LENGTH avs = n /\
    !i. i < n ==>
      vyper_to_abi env t (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))) = SOME (EL i avs)
Proof
  Induct >> simp[Once vyper_to_abi_def, array_elements_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `_ ++ [_] = avs` (SUBST_ALL_TAC o SYM) >> fs[] >>
  drule (cj 1 vyper_to_abi_default_value) >> disch_tac >>
  rpt strip_tac >> Cases_on `i = n` >> gvs[EL_APPEND_EQN] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[array_elements_def, EL_APPEND_EQN]
QED

Theorem abi_encoder_sparse_source:
  evaluate_type env t = SOME tv /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) sb mem /\
  vyper_to_abi_sparse env t tv n kvs = SOME avs ==>
  LENGTH avs = n /\
  !i. i < n ==>
    value_has_type tv
      (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))) /\
    val_in_memory tv
      (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (sb+i*type_memory_size tv) mem /\
    vyper_to_abi env t
      (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))) = SOME (EL i avs)
Proof
  strip_tac >> drule_all abi_encoder_sparse_conversion >> strip_tac >>
  drule evaluate_type_well_formed_type_value >>
  disch_then (assume_tac o MATCH_MP default_value_well_typed) >>
  simp[] >> rpt strip_tac
  >- (gvs[array_elements_def] >> Cases_on `ALOOKUP kvs i` >> gvs[] >>
      gvs[value_has_type_def] >>
      drule_all sparse_has_type_lookup >> simp[]) >>
  gvs[val_in_memory_def, array_elements_def] >>
  Cases_on `ALOOKUP kvs i` >> gvs[] >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem abi_encoder_dynamic_source:
  evaluate_type env (ArrayT t (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) sb mem /\
  vyper_to_abi env (ArrayT t (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME av ==>
  ?avs. evaluate_type env t = SOME tv /\ av = ListV avs /\
  LENGTH avs = LENGTH vs /\
  mem_word_at sb mem = n2w (LENGTH vs) /\
  32 + LENGTH vs * type_memory_size tv <= type_memory_size (ArrayTV tv (Dynamic cap)) /\
  !i. i < LENGTH vs ==>
    value_has_type tv (EL i vs) /\
    val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem /\
    vyper_to_abi env t (EL i vs) = SOME (EL i avs)
Proof
  simp[Once evaluate_type_def, value_has_type_def, all_have_type_EVERY,
       val_in_memory_def, Once vyper_to_abi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all abi_encoder_dense_source >> strip_tac >>
  simp[type_memory_size_def] >> rpt strip_tac >>
  first_x_assum drule >> simp_tac bool_ss [AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_tuple_parent:
  evaluate_type env (TupleT ts) = SOME tv /\
  value_has_type tv (ArrayV (TupleV vs)) /\
  val_in_memory tv (ArrayV (TupleV vs)) sb mem /\
  vyper_to_abi env (TupleT ts) (ArrayV (TupleV vs)) = SOME av ==>
  ?tvs avs. tv = TupleTV tvs /\ av = ListV avs /\
    LENGTH tvs = LENGTH ts /\ LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts /\
    !i. i < LENGTH ts ==>
      evaluate_type env (EL i ts) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem /\
      vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs)
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[value_has_type_def, val_in_memory_def, Once vyper_to_abi_def, AllCaseEqs()] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `!i. i < LENGTH tvs ==> val_in_memory (EL i tvs) (EL i vs)
    (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (rpt strip_tac >> irule abi_encoder_tuple_memory >> simp[]) >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, EL_MAP] >>
  rpt strip_tac >>
  qpat_x_assum `!n. _ ==> IS_SOME _` (qspec_then `i` mp_tac) >>
  Cases_on `evaluate_type env (EL i ts)` >> simp[]
QED

Theorem abi_encoder_struct_parent:
  evaluate_type env (StructT nsid) = SOME tv /\
  value_has_type tv (StructV fields) /\
  val_in_memory tv (StructV fields) sb mem /\
  vyper_to_abi env (StructT nsid) (StructV fields) = SOME av ==>
  ?args tvs avs. FLOOKUP env nsid = SOME (StructArgs args) /\
    tv = StructTV (ZIP (MAP FST args,tvs)) /\ av = ListV avs /\
    LENGTH tvs = LENGTH args /\ LENGTH fields = LENGTH args /\ LENGTH avs = LENGTH args /\
    !i. i < LENGTH args ==>
      evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i (MAP SND fields)) /\
      val_in_memory (EL i tvs) (EL i (MAP SND fields))
        (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem /\
      vyper_to_abi (env \\ nsid) (EL i (MAP SND args)) (EL i (MAP SND fields)) =
        SOME (EL i avs)
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[value_has_type_def, val_in_memory_def, Once vyper_to_abi_def, AllCaseEqs()] >>
  drule evaluate_types_length >> simp[] >> strip_tac >>
  drule struct_has_type_values_have_types >>
  simp[MAP_ZIP, values_have_types_LIST_REL, LIST_REL_EL_EQN] >> strip_tac >>
  gvs[fields_in_memory_tuple, MAP_ZIP] >> qexists_tac `tvs` >> simp[] >>
  drule vyper_to_abi_list_EL >> simp[] >> strip_tac >>
  `!i. i < LENGTH tvs ==> val_in_memory (EL i tvs) (EL i (MAP SND fields))
    (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (rpt strip_tac >> irule abi_encoder_tuple_memory >> simp[]) >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, EL_MAP] >>
  rpt strip_tac >>
  qpat_x_assum `!n. _ ==> IS_SOME _` (qspec_then `i` mp_tac) >>
  Cases_on `evaluate_type (env \\ nsid) (SND (EL i args))` >> simp[]
QED

Theorem abi_encoder_sparse_zero_probe:
  array_elements (ArrayTV tv (Fixed 0)) (SArrayV []) = [] /\
  vyper_to_abi_sparse env t tv 0 [] = SOME []
Proof
  EVAL_TAC
QED

Theorem abi_encoder_sparse_absent_probe:
  array_elements (ArrayTV tv (Fixed 1)) (SArrayV []) = [default_value tv] /\
  (evaluate_type env t = SOME tv ==>
    vyper_to_abi env t (default_value tv) = SOME (default_to_abi tv))
Proof
  simp[array_elements_def, GENLIST, cj 1 vyper_to_abi_default_value]
QED

(* Retained tags do not reconstruct axiom provenance erased by .dat loading. *)
val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_TRANSPORT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source transport admission dependency: " ^ name)
  end)
  [("dense", abi_encoder_dense_source),
   ("tuple", abi_encoder_tuple_source),
   ("sparse", abi_encoder_sparse_source),
   ("dynamic_parent", abi_encoder_dynamic_source),
   ("tuple_parent", abi_encoder_tuple_parent),
   ("struct_parent", abi_encoder_struct_parent),
   ("zero_probe", abi_encoder_sparse_zero_probe),
   ("absent_probe", abi_encoder_sparse_absent_probe)];
