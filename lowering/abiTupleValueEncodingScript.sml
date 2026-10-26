(* TOP-LEVEL: abi_word_tuple_memory.
   Exact ABI layout of arbitrarily long tuples of typed scalar values.
   The recursive encoder's dynamic cases require separate execution proofs. *)
Theory abiTupleValueEncoding
Ancestors
  abiValueEncoding valueEncoding valueEncodingProps compileEnv
  vyperABI vyperABIRoundtrip vyperValue vyperTyping vyperTypeABI exprLowering contractABI
  list rich_list option

Theorem abi_word_metadata:
  is_word_type ty ⇒
  type_memory_bytes cenv ty = 32 ∧
  type_to_abi_enc_info sfields cenv ty = AbiCopy 32 ∧
  ¬is_abi_dynamic fields ty ∧ ¬is_dynamic (vyper_to_abi_type tenv ty)
Proof
  Cases_on `ty` >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
       TRY (rename1 `BytesT bd` >> Cases_on `bd`)) >>
  simp[is_word_type_def, type_memory_bytes_def, type_to_abi_enc_info_def,
       is_abi_dynamic_def]
QED

Theorem abi_word_types_metadata:
  ∀tys. EVERY is_word_type tys ⇒
  SUM (MAP (type_memory_bytes cenv) tys) = 32 * LENGTH tys ∧
  ¬EXISTS (is_abi_dynamic fields) tys ∧
  ¬any_dynamic (vyper_to_abi_types tenv tys)
Proof
  Induct >> simp[vyper_to_abi_type_def, any_dynamic_EXISTS] >>
  rpt strip_tac >> imp_res_tac abi_word_metadata >> fs[any_dynamic_EXISTS]
QED

Theorem abi_word_tuple_metadata:
  EVERY is_word_type tys ⇒
  type_to_abi_enc_info sfields cenv (TupleT tys) = AbiCopy (32 * LENGTH tys)
Proof
  strip_tac >>
  `SUM (MAP (type_memory_bytes cenv) tys) = 32 * LENGTH tys ∧
   ¬EXISTS (is_abi_dynamic cenv.ce_struct_fields) tys` by
    metis_tac[abi_word_types_metadata] >>
  fs[type_to_abi_enc_info_def, type_memory_bytes_def, is_abi_dynamic_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_word_tuple_memory:
  ∀tys tvs vs avs off mem.
  EVERY is_word_type tys ∧
  OPT_MMAP (evaluate_type tenv) tys = SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  vyper_to_abi_list tenv tys vs = SOME avs ∧
  tuple_in_memory vs tvs off mem ∧
  off + 32 * LENGTH tys ≤ LENGTH mem ⇒
  mem_bytes_at off (32 * LENGTH tys) mem =
    FLAT (MAP2 (λty av. enc (vyper_to_abi_type tenv ty) av) tys avs)
Proof
  Induct
  >- (Cases_on `vs` >>
      simp[vyper_to_abi_def, OPT_MMAP_def, mem_bytes_at_def]) >>
  Cases_on `vs` >>
  simp[vyper_to_abi_def, OPT_MMAP_def, EVERY_DEF, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `evaluate_type tenv head_ty = SOME tv` >>
  `type_memory_size tv = 32` by
    (irule abi_word_type_size >> metis_tac[]) >>
  gvs[Once val_in_memory_def] >>
  rename1 `tuple_in_memory tail_vs tail_tvs (off + 32) mem` >>
  `off + 32 ≤ LENGTH mem` by decide_tac >>
  drule_all abi_word_memory >> strip_tac >>
  `mem_bytes_at off (32 * SUC (LENGTH tys)) mem =
     mem_bytes_at off 32 mem ++ mem_bytes_at (off + 32) (32 * LENGTH tys) mem` by
    (`32 * SUC (LENGTH tys) = 32 + 32 * LENGTH tys` by simp[] >>
     pop_assum SUBST1_TAC >> irule mem_bytes_at_split >> decide_tac) >>
  pop_assum SUBST1_TAC >> simp[] >>
  first_x_assum irule >> simp[] >> qexists_tac `tail_vs` >> simp[]
QED

Theorem abi_values_have_types:
  ∀tvs vs. values_have_types tvs vs ⇔ LIST_REL value_has_type tvs vs
Proof
  Induct >> Cases_on `vs` >> simp[Once value_has_type_def]
QED

Theorem abi_static_tuple_accumulator:
  ∀tys avs hl tl heads tails.
  ¬any_dynamic tys ∧ LENGTH tys = LENGTH avs ⇒
  enc_tuple hl tl tys avs heads tails =
    FLAT (REVERSE heads) ++ FLAT (MAP2 enc tys avs) ++ FLAT (REVERSE tails)
Proof
  Induct >> Cases_on `avs` >>
  simp[Once enc_def, any_dynamic_EXISTS, REV_REVERSE_LEM] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[enc_def, REV_REVERSE_LEM, APPEND_ASSOC]
QED

Theorem abi_static_tuple_bytes:
  ∀tys avs.
  ¬any_dynamic tys ∧ LENGTH tys = LENGTH avs ⇒
  enc (Tuple tys) (ListV avs) = FLAT (MAP2 enc tys avs)
Proof
  rpt strip_tac >> simp[Once enc_def] >>
  drule_all abi_static_tuple_accumulator >> simp[]
QED

(* Typed source values supply successful conversion; callers need not assume
   that an attempted ABI preparation or target execution has succeeded. *)
Theorem abi_typed_word_tuple_memory:
  EVERY is_word_type tys ∧ evaluate_types tenv tys [] = SOME tvs ∧
  values_have_types tvs vs ∧ tuple_in_memory vs tvs off mem ∧
  off + 32 * LENGTH tys ≤ LENGTH mem ⇒
  ∃avs. vyper_to_abi_list tenv tys vs = SOME avs ∧
    mem_bytes_at off (32 * LENGTH tys) mem =
      FLAT (MAP2 (λty av. enc (vyper_to_abi_type tenv ty) av) tys avs)
Proof
  rpt strip_tac >>
  `OPT_MMAP (evaluate_type tenv) tys = SOME tvs` by
    fs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (λty tv. evaluate_type tenv ty = SOME tv) tys tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[]) >>
  `∃avs. vyper_to_abi_list tenv tys vs = SOME avs` by
    metis_tac[cj 2 vyper_to_abi_total] >>
  qexists_tac `avs` >> simp[] >>
  `LIST_REL value_has_type tvs vs` by fs[abi_values_have_types] >>
  drule_all abi_word_tuple_memory >> simp[]
QED

Theorem abi_types_length[simp]:
  ∀tys. LENGTH (vyper_to_abi_types tenv tys) = LENGTH tys
Proof
  Induct >> simp[vyper_to_abi_type_def]
QED

Theorem abi_tuple_map:
  ∀tys avs. LENGTH tys = LENGTH avs ⇒
  MAP2 enc (vyper_to_abi_types tenv tys) avs =
    MAP2 (λty av. enc (vyper_to_abi_type tenv ty) av) tys avs
Proof
  Induct >> Cases_on `avs` >> simp[vyper_to_abi_type_def]
QED

Theorem abi_typed_word_tuple_encoding:
  EVERY is_word_type tys ∧ evaluate_types tenv tys [] = SOME tvs ∧
  values_have_types tvs vs ∧ tuple_in_memory vs tvs off mem ∧
  off + 32 * LENGTH tys ≤ LENGTH mem ⇒
  ∃avs. vyper_to_abi_list tenv tys vs = SOME avs ∧
    mem_bytes_at off (32 * LENGTH tys) mem =
      enc (vyper_to_abi_type tenv (TupleT tys)) (ListV avs) ∧
    LENGTH (enc (vyper_to_abi_type tenv (TupleT tys)) (ListV avs)) =
      32 * LENGTH tys
Proof
  strip_tac >> drule_all abi_typed_word_tuple_memory >> strip_tac >>
  `LENGTH tys = LENGTH avs` by metis_tac[vyper_to_abi_list_EL] >>
  `¬any_dynamic (vyper_to_abi_types tenv tys)` by
    metis_tac[abi_word_types_metadata] >>
  `enc (Tuple (vyper_to_abi_types tenv tys)) (ListV avs) =
     FLAT (MAP2 (λty av. enc (vyper_to_abi_type tenv ty) av) tys avs)` by
    (qspecl_then [`vyper_to_abi_types tenv tys`, `avs`] mp_tac
       abi_static_tuple_bytes >>
     simp[abi_tuple_map]) >>
  qexists_tac `avs` >>
  pure_rewrite_tac[vyper_to_abi_type_def] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `mem_bytes_at off (32 * LENGTH tys) mem = _`
    (mp_tac o AP_TERM ``LENGTH : byte list -> num``) >> simp[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "abiTupleValueEncoding");
