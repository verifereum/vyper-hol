(* TOP-LEVEL: compose source ABI typing through heterogeneous, homogeneous
   and sparse lists, including implicit default elements of fixed arrays. *)
Theory sourceAbiTypingLists
Ancestors
  sourceAbiTypingDefs vyperABI vyperValue vyperTyping vyperTypeDefaults
  contractABI list rich_list option pair arithmetic alist

Theorem source_abi_types_map:
  !env tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys
Proof
  gen_tac >> Induct >> simp[]
QED

Theorem source_abi_list_length:
  !tys env vs avs.
    vyper_to_abi_list env tys vs = SOME avs ==> LENGTH avs = LENGTH tys
Proof
  Induct >> rpt gen_tac >> Cases_on `vs` >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >> res_tac
QED

Theorem source_abi_types_typed_nil:
  source_abi_types_typed []
Proof
  simp[source_abi_types_typed_def] >> rpt gen_tac >>
  Cases_on `vs` >> simp[value_has_type_def]
QED

Theorem source_abi_types_typed_cons:
  !tv tvs. source_abi_typed tv /\ source_abi_types_typed tvs ==>
    source_abi_types_typed (tv::tvs)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [source_abi_types_typed_def] >>
  rpt gen_tac >> Cases_on `tys` >> Cases_on `vs` >>
  simp[value_has_type_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >>
  rename1 `evaluate_type env head_ty = SOME tv` >>
  rename1 `vyper_to_abi env head_ty head_v = SOME head_av` >>
  rename1 `vyper_to_abi_list env tail_tys tail_vs = SOME tail_avs` >>
  `has_type (vyper_to_abi_type env head_ty) head_av` by
    (qpat_x_assum `source_abi_typed tv` (mp_tac o REWRITE_RULE [source_abi_typed_def]) >>
     disch_then (qspecl_then [`env`, `head_ty`, `head_v`, `head_av`] mp_tac) >> simp[]) >>
  `has_types (MAP (vyper_to_abi_type env) tail_tys) tail_avs` by
    (qpat_x_assum `source_abi_types_typed tvs` (mp_tac o REWRITE_RULE [source_abi_types_typed_def]) >>
     disch_then (qspecl_then [`env`, `tail_tys`, `tail_vs`, `tail_avs`] mp_tac) >> simp[]) >> gvs[]
QED

Theorem source_abi_typed_same:
  !vs env ty tv avs.
    source_abi_typed tv /\ evaluate_type env ty = SOME tv /\
    abi_type_format (vyper_to_abi_type env ty) /\ all_have_type tv vs /\
    vyper_to_abi_same env ty vs = SOME avs ==>
    have_type (vyper_to_abi_type env ty) avs /\ LENGTH avs = LENGTH vs
Proof
  Induct_on `vs` >> simp[value_has_type_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  rename1 `vyper_to_abi env ty h = SOME head_av` >>
  `has_type (vyper_to_abi_type env ty) head_av` by
    (qpat_x_assum `source_abi_typed tv` (mp_tac o REWRITE_RULE [source_abi_typed_def]) >>
     disch_then (qspecl_then [`env`, `ty`, `h`, `head_av`] mp_tac) >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem source_abi_typed_default:
  !env ty tv.
    source_abi_typed tv /\ evaluate_type env ty = SOME tv /\
    abi_type_format (vyper_to_abi_type env ty) ==>
    has_type (vyper_to_abi_type env ty) (default_to_abi tv)
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyper_to_abi_default_value) >> DISCH_TAC >>
  drule (CONJUNCT1 vyperTypeDefaultsTheory.default_value_has_type) >> DISCH_TAC >>
  qpat_x_assum `source_abi_typed tv` (mp_tac o REWRITE_RULE [source_abi_typed_def]) >>
  disch_then (qspecl_then [`env`, `ty`, `default_value tv`, `default_to_abi tv`] mp_tac) >> simp[]
QED

Theorem source_abi_have_type_every:
  !ty avs. have_type ty avs <=> EVERY (has_type ty) avs
Proof
  gen_tac >> Induct >> simp[has_type_def]
QED

Theorem source_abi_typed_sparse:
  !n env ty tv sparse avs.
    source_abi_typed tv /\ evaluate_type env ty = SOME tv /\
    abi_type_format (vyper_to_abi_type env ty) /\
    (!k v. MEM (k,v) sparse ==> value_has_type tv v) /\
    vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
    EVERY (has_type (vyper_to_abi_type env ty)) avs /\ LENGTH avs = n
Proof
  Induct_on `n` >- simp[Once vyper_to_abi_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `vyper_to_abi_sparse _ _ _ (SUC _) _ = SOME _` mp_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule_all >> strip_tac >>
  FIRST [drule_all source_abi_typed_default >> simp[] >> NO_TAC,
    rename1 `ALOOKUP sparse n = SOME sv` >>
    `value_has_type tv sv` by (drule ALOOKUP_MEM >> metis_tac[]) >>
    qpat_x_assum `source_abi_typed tv` (mp_tac o REWRITE_RULE [source_abi_typed_def]) >>
    disch_then (qspecl_then [`env`, `ty`, `sv`] mp_tac) >> simp[] >>
    rpt strip_tac >> simp[]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source ABI list typing: " ^ name)
  end) (DB.thms "sourceAbiTypingLists")
