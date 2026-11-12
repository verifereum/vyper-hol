(* Source array views for recursive decoder clients, without ABI typing. *)
Theory sourceArrayInputs
Ancestors
  abiDecoderCoherence entryDecodeStaticProps vyperABIRoundtrip
  vyperTyping vyperABI vyperValue list rich_list

Theorem source_dynamic_array_values:
  value_has_type (ArrayTV tv (Dynamic n)) v /\
  vyper_to_abi env (ArrayT ty (Dynamic n)) v = SOME av ==>
  ?xs avs. v = ArrayV (DynArrayV xs) /\ av = ListV avs /\
    LENGTH xs <= n /\ EVERY (value_has_type tv) xs /\
    vyper_to_abi_same env ty xs = SOME avs
Proof
  strip_tac >>
  `?xs. v = ArrayV (DynArrayV xs) /\ LENGTH xs <= n /\ all_have_type tv xs` by
    (qpat_assum `value_has_type _ v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `v` >> simp[value_has_type_def] >>
     rename1 `ArrayV a` >> Cases_on `a` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  gvs[vyper_to_abi_def, AllCaseEqs(), all_have_type_EVERY] >> metis_tac[]
QED

Theorem source_list_conversion_intro:
  !tys vs avs.
    LENGTH tys = LENGTH vs /\ LENGTH avs = LENGTH vs /\
    (!i. i < LENGTH vs ==>
      vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs)) ==>
    vyper_to_abi_list env tys vs = SOME avs
Proof
  Induct >> Cases_on `vs` >> Cases_on `avs` >>
  simp[vyper_to_abi_def] >> rpt strip_tac >>
  rename1 `vyper_to_abi env th vh` >>
  rename1 `SOME (ah::avs_tail)` >>
  `vyper_to_abi env th vh = SOME ah` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `vyper_to_abi_list env tys t = SOME avs_tail` suffices_by
    simp[vyper_to_abi_def] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem source_fixed_array_values:
  evaluate_type env ty = SOME tv /\
  value_has_type (ArrayTV tv (Fixed n)) v /\
  vyper_to_abi env (ArrayT ty (Fixed n)) v = SOME av ==>
  ?sp vs avs. v = ArrayV (SArrayV sp) /\ av = ListV avs /\
    LENGTH vs = n /\ LIST_REL value_has_type (REPLICATE n tv) vs /\
    vyper_to_abi_list env (REPLICATE n ty) vs = SOME avs /\
    (!i. i < n ==> EL i vs = sparse_val tv sp i)
Proof
  strip_tac >>
  `?sp. v = ArrayV (SArrayV sp)` by
    (qpat_assum `value_has_type _ v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `v` >> simp[value_has_type_def] >>
     rename1 `ArrayV a` >> Cases_on `a` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `?avs. av = ListV avs /\ vyper_to_abi_sparse env ty tv n sp = SOME avs` by
    (qpat_x_assum `vyper_to_abi env _ _ = _` mp_tac >>
     simp[vyper_to_abi_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  drule_all vyper_to_abi_sparse_EL >> strip_tac >>
  qexistsl_tac [`sp`,`GENLIST (sparse_val tv sp) n`,`avs`] >>
  simp[LIST_REL_EL_EQN, EL_REPLICATE, EL_GENLIST] >>
  conj_tac
  >- (rpt strip_tac >> irule sparse_val_has_type >>
      conj_tac
      >- (qexistsl_tac [`env`,`ty`] >> simp[]) >>
      qexists_tac `n` >> fs[value_has_type_def]) >>
  irule source_list_conversion_intro >> simp[EL_REPLICATE, EL_GENLIST]
QED
