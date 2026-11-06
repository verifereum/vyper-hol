(* Compiler and source ABI sizes agree for types that evaluate. *)
Theory abiTypeBoundProps
Ancestors
  compileEnv vyperValue vyperABI vyperTypeABI vyperTyping
  finite_map list rich_list option pair

(* Evaluation and the ABI type are stable under a larger type env: a type
   that evaluates names only structs its env has. *)
Theorem vyper_to_abi_type_submap:
  (!env ty tv.
     evaluate_type env ty = SOME tv ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_type tenv ty = SOME tv /\
            vyper_to_abi_type env ty = vyper_to_abi_type tenv ty) /\
  (!env ts acc tvs.
     evaluate_types env ts acc = SOME tvs ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_types tenv ts acc = SOME tvs /\
            vyper_to_abi_types env ts = vyper_to_abi_types tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      `FLOOKUP tenv nsid = SOME (StructArgs args)`
        by fs[SUBMAP_FLOOKUP_EQN] >>
      `env \\ nsid SUBMAP tenv \\ nsid`
        by fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> simp[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      fs[SUBMAP_FLOOKUP_EQN])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> Cases_on `bd` >> simp[])
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem evaluate_type_array_child_size:
  evaluate_type env (ArrayT t bd) = SOME v ==>
  ?u. evaluate_type env t = SOME u /\
      type_value_size u < type_value_size v
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> qexists `tv` >> simp[]
QED

Theorem evaluate_type_tuple_child_size:
  evaluate_type env (TupleT ts) = SOME v /\ MEM t ts ==>
  ?u. evaluate_type env t = SOME u /\
      type_value_size u < type_value_size v
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule evaluate_types_LIST_REL >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  gvs[MEM_EL] >>
  qspecl_then [`tvs`, `EL n tvs`] mp_tac MEM_type_value_size_TupleTV >>
  simp[MEM_EL] >> metis_tac[]
QED

Theorem evaluate_type_struct_child_size:
  FLOOKUP env k = SOME (StructArgs args) /\
  evaluate_type env (StructT k) = SOME v /\ MEM t (MAP SND args) ==>
  ?u. evaluate_type (env \\ k) t = SOME u /\
      type_value_size u < type_value_size v
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule evaluate_types_LIST_REL >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> gvs[MEM_EL] >>
  qspecl_then [`ZIP (MAP FST args,tvs)`, `EL n (MAP FST args)`,
                `EL n tvs`] mp_tac MEM_type_value_size_StructTV >>
  simp[MEM_ZIP] >> metis_tac[]
QED

Theorem evaluate_type_struct_same_fields:
  FLOOKUP env k = SOME (StructArgs a) /\
  FLOOKUP env j = SOME (StructArgs b) /\
  MAP FST a = MAP FST b /\ MAP SND a = MAP SND b /\
  evaluate_type env (StructT k) = SOME v /\
  evaluate_type env (StructT j) = SOME w ==> v = w
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `env \\ k SUBMAP env /\ env \\ j SUBMAP env`
    by simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  imp_res_tac (cj 2 vyper_to_abi_type_submap) >> gvs[]
QED

(* Proof-only forward consistency, restricted by evaluated runtime-type size. *)
Definition abi_sfields_consistent_upto_def:
  abi_sfields_consistent_upto n sf env <=>
    !k args v.
      FLOOKUP env k = SOME (StructArgs args) /\
      evaluate_type env (StructT k) = SOME v /\ type_value_size v <= n ==>
      ?fields. FLOOKUP sf (nsid_to_string k) = SOME fields /\
        MAP FST fields = MAP FST args /\
        MAP (FST o SND) fields = MAP SND args
End

Theorem abi_sfields_consistent_upto_init:
  sfields_tenv_consistent sf env ==> abi_sfields_consistent_upto n sf env
Proof
  simp[sfields_tenv_consistent_def, abi_sfields_consistent_upto_def] >>
  metis_tac[]
QED

Theorem abi_sfields_consistent_upto_mono:
  abi_sfields_consistent_upto n sf env /\ m <= n ==>
  abi_sfields_consistent_upto m sf env
Proof
  rw[abi_sfields_consistent_upto_def] >> first_x_assum irule >>
  qexists `v` >> simp[]
QED

Theorem abi_sfields_consistent_upto_lookup:
  abi_sfields_consistent_upto n sf env /\
  FLOOKUP env k = SOME (StructArgs args) /\
  evaluate_type env (StructT k) = SOME v /\ type_value_size v <= n ==>
  ?fields. FLOOKUP sf (nsid_to_string k) = SOME fields /\
    MAP FST fields = MAP FST args /\
    MAP (FST o SND) fields = MAP SND args
Proof
  metis_tac[abi_sfields_consistent_upto_def]
QED

Theorem abi_sfields_consistent_upto_domsub:
  abi_sfields_consistent_upto n sf env /\
  FLOOKUP env k = SOME (StructArgs args) /\
  evaluate_type env (StructT k) = SOME v /\ type_value_size v <= n /\
  m < type_value_size v ==>
  abi_sfields_consistent_upto m (sf \\ nsid_to_string k) (env \\ k)
Proof
  rpt strip_tac >>
  drule_all abi_sfields_consistent_upto_lookup >> strip_tac >>
  rw[abi_sfields_consistent_upto_def] >>
  rename1 `evaluate_type (env \\ k) (StructT j) = SOME w` >>
  `env \\ k SUBMAP env`
    by simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  `evaluate_type env (StructT j) = SOME w`
    by metis_tac[cj 1 vyper_to_abi_type_submap] >>
  gvs[DOMSUB_FLOOKUP_THM] >>
  `type_value_size w <= n` by simp[] >>
  drule_all abi_sfields_consistent_upto_lookup >> strip_tac >>
  Cases_on `nsid_to_string j = nsid_to_string k`
  >- (gvs[] >>
      `w = v` by metis_tac[evaluate_type_struct_same_fields] >> gvs[]) >>
  simp[DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

Theorem abi_props_vyper_list:
  (!t. MEM t ts ==>
    is_abi_dynamic sf t = vyper_is_dynamic env t /\
    abi_size_bound sf t = vyper_abi_size_bound env t /\
    (~vyper_is_dynamic env t ==>
      abi_static_size sf t = vyper_abi_size_bound env t)) ==>
  EXISTS (is_abi_dynamic sf) ts = vyper_any_dynamic env ts /\
  SUM (MAP (\t. abi_embedded_static_size sf t +
    (if is_abi_dynamic sf t then abi_size_bound sf t else 0)) ts) =
    vyper_abi_size_bound_list env ts /\
  (~vyper_any_dynamic env ts ==>
    SUM (MAP (abi_embedded_static_size sf) ts) =
      vyper_abi_size_bound_list env ts)
Proof
  Induct_on `ts` >> simp[vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
  rpt gen_tac >> strip_tac >>
  `is_abi_dynamic sf h = vyper_is_dynamic env h /\
   abi_size_bound sf h = vyper_abi_size_bound env h /\
   (~vyper_is_dynamic env h ==>
     abi_static_size sf h = vyper_abi_size_bound env h)`
    by metis_tac[] >>
  qpat_x_assum `(!t. MEM t ts ==> _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `vyper_is_dynamic env h` >>
  gvs[abi_embedded_static_size_def, vyper_abi_size_bound_def]
QED

Theorem abi_props_vyper_upto:
  !env ty v sf.
    evaluate_type env ty = SOME v /\
    abi_sfields_consistent_upto (type_value_size v) sf env ==>
    is_abi_dynamic sf ty = vyper_is_dynamic env ty /\
    abi_size_bound sf ty = vyper_abi_size_bound env ty /\
    (~vyper_is_dynamic env ty ==>
      abi_static_size sf ty = vyper_abi_size_bound env ty)
Proof
  measureInduct_on `type_value_size v` >> rpt gen_tac >> strip_tac >>
  Cases_on `ty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >>
      simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
           vyper_is_dynamic_def, vyper_abi_size_bound_def,
           contractABITheory.ceil32_def] >>
      Cases_on `b` >> simp[is_abi_dynamic_def, abi_size_bound_def,
        abi_static_size_def, vyper_is_dynamic_def, vyper_abi_size_bound_def,
        contractABITheory.ceil32_def])
  >~ [`TupleT ts`]
  >- (`!t. MEM t ts ==>
        is_abi_dynamic sf t = vyper_is_dynamic env t /\
        abi_size_bound sf t = vyper_abi_size_bound env t /\
        (~vyper_is_dynamic env t ==>
          abi_static_size sf t = vyper_abi_size_bound env t)`
        by (rpt gen_tac >> strip_tac >>
            drule_all evaluate_type_tuple_child_size >> strip_tac >>
            first_x_assum drule >> disch_then irule >>
            simp[] >> irule abi_sfields_consistent_upto_mono >>
            qexists `type_value_size v` >> simp[]) >>
      drule abi_props_vyper_list >> strip_tac >>
      simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
        abi_embedded_static_size_def, vyper_is_dynamic_def,
        vyper_abi_size_bound_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      gvs[GSYM abi_embedded_static_size_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])
  >~ [`ArrayT t bd`]
  >- (drule evaluate_type_array_child_size >> strip_tac >>
      first_x_assum drule >>
      disch_then (qspecl_then [`env`, `t`, `sf`] mp_tac) >>
      (impl_tac >- (simp[] >> irule abi_sfields_consistent_upto_mono >>
        qexists `type_value_size v` >> simp[])) >> strip_tac >>
      Cases_on `bd` >> Cases_on `vyper_is_dynamic env t` >>
      gvs[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
          vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
      simp[abi_embedded_static_size_def, arithmeticTheory.ADD_COMM])
  >~ [`StructT k`]
  >- (`?args. FLOOKUP env k = SOME (StructArgs args)`
        by gvs[Once evaluate_type_def, AllCaseEqs()] >>
      `type_value_size v <= type_value_size v` by simp[] >>
      drule_all abi_sfields_consistent_upto_lookup >> strip_tac >>
      `!t. MEM t (MAP SND args) ==>
        is_abi_dynamic (sf \\ nsid_to_string k) t =
          vyper_is_dynamic (env \\ k) t /\
        abi_size_bound (sf \\ nsid_to_string k) t =
          vyper_abi_size_bound (env \\ k) t /\
        (~vyper_is_dynamic (env \\ k) t ==>
          abi_static_size (sf \\ nsid_to_string k) t =
            vyper_abi_size_bound (env \\ k) t)`
        by (rpt gen_tac >> strip_tac >>
            drule_all evaluate_type_struct_child_size >> strip_tac >>
            first_x_assum drule >> disch_then irule >> simp[] >>
            irule abi_sfields_consistent_upto_domsub >>
            metis_tac[]) >>
      drule abi_props_vyper_list >> strip_tac >>
      simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
        vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      gvs[GSYM abi_embedded_static_size_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
       vyper_is_dynamic_def, vyper_abi_size_bound_def]
QED

(* Struct names can collide after string conversion. Evaluated type sizes
   still decrease down fields: colliding ancestor and child names would
   force equal field lists and equal evaluated types, contradicting that
   decrease. A size-bounded, one-way struct consistency invariant suffices
   when both environments drop a struct. Compiler embedded static size
   counts only the head; source embedded size also includes a dynamic tail. *)
(* Per-member embedded sizes determine the complete tuple encoding size. *)
Theorem abi_size_bound_tuple_agrees:
  !ts sf tenv.
    (!t. MEM t ts ==>
      abi_embedded_static_size sf t +
        (if is_abi_dynamic sf t then abi_size_bound sf t else 0) =
      vyper_abi_embedded_size tenv t) ==>
    abi_size_bound sf (TupleT ts) = vyper_abi_size_bound tenv (TupleT ts)
Proof
  simp[abi_size_bound_def, vyperABITheory.vyper_abi_size_bound_def] >>
  Induct >> simp[vyperABITheory.vyper_abi_size_bound_def] >> metis_tac[]
QED

Theorem abi_props_vyper_typed:
  !sf tenv ty tv.
    sfields_tenv_consistent sf tenv /\
    evaluate_type tenv ty = SOME tv ==>
    is_abi_dynamic sf ty = vyper_is_dynamic tenv ty /\
    abi_size_bound sf ty = vyper_abi_size_bound tenv ty /\
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0) =
      vyper_abi_embedded_size tenv ty
Proof
  rpt gen_tac >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size tv) sf tenv`
    by metis_tac[abi_sfields_consistent_upto_init] >>
  drule_all abi_props_vyper_upto >> strip_tac >> simp[] >>
  Cases_on `vyper_is_dynamic tenv ty` >>
  gvs[abi_embedded_static_size_def, vyper_abi_size_bound_def,
      arithmeticTheory.ADD_COMM]
QED
