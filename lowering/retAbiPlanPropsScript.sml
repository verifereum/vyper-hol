(*
 * External Return ABI Plan Properties
 *
 * The encoding plan and buffer size update_cenv_ret_abi puts in the compile
 * env are right for the source's ABI encoding of the return value: the plan
 * meets abi_enc_plan and the size is vyper_abi_size_bound, of the return
 * type wrapped in a singleton tuple when the ABI wraps it and it is dynamic.
 * The compiler reads struct fields from make_struct_fields_map, which agrees
 * with type_env (structFieldsProps), so its ABI sizes and flags agree with
 * the source's: is_abi_dynamic, abi_static_size and abi_size_bound with
 * vyper_is_dynamic and vyper_abi_size_bound (as in Python's abi_types.py,
 * ABIType.is_dynamic/static_size/size_bound).
 *
 * TOP-LEVEL:
 *   update_cenv_ret_abi_plan -- the plan and size of a return type
 *   build_compile_env_ret_abi_plan -- the same at package_external_fn's env
 * Helpers:
 *   vyper_to_abi_type_submap -- evaluation and ABI type in a larger env
 *   sfields_tenv_consistent_domsub -- struct map and env drop a struct
 *   abi_props_vyper -- compile-side ABI sizes and flags are the source's
 *   abi_elem_props -- the same for a type in a smaller env than the map's
 *   abi_enc_plan_static_copy, abi_enc_plans_map, abi_enc_plans_replicate
 *     -- plans for static types, mapped and replicated element lists
 *   type_to_abi_enc_info_plan -- type_to_abi_enc_info builds a plan
 *   external_return_needs_wrap_eq -- the compiler's wrap is the ABI's
 *)

Theory retAbiPlanProps
Ancestors
  compileVyper compileEnv exprLowering abiEncoderProps structFieldsProps
  typedCopyProducer
  vyperTypeSystem vyperContext vyperValue vyperABI contractABI
  valueEncoding finite_map list rich_list option pair combin

(* ===== Source side ===== *)

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

(* vyperTypeABI has these two as local lemmas. *)
Theorem vyper_to_abi_type_dynamic[local]:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv ==>
     is_dynamic (vyper_to_abi_type tenv ty) = vyper_is_dynamic tenv ty) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> TRY (Cases_on `bd`) >> gvs[vyper_is_dynamic_def]
QED

Theorem vyper_to_abi_static_length[local]:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv /\ ~vyper_is_dynamic tenv ty ==>
     static_length (vyper_to_abi_type tenv ty) = vyper_abi_size_bound tenv ty) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs /\ ~vyper_any_dynamic tenv ts ==>
     static_length (Tuple (vyper_to_abi_types tenv ts)) =
     vyper_abi_size_bound_list tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, vyper_abi_size_bound_def,
       AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> TRY (Cases_on `bd`) >>
  gvs[vyper_is_dynamic_def, vyper_abi_size_bound_def, static_length_Tuple_SUM]
QED

(* ===== Compile side against the source ===== *)

(* The struct map stays consistent with the type env when both drop the same
   struct, as long as every struct key of the env is a main-module one (so
   nsid_to_string tells the env's structs apart). *)
Theorem sfields_tenv_consistent_domsub:
  sfields_tenv_consistent sf tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  FLOOKUP tenv nsid = SOME (StructArgs args) ==>
  sfields_tenv_consistent (sf \\ nsid_to_string nsid) (tenv \\ nsid) /\
  (!k a. FLOOKUP (tenv \\ nsid) k = SOME (StructArgs a) ==> FST k = NONE)
Proof
  strip_tac >>
  `!k a. FLOOKUP tenv k = SOME (StructArgs a) /\ k <> nsid ==>
         nsid_to_string k <> nsid_to_string nsid`
    by (rpt strip_tac >> res_tac >>
        Cases_on `k` >> Cases_on `nsid` >> gvs[nsid_to_string_def]) >>
  fs[sfields_tenv_consistent_def, DOMSUB_FLOOKUP_THM] >> rpt strip_tac
  >~ [`nsid_to_string _ <> name`]
  >- (res_tac >> qexistsl [`nsid'`, `args'`] >> simp[] >>
      strip_tac >> gvs[])
QED

(* Instantiate the induction hypothesis at the struct map sf. *)
val ih_at_sf =
  first_x_assum (qspec_then
    `sf : (string, (string # type # num) list) fmap` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac;

val abi_size_defs =
  [is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
   vyper_is_dynamic_def, vyper_abi_size_bound_def,
   abi_embedded_static_size_def];

Theorem abi_props_vyper:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv ==>
     !(sf : (string, (string # type # num) list) fmap).
          sfields_tenv_consistent sf tenv /\
          (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) ==>
          is_abi_dynamic sf ty = vyper_is_dynamic tenv ty /\
          abi_size_bound sf ty = vyper_abi_size_bound tenv ty /\
          (~vyper_is_dynamic tenv ty ==>
           abi_static_size sf ty = vyper_abi_size_bound tenv ty)) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     !(sf : (string, (string # type # num) list) fmap).
          sfields_tenv_consistent sf tenv /\
          (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) ==>
          EXISTS (is_abi_dynamic sf) ts = vyper_any_dynamic tenv ts /\
          SUM (MAP (\t. (if is_abi_dynamic sf t then 32
                         else abi_static_size sf t) +
                        (if is_abi_dynamic sf t then abi_size_bound sf t
                         else 0)) ts) =
            vyper_abi_size_bound_list tenv ts /\
          (~vyper_any_dynamic tenv ts ==>
           SUM (MAP (\t. if is_abi_dynamic sf t then 32
                         else abi_static_size sf t) ts) =
             vyper_abi_size_bound_list tenv ts))
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      drule_all sfields_tenv_consistent_domsub >> strip_tac >>
      `?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
                MAP (FST o SND) fields = MAP SND args`
        by (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
            simp[sfields_tenv_consistent_def] >> strip_tac >>
            first_x_assum drule >> strip_tac >> simp[]) >>
      first_x_assum (qspec_then `fdomsub sf (nsid_to_string nsid)` mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      simp abi_size_defs >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      gvs[vyper_is_dynamic_def, vyper_abi_size_bound_def])
  >~ [`ArrayT t bd`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      ih_at_sf >>
      Cases_on `bd` >>
      simp abi_size_defs >>
      Cases_on `vyper_is_dynamic tenv t` >> gvs[])
  >~ [`TupleT ts`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      ih_at_sf >>
      simp abi_size_defs >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      gvs[vyper_is_dynamic_def, vyper_abi_size_bound_def])
  >~ [`BaseT bt`]
  >- (rpt strip_tac >>
      Cases_on `bt` >> TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
      gvs[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
          vyper_is_dynamic_def, vyper_abi_size_bound_def,
          contractABITheory.ceil32_def])
  >~ [`evaluate_types tenv (t::ts) acc`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      ih_at_sf >> ih_at_sf >>
      simp[vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
      Cases_on `vyper_is_dynamic tenv t` >> gvs[]) >>
  rpt strip_tac >>
  simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
       vyper_is_dynamic_def, vyper_abi_size_bound_def]
QED

(* ===== Encoding plans ===== *)

(* What a plan element needs of a component type evaluating in a smaller
   env than the compiler's struct map stands for. *)
Theorem abi_elem_props:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type tenv t = SOME tv ==>
  is_abi_dynamic cenv.ce_struct_fields t =
    is_dynamic (vyper_to_abi_type tenv t) /\
  abi_embedded_static_size cenv.ce_struct_fields t =
    (if is_dynamic (vyper_to_abi_type tenv t) then 32
     else static_length (vyper_to_abi_type tenv t)) /\
  abi_size_bound cenv.ce_struct_fields t = vyper_abi_size_bound tenv0 t /\
  type_memory_bytes cenv t = type_memory_size tv
Proof
  strip_tac >>
  drule (cj 1 vyper_to_abi_type_submap) >> disch_then drule >> strip_tac >>
  drule (cj 1 abi_props_vyper) >>
  disch_then (qspec_then `cenv.ce_struct_fields` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[abi_embedded_static_size_def] >>
  Cases_on `vyper_is_dynamic tenv0 t` >> simp[] >>
  drule_all (cj 1 vyper_to_abi_static_length) >> simp[]
QED

Theorem abi_enc_plans_map:
  !ts.
    tenv SUBMAP tenv0 /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
    (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv0 t = SOME tv ==>
            type_memory_bytes cenv t = type_memory_size tv) /\
    (!t. MEM t ts ==>
         IS_SOME (evaluate_type tenv t) /\ abi_enc_plan tenv t (f t)) ==>
    abi_enc_plans tenv ts
      (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t,
                 is_abi_dynamic cenv.ce_struct_fields t)) ts)
Proof
  Induct >> simp[abi_enc_plan_nil] >> rpt strip_tac >>
  `?tv. evaluate_type tenv h = SOME tv`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[IS_SOME_EXISTS]) >>
  drule_all abi_elem_props >> strip_tac >> simp[] >>
  irule abi_enc_plan_cons >> simp[]
QED

(* A static type is encoded by copying its memory. *)
Theorem abi_enc_plan_static_copy:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type tenv ty = SOME tv /\
  ~is_abi_dynamic cenv.ce_struct_fields ty ==>
  abi_enc_plan tenv ty (AbiCopy (type_memory_bytes cenv ty))
Proof
  strip_tac >> drule_all abi_elem_props >> strip_tac >> gvs[] >>
  irule abi_enc_plan_copy >> fs[]
QED

Theorem map_struct_field_types[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >> simp[FORALL_PROD]
QED

Theorem abi_enc_plans_replicate:
  evaluate_type env t = SOME tv /\ abi_enc_plan env t ei ==>
  !n. abi_enc_plans env (REPLICATE n t)
        (REPLICATE n
           (ei, (if is_dynamic (vyper_to_abi_type env t) then 32
                 else static_length (vyper_to_abi_type env t)),
            type_memory_size tv, is_dynamic (vyper_to_abi_type env t)))
Proof
  strip_tac >> Induct >> simp[abi_enc_plan_nil] >>
  irule abi_enc_plan_cons >> simp[]
QED

(* The StructT case of type_to_abi_enc_info_plan, given the plan for each
   field (the induction hypothesis). *)
Theorem type_to_abi_enc_info_plan_struct[local]:
  FLOOKUP tenv nsid = SOME (StructArgs args) /\
  assignable_type tenv (StructT nsid) /\
  (!ty args x ty'.
     FLOOKUP tenv nsid = SOME ty /\ ty = StructArgs args /\ MEM x args /\
     ty' = SND x ==>
     assignable_type (tenv \\ nsid) ty' ==>
     !(sf' : (string, (string # type # 'a) list) fmap) cenv tenv1.
       tenv \\ nsid SUBMAP tenv1 /\
       sfields_tenv_consistent sf' (tenv \\ nsid) /\
       (!k a. FLOOKUP (tenv \\ nsid) k = SOME (StructArgs a) ==>
              FST k = NONE) /\
       sfields_tenv_consistent cenv.ce_struct_fields tenv1 /\
       (!k a. FLOOKUP tenv1 k = SOME (StructArgs a) ==> FST k = NONE) /\
       (!t tv. evaluate_type tenv1 t = SOME tv ==>
               type_memory_bytes cenv t = type_memory_size tv) ==>
       abi_enc_plan (tenv \\ nsid) ty' (type_to_abi_enc_info sf' cenv ty')) /\
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # 'a) list) fmap) tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) ==>
  abi_enc_plan tenv (StructT nsid)
    (type_to_abi_enc_info sf cenv (StructT nsid))
Proof
  strip_tac >>
  gvs[assignable_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
  `?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
            MAP (FST o SND) fields = MAP SND args`
    by (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
        simp[sfields_tenv_consistent_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> simp[]) >>
  drule_all abi_elem_props >> strip_tac >>
  simp[map_struct_field_types] >>
  irule abi_enc_plan_struct >> conj_tac >- gvs[] >>
  qexists `args` >> simp[] >>
  drule_all sfields_tenv_consistent_domsub >> strip_tac >>
  irule abi_enc_plans_map >> simp[MEM_MAP, PULL_EXISTS] >>
  qexists `tenv0` >> simp[] >>
  reverse conj_tac
  >- (irule SUBMAP_TRANS >> qexists `tenv` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `assignable_type (tenv \\ nsid) (SND y)`
    by (qpat_x_assum `EVERY _ args` mp_tac >> simp[EVERY_MEM] >>
        disch_then drule >> simp[]) >>
  conj_tac
  >- (drule assignable_type_well_formed >> simp[well_formed_type_def]) >>
  qpat_x_assum `!x. MEM x args ==> _` (drule_then (drule_then irule)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists `tenv0` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule SUBMAP_TRANS >> qexists `tenv` >> simp[]
QED

(* The ArrayT case of type_to_abi_enc_info_plan, given the element's plan. *)
Theorem type_to_abi_enc_info_plan_array[local]:
  evaluate_type tenv (ArrayT elem bd) = SOME tv /\
  evaluate_type tenv elem = SOME etv /\
  abi_enc_plan tenv elem (type_to_abi_enc_info sf cenv elem) /\
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) ==>
  abi_enc_plan tenv (ArrayT elem bd)
    (type_to_abi_enc_info sf cenv (ArrayT elem bd))
Proof
  strip_tac >>
  Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
      simp[GSYM REPLICATE_GENLIST] >>
      qpat_x_assum `evaluate_type tenv elem = _` assume_tac >>
      drule_all abi_elem_props >> strip_tac >>
      irule abi_enc_plan_sarray >>
      gvs[is_abi_dynamic_def] >>
      drule_all abi_enc_plans_replicate >>
      disch_then (qspec_then `n` mp_tac) >> gvs[]) >>
  qpat_x_assum `evaluate_type tenv elem = _` assume_tac >>
  drule_all abi_elem_props >> strip_tac >> simp[] >>
  irule abi_enc_plan_dynarray >> simp[]
QED

(* type_to_abi_enc_info builds a plan for an assignable type (which has no
   NoneT inside: the compiler gives NoneT AbiComplex [], for which there is
   no plan). sf is the struct map the recursion has narrowed to tenv's
   structs; the sizes and flags come from the whole map. *)
Theorem type_to_abi_enc_info_plan:
  !tenv ty.
    assignable_type tenv ty ==>
    !sf cenv tenv0.
      tenv SUBMAP tenv0 /\
      sfields_tenv_consistent sf tenv /\
      (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
      (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
      (!t tv. evaluate_type tenv0 t = SOME tv ==>
              type_memory_bytes cenv t = type_memory_size tv) ==>
      abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      `?args. FLOOKUP tenv nsid = SOME (StructArgs args)`
        by (qpat_x_assum `assignable_type _ _` mp_tac >>
            simp[assignable_type_def] >> rpt BasicProvers.TOP_CASE_TAC >> simp[]) >>
      drule_all type_to_abi_enc_info_plan_struct >> simp[])
  >~ [`TupleT tys`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[assignable_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
      simp[Once type_to_abi_enc_info_def] >>
      IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
      drule_all abi_elem_props >> strip_tac >>
      irule abi_enc_plan_tuple >> gvs[] >>
      irule abi_enc_plans_map >> simp[] >>
      reverse conj_tac
      >- (qexists `tenv0` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      `assignable_type tenv t`
        by (qpat_x_assum `EVERY _ tys` mp_tac >> simp[EVERY_MEM] >>
            disch_then drule >> simp[]) >>
      conj_tac
      >- (drule assignable_type_well_formed >> simp[well_formed_type_def]) >>
      qpat_x_assum `!ty. MEM ty tys ==> _` (drule_then (drule_then irule)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists `tenv0` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >~ [`ArrayT elem bd`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[assignable_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
      `?etv. evaluate_type tenv elem = SOME etv`
        by (drule assignable_type_well_formed >>
            simp[well_formed_type_def, IS_SOME_EXISTS]) >>
      `abi_enc_plan tenv elem (type_to_abi_enc_info sf cenv elem)`
        by (first_x_assum irule >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qexists `tenv0` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
      drule_all type_to_abi_enc_info_plan_array >> simp[])
  >~ [`BaseT bt`]
  >- (rpt strip_tac >>
      gvs[assignable_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
      Cases_on `bt` >> TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
      simp[type_to_abi_enc_info_def, abi_enc_plan_bytes,
           abi_enc_plan_string] >>
      irule abi_enc_plan_static_copy >> simp[is_abi_dynamic_def] >>
      first_assum (irule_at Any) >> simp[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >>
      gvs[assignable_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
      simp[type_to_abi_enc_info_def] >>
      irule abi_enc_plan_static_copy >> simp[is_abi_dynamic_def] >>
      first_assum (irule_at Any) >> simp[]) >>
  simp[assignable_type_def]
QED

(* ===== The return plan ===== *)

Theorem external_return_needs_wrap_eq:
  external_return_needs_wrap ty = needs_external_call_wrap ty
Proof
  Cases_on `ty` >> simp[external_return_needs_wrap_def,
                        needs_external_call_wrap_def] >>
  rename1 `TupleT ts` >> Cases_on `ts` >>
  simp[external_return_needs_wrap_def] >>
  rename1 `TupleT (_ :: ts)` >> Cases_on `ts` >>
  simp[external_return_needs_wrap_def]
QED

(* The return's encoding plan and buffer size: for an assignable return type
   (not NoneT, and none inside it), the plan update_cenv_ret_abi builds is a
   plan for the type the ABI encodes, and the buffer is exactly its ABI size
   bound. *)
Theorem update_cenv_ret_abi_plan:
  !tops cenv ret.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    assignable_type (type_env tops) ret ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (update_cenv_ret_abi cenv ret).ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) =
      (update_cenv_ret_abi cenv ret).ce_max_return_size
Proof
  rpt gen_tac >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (type_env tops)`
    by simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE`
    by (rw[type_env_def] >> drule type_env_for_module_struct_mem >>
        rw[] >> simp[]) >>
  `struct_args_unique tops`
    by (irule distinct_type_keys_struct_args_unique >> simp[]) >>
  `!t tv. evaluate_type (type_env tops) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv`
    by (rpt strip_tac >> drule_all make_struct_fields_map_memory_size >>
        simp[]) >>
  `abi_enc_plan (type_env tops) ret
     (type_to_abi_enc_info cenv.ce_struct_fields cenv ret)`
    by (irule type_to_abi_enc_info_plan >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexists `type_env tops` >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  `?tv. evaluate_type (type_env tops) ret = SOME tv`
    by (drule assignable_type_well_formed >>
        simp[well_formed_type_def, IS_SOME_EXISTS]) >>
  `type_env tops SUBMAP type_env tops` by simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[update_cenv_ret_abi_def, external_return_needs_wrap_eq] >>
  IF_CASES_TAC >> gvs[] >>
  conj_tac >- (irule abi_enc_plan_tuple >> gvs[] >>
               drule_all abi_enc_plans_replicate >>
               disch_then (qspec_then `SUC 0` mp_tac) >> gvs[REPLICATE]) >>
  simp[vyper_abi_size_bound_def]
QED

(* The same at the env package_external_fn builds. *)
Theorem build_compile_env_ret_abi_plan:
  !tops vis mut func_name args ret_type fn_body use_trans rr ret.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    assignable_type (type_env tops) ret ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (update_cenv_ret_abi
         (build_compile_env tops vis mut func_name args ret_type fn_body
            use_trans with ce_raw_return := rr) ret).ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) =
      (update_cenv_ret_abi
         (build_compile_env tops vis mut func_name args ret_type fn_body
            use_trans with ce_raw_return := rr) ret).ce_max_return_size
Proof
  rpt gen_tac >> strip_tac >> irule update_cenv_ret_abi_plan >>
  simp[build_compile_env_ce_struct_fields]
QED
