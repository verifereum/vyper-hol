(*
 * Lowering Memory Safety — Proofs
 *
 * Proofs for theorems in loweringMemSafetyProps.
 *)

Theory loweringMemSafetyProofs
Ancestors
  loweringMemSafetyDefs
  allocaRemapDefs pointerConfinedDefs
  vyperTypeSoundness vyperTypeSoundnessDefs vyperTyping vyperValue
  vyperTypeSoundnessHelpers vyperAST rich_list vyperMisc
  list option pair
  venomState venomMemDefs compileVyper words arithmetic

(* ===== value_type_fits_alloca and helpers ===== *)

Theorem evaluate_types_OPT_MMAP:
  !tenv tys tvs.
    evaluate_types tenv tys [] = SOME tvs ⇒
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  rpt strip_tac >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP]
QED

Theorem MEM_type_size_lt_type1_size:
  ∀ty l. MEM ty l ⇒ type_size ty < type1_size l + 1
Proof
  Induct_on `l` >> rpt strip_tac >> Cases_on `MEM ty (h::t)` >>
  gvs[type_size_def] >> (first_x_assum drule >> strip_tac >> decide_tac)
QED

Theorem LIST_REL_value_within_alloca_size_IH:
  ∀l tvs vs cenv tenv.
    evaluate_types tenv l [] = SOME tvs ∧
    LIST_REL value_has_type tvs vs ∧
    EVERY well_formed_type_value tvs ∧
    (∀ty tv v.
       type_size ty < type1_size l + 1 ∧
       evaluate_type tenv ty = SOME tv ∧
       value_has_type tv v ∧ well_formed_type_value tv
       ⇒ value_within_alloca_size cenv ty v)
    ⇒ LIST_REL (value_within_alloca_size cenv) l vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL value_has_type tvs vs` mp_tac >>
  qpat_x_assum `EVERY well_formed_type_value tvs` mp_tac >>
  qpat_x_assum `evaluate_types tenv l [] = SOME tvs` mp_tac >>
  map_every qid_spec_tac [`vs`,`tvs`] >>
  Induct_on `l` >- (
    rpt strip_tac >>
    drule evaluate_types_OPT_MMAP >> strip_tac >>
    fs[OPT_MMAP_def] >>
    Cases_on `vs` >> fs[LIST_REL_def]
  ) >>
  rpt strip_tac >>
  drule evaluate_types_OPT_MMAP >> strip_tac >>
  gvs[OPT_MMAP_def, OPTION_BIND_def, LIST_REL_def] >>
  conj_tac >- (
    first_x_assum irule >> simp[type_size_def] >> decide_tac
  ) >>
  first_x_assum irule >>
  rpt strip_tac >- (
    first_x_assum irule >> simp[type_size_def] >> decide_tac
  ) >- (
    simp[vyperValueTheory.evaluate_types_OPT_MMAP] >> metis_tac[APPEND]
  ) >>
  simp[]
QED

Theorem LIST_REL_value_within_alloca_size_MEM:
  ∀l tvs vs cenv tenv.
    evaluate_types tenv l [] = SOME tvs ∧
    LIST_REL value_has_type tvs vs ∧
    EVERY well_formed_type_value tvs ∧
    (∀ty tv v.
       MEM ty l ∧
       evaluate_type tenv ty = SOME tv ∧
       value_has_type tv v ∧ well_formed_type_value tv
       ⇒ value_within_alloca_size cenv ty v)
    ⇒ LIST_REL (value_within_alloca_size cenv) l vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL value_has_type tvs vs` mp_tac >>
  qpat_x_assum `EVERY well_formed_type_value tvs` mp_tac >>
  qpat_x_assum `evaluate_types tenv l [] = SOME tvs` mp_tac >>
  qid_spec_tac `vs` >> qid_spec_tac `tvs` >>
  Induct_on `l` >- (
    rpt strip_tac >>
    drule evaluate_types_OPT_MMAP >> strip_tac >>
    fs[OPT_MMAP_def] >>
    Cases_on `vs` >> fs[LIST_REL_def]
  ) >>
  rpt strip_tac >>
  drule evaluate_types_OPT_MMAP >> strip_tac >>
  gvs[OPT_MMAP_def, OPTION_BIND_def, LIST_REL_def] >>
  first_x_assum $ irule >> qexists `t` >>
  simp[vyperValueTheory.evaluate_types_OPT_MMAP]
QED

Theorem LIST_REL_value_within_alloca_size_PAIR_MEM:
  ∀l tvs vs cenv tenv.
    evaluate_types tenv l [] = SOME tvs ∧
    LIST_REL value_has_type tvs vs ∧
    EVERY well_formed_type_value tvs ∧
    (∀ty tv v.
       MEM ty l ∧ MEM v vs ∧
       evaluate_type tenv ty = SOME tv ∧
       value_has_type tv v ∧ well_formed_type_value tv
       ⇒ value_within_alloca_size cenv ty v)
    ⇒ LIST_REL (value_within_alloca_size cenv) l vs
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  qpat_x_assum `EVERY well_formed_type_value tvs` mp_tac >>
  qpat_x_assum `LIST_REL value_has_type tvs vs` mp_tac >>
  qpat_x_assum `evaluate_types tenv l [] = SOME tvs` mp_tac >>
  map_every qid_spec_tac [`vs`,`tvs`] >>
  Induct_on `l` >- (
    rpt strip_tac >>
    drule evaluate_types_OPT_MMAP >> strip_tac >>
    fs[OPT_MMAP_def] >>
    Cases_on `vs` >> fs[LIST_REL_def]
  ) >>
  rpt strip_tac >>
  drule evaluate_types_OPT_MMAP >> strip_tac >>
  gvs[OPT_MMAP_def, OPTION_BIND_def, LIST_REL_def] >>
  first_x_assum irule >>
  simp[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem LIST_REL_eta_bridge:
  ∀cenv tys vs.
    LIST_REL (λa a'. value_within_alloca_size cenv a a') tys vs ⇔
    LIST_REL (value_within_alloca_size cenv) tys vs
Proof
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem evaluate_type_ArrayT_inv:
  ∀tenv elem_ty bd tv tv0.
    evaluate_type tenv (ArrayT elem_ty bd) = SOME tv ∧
    evaluate_type tenv elem_ty = SOME tv0
  ⇒ tv = ArrayTV tv0 bd
Proof
  rpt strip_tac >> fs[evaluate_type_def]
QED

Theorem evaluate_type_TupleT_inv:
  ∀tenv tys tv tvs.
    evaluate_type tenv (TupleT tys) = SOME tv ∧
    evaluate_types tenv tys [] = SOME tvs
  ⇒ tv = TupleTV tvs
Proof
  rpt gen_tac >> disch_tac >> gvs[Once evaluate_type_def] >> gvs[]
QED

Theorem evaluate_type_TupleT_SOME:
  ∀tenv l tv.
    evaluate_type tenv (TupleT l) = SOME tv ⇒
    ∃tvs. evaluate_types tenv l [] = SOME tvs ∧ tv = TupleTV tvs
Proof
  rpt strip_tac >> Cases_on `evaluate_types tenv l []` >>
  gvs[evaluate_type_def]
QED

Theorem evaluate_type_ArrayT_SOME:
  ∀tenv t bd tv.
    evaluate_type tenv (ArrayT t bd) = SOME tv ⇒
    ∃tv0. evaluate_type tenv t = SOME tv0 ∧ tv = ArrayTV tv0 bd
Proof
  rpt strip_tac >> Cases_on `evaluate_type tenv t` >>
  gvs[evaluate_type_def] >> metis_tac[]
QED

Theorem values_have_types_LIST_REL:
  ∀tvs vs. values_have_types tvs vs ⇔ LIST_REL value_has_type tvs vs
Proof
  Induct_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, LIST_REL_def]
QED

Theorem value_type_fits_alloca_dynarray:
  ∀cenv tenv elem_ty n vs tv tv0.
    evaluate_type tenv elem_ty = SOME tv0 ∧
    well_formed_type_value tv0 ∧
    evaluate_type tenv (ArrayT elem_ty (Dynamic n)) = SOME tv ∧
    value_has_type tv (ArrayV (DynArrayV vs)) ∧
    well_formed_type_value tv ∧
    (∀v tenv' tv'.
       MEM v vs ∧
       evaluate_type tenv' elem_ty = SOME tv' ∧
       value_has_type tv' v ∧ well_formed_type_value tv'
       ⇒ value_within_alloca_size cenv elem_ty v)
  ⇒ value_within_alloca_size cenv (ArrayT elem_ty (Dynamic n)) (ArrayV (DynArrayV vs))
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once value_within_alloca_size_def] >>
  rpt strip_tac >> drule evaluate_type_ArrayT_inv >> strip_tac >>
  gvs[value_has_type_inv, all_have_type_EVERY] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> (disch_then drule >> simp[]) >>
  strip_tac >> first_x_assum irule >> fs[EVERY_MEM]
QED

Theorem value_type_fits_alloca_tuple:
  ∀cenv tenv tys vs tv tvs'.
    evaluate_types tenv tys [] = SOME tvs' ∧
    EVERY well_formed_type_value tvs' ∧
    evaluate_type tenv (TupleT tys) = SOME tv ∧
    value_has_type tv (ArrayV (TupleV vs)) ∧
    well_formed_type_value tv ∧
    (∀ty tv1 v.
       MEM ty tys ∧ MEM v vs ∧
       evaluate_type tenv ty = SOME tv1 ∧
       value_has_type tv1 v ∧ well_formed_type_value tv1
       ⇒ value_within_alloca_size cenv ty v)
  ⇒ value_within_alloca_size cenv (TupleT tys) (ArrayV (TupleV vs))
Proof
  rpt gen_tac >> strip_tac >>
  fs[value_within_alloca_size_def, value_has_type_inv,
     values_have_types_LIST_REL, AllCaseEqs()] >>
  `tv = TupleTV tvs'` by metis_tac[evaluate_type_TupleT_inv] >> fs[] >>
  conj_tac >- metis_tac[LIST_REL_LENGTH, evaluate_types_OPT_MMAP, OPT_MMAP_LENGTH] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  irule LIST_REL_value_within_alloca_size_PAIR_MEM >>
  qexistsl [`tenv`,`tvs`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem baseT_fits_alloca:
  ∀cenv tenv b tv v.
    evaluate_type tenv (BaseT b) = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
  ⇒ value_within_alloca_size cenv (BaseT b) v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `b` >> Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_inv, value_within_alloca_size_def,
      AllCaseEqs()]
QED

Theorem TupleTV_ArrayV_TupleV_has_type:
  ∀tvs vs. value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) ⇒ values_have_types tvs vs
Proof
  rpt strip_tac >> gvs[value_has_type_inv, type_value_11]
QED

Theorem ArrayTV_Dynamic_DynArrayV_has_type:
  ∀tv0 n vs. value_has_type (ArrayTV tv0 (Dynamic n)) (ArrayV (DynArrayV vs)) ⇒
    LENGTH vs ≤ n ∧ EVERY (value_has_type tv0) vs
Proof
  rpt gen_tac >> strip_tac >> first_x_assum (mp_tac o REWRITE_RULE [value_has_type_inv]) >> simp[all_have_type_EVERY] >> strip_tac >> gvs[type_value_11]
QED

Theorem ArrayTV_Fixed_TupleV_contra:
  ∀tv0 n vs. value_has_type (ArrayTV tv0 (Fixed n)) (ArrayV (TupleV vs)) ⇒ F
Proof
  rpt gen_tac >> disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [Once value_has_type_inv]) >> gvs[type_value_distinct]
QED

Theorem well_formed_type_value_TupleTV_imp:
  ∀tvs. well_formed_type_value (TupleTV tvs) ⇒ EVERY well_formed_type_value tvs
Proof
  rpt strip_tac >> fs[well_formed_type_value_def, ETA_THM]
QED

Theorem well_formed_type_value_ArrayTV_imp:
  ∀tv b. well_formed_type_value (ArrayTV tv b) ⇒ well_formed_type_value tv
Proof
  rpt strip_tac >> fs[well_formed_type_value_def]
QED

Theorem value_type_fits_alloca_TupleT:
  ∀cenv tenv l tv v.
    evaluate_type tenv (TupleT l) = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv ∧
    (∀ty tv' v'.
       type_size ty < type_size (TupleT l) ∧
       evaluate_type tenv ty = SOME tv' ∧
       value_has_type tv' v' ∧ well_formed_type_value tv'
       ⇒ value_within_alloca_size cenv ty v')
  ⇒ value_within_alloca_size cenv (TupleT l) v
Proof
  rpt strip_tac >>
  drule evaluate_type_TupleT_SOME >> strip_tac >>
  qpat_x_assum `tv = TupleTV tvs` SUBST_ALL_TAC >>
  imp_res_tac well_formed_type_value_TupleTV_imp >>
  Cases_on `v` >> simp[value_within_alloca_size_def] >>
  Cases_on `a` >> simp[value_within_alloca_size_def] >>
  imp_res_tac TupleTV_ArrayV_TupleV_has_type >>
  simp[values_have_types_LIST_REL] >>
  conj_tac >- (
    imp_res_tac values_have_types_length >>
    drule evaluate_types_OPT_MMAP >> strip_tac >>
    imp_res_tac OPT_MMAP_LENGTH >> simp[]) >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  irule LIST_REL_value_within_alloca_size_IH >>
  simp[values_have_types_LIST_REL] >>
  qexistsl [`tenv`,`tvs`] >> simp[] >>
  conj_tac >- (
    rpt strip_tac >>
    first_x_assum irule >>
    simp[type_size_def] >> decide_tac) >>
  simp[GSYM values_have_types_LIST_REL]
QED

Theorem value_type_fits_alloca_ArrayT:
  ∀cenv tenv t b tv v.
    evaluate_type tenv (ArrayT t b) = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv ∧
    (∀ty tv' v'.
       type_size ty < type_size (ArrayT t b) ∧
       evaluate_type tenv ty = SOME tv' ∧
       value_has_type tv' v' ∧ well_formed_type_value tv'
       ⇒ value_within_alloca_size cenv ty v')
  ⇒ value_within_alloca_size cenv (ArrayT t b) v
Proof
  rpt strip_tac >>
  drule evaluate_type_ArrayT_SOME >> strip_tac >>
  qpat_x_assum `tv = ArrayTV tv0 b` SUBST_ALL_TAC >>
  imp_res_tac well_formed_type_value_ArrayTV_imp >>
  Cases_on `v` >> simp[value_within_alloca_size_def] >>
  Cases_on `a` >> simp[value_within_alloca_size_def] >>
  Cases_on `b` >> simp[value_within_alloca_size_def] >>
  TRY (imp_res_tac ArrayTV_Fixed_TupleV_contra >> simp[]) >>
  imp_res_tac ArrayTV_Dynamic_DynArrayV_has_type >>
  conj_tac >- simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum irule >>
  conj_tac >- (simp[type_size_def, bound_size_def] >> decide_tac) >>
  qexists `tv0` >> simp[] >>
  gvs[EVERY_MEM]
QED

Theorem value_type_fits_alloca:
  ∀cenv tenv ty tv v.
    evaluate_type tenv ty = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
  ⇒ value_within_alloca_size cenv ty v
Proof
  measureInduct_on `type_size ty` >>
  rpt strip_tac >>
  Cases_on `ty`
  >- metis_tac[baseT_fits_alloca]
  >- (drule evaluate_type_TupleT_SOME >> strip_tac >>
     qpat_x_assum `tv = TupleTV tvs` SUBST_ALL_TAC >>
     imp_res_tac well_formed_type_value_TupleTV_imp >>
     Cases_on `v` >> simp[value_within_alloca_size_def] >>
     Cases_on `a` >> simp[value_within_alloca_size_def] >>
     imp_res_tac TupleTV_ArrayV_TupleV_has_type >>
     simp[values_have_types_LIST_REL] >>
     conj_tac >- (
       imp_res_tac values_have_types_length >>
       drule evaluate_types_OPT_MMAP >> strip_tac >>
       imp_res_tac OPT_MMAP_LENGTH >> simp[]) >>
     CONV_TAC(DEPTH_CONV ETA_CONV) >>
     irule LIST_REL_value_within_alloca_size_IH >>
     simp[values_have_types_LIST_REL] >>
     qexistsl [`tenv`,`tvs`] >> simp[] >>
     conj_tac >- (
       rpt gen_tac >> strip_tac >>
       first_x_assum (qspec_then `ty` mp_tac) >>
       simp[type_size_def] >> strip_tac >>
       first_x_assum (qspecl_then [`cenv`,`tenv`,`tv`,`v`] mp_tac) >>
       simp[]) >>
     simp[GSYM values_have_types_LIST_REL])
  >- (drule evaluate_type_ArrayT_SOME >> strip_tac >>
     qpat_x_assum `tv = ArrayTV tv0 b` SUBST_ALL_TAC >>
     imp_res_tac well_formed_type_value_ArrayTV_imp >>
     Cases_on `v` >> simp[value_within_alloca_size_def] >>
     Cases_on `a` >> simp[value_within_alloca_size_def] >>
     Cases_on `b` >> simp[value_within_alloca_size_def] >>
     TRY (imp_res_tac ArrayTV_Fixed_TupleV_contra >> simp[]) >>
     imp_res_tac ArrayTV_Dynamic_DynArrayV_has_type >>
     conj_tac >- simp[] >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `∀y. type_size y < _ ⇒ _` (fn ih => mp_tac (Q.SPEC `t` ih)) >>
     simp[type_size_def, bound_size_def] >> strip_tac >>
     first_x_assum (qspecl_then [`cenv`,`tenv`,`tv0`,`v`] mp_tac) >>
     impl_tac >- (simp[] >> gvs[EVERY_MEM]) >> simp[])
  >- (qpat_x_assum `∀y. type_size y < _ ⇒ _` kall_tac >>
     Cases_on `v` >> simp[value_within_alloca_size_def] >> simp[EVERY_MEM])
  >- (qpat_x_assum `∀y. type_size y < _ ⇒ _` kall_tac >>
     Cases_on `v` >> simp[value_within_alloca_size_def])
  >- (qpat_x_assum `∀y. type_size y < _ ⇒ _` kall_tac >>
     Cases_on `v` >> simp[value_within_alloca_size_def])
QED

(* ===== General helpers ===== *)

Theorem alloca_regions_same:
  ∀s a1 a2 b1 sz1 b2 sz2 x.
    allocas_non_overlapping s ∧
    FLOOKUP s.vs_allocas a1 = SOME (b1,sz1) ∧
    FLOOKUP s.vs_allocas a2 = SOME (b2,sz2) ∧
    b1 ≤ x ∧ x < b1 + sz1 ∧ b2 ≤ x ∧ x < b2 + sz2
    ⇒ a1 = a2 ∧ b1 = b2 ∧ sz1 = sz2
Proof
  rpt strip_tac >> Cases_on `a1 = a2` >- (
    fs[SOME_11]
  ) >>
  fs[allocas_non_overlapping_def] >>
  first_x_assum (qspecl_then [`a1`,`a2`,`b1`,`sz1`,`b2`,`sz2`] mp_tac) >>
  simp[] >> strip_tac >> decide_tac
QED

Theorem RTC_step_preserves:
  ∀R P.
    (∀x y. R x y ∧ P x ⇒ P y) ⇒
    ∀x y. R꙳ x y ⇒ P x ⇒ P y
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >>
  rpt strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem reachable_preserves_safety:
  ∀fn roots s s'.
    step_preserves_safety fn roots ∧
    alloca_safe_access fn roots s ∧
    ptrs_in_alloca_bounds fn roots s ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn roots s' ∧ ptrs_in_alloca_bounds fn roots s'
Proof
  simp[reachable_by_execution_def] >>
  rpt gen_tac >> strip_tac >>
  `∀x y.
    (λs1 s2. ∃inst bb.
       MEM bb fn.fn_blocks ∧ MEM inst bb.bb_instructions ∧
       step_inst_base inst s1 = OK s2 ∧
       ¬is_terminator inst.inst_opcode ∧ ¬is_ext_call_op inst.inst_opcode)꙳ x y ⇒
    alloca_safe_access fn roots x ∧ ptrs_in_alloca_bounds fn roots x ⇒
    alloca_safe_access fn roots y ∧ ptrs_in_alloca_bounds fn roots y`
  by (
    ho_match_mp_tac relationTheory.RTC_INDUCT >>
    simp[] >>
    rpt strip_tac >>
    metis_tac[step_preserves_safety_def]) >>
  metis_tac[]
QED

Theorem reachable_preserves_alloca_safe_access:
  ∀fn roots s s'.
    step_preserves_safety fn roots ∧
    alloca_safe_access fn roots s ∧
    ptrs_in_alloca_bounds fn roots s ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn roots s'
Proof
  metis_tac[reachable_preserves_safety]
QED

(* ===== TOP-LEVEL THEOREM (stub) ===== *)

Theorem lowering_memory_safe:
  ∀selectors ext_fns int_fns fb_fn (dispatch:dispatch_strategy)
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s0 s.
    MEM fn (FST (run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s0 ∧
    state_matches_fn fn s0 ∧
    well_typed_lowering cenv ∧
    (∀aid off asz.
       FLOOKUP s0.vs_allocas aid = SOME (off,asz) ⇒
       off + asz ≤ LENGTH s0.vs_memory ∧ off + asz < dimword (:256)) ∧
    reachable_by_execution fn s0 s
    ⇒ ptrs_in_alloca_bounds fn (alloca_roots fn) s ∧
      alloca_safe_access fn (alloca_roots fn) s
Proof
  (* TEMPORARILY CHEATED - progress theorem; requires lowering type-soundness
     integration and a real execution-safety model. *)
  cheat
QED
