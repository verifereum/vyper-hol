(* Successful type evaluation survives restoration of deleted declarations.
   This supplies the link from struct children evaluated under a descending
   environment to field sizes computed in the complete caller environment. *)
Theory abiCallerTypeEnv
Ancestors
  vyperTypeExprSoundness vyperValue vyperABI finite_map pred_set

Theorem abi_caller_type_restore:
  !removed. FINITE removed ==>
    !env ty tv.
    evaluate_type (DRESTRICT env (COMPL removed)) ty = SOME tv ==>
    evaluate_type env ty = SOME tv
Proof
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >- simp[DRESTRICT_UNIV] >>
  qx_gen_tac `removed` >> strip_tac >> qx_gen_tac `key` >> strip_tac >>
  map_every qx_gen_tac [`env`, `ty`, `tv`] >>
  `COMPL ((key:num option # string) INSERT removed) = COMPL removed DELETE key`
    by simp[EXTENSION, CONJ_COMM] >>
  asm_rewrite_tac [GSYM DRESTRICT_DOMSUB] >> strip_tac >>
  drule (cj 1 evaluate_type_mono) >> strip_tac >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_caller_submap_restriction:
  small SUBMAP large ==>
  DRESTRICT large (COMPL (FDOM large DIFF FDOM small)) = small
Proof
  strip_tac >>
  simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >> qx_gen_tac `key` >>
  Cases_on `key IN FDOM small` >>
  fs[SUBMAP_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem abi_caller_type_submap:
  small SUBMAP large /\ evaluate_type small ty = SOME tv ==>
  evaluate_type large ty = SOME tv
Proof
  strip_tac >> drule abi_caller_submap_restriction >> strip_tac >>
  qpat_assum `DRESTRICT large _ = small` (fn eq =>
    mp_tac (SIMP_RULE (srw_ss()) []
      (SPEC (rand (rand (lhs (concl eq)))) abi_caller_type_restore))) >>
  disch_then (qspecl_then [`large`, `ty`, `tv`] mp_tac) >> simp[]
QED

Theorem abi_caller_submap_delete:
  small SUBMAP large ==> small \\ key SUBMAP large \\ key
Proof
  simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Restoring declarations preserves the ABI descriptor of every successfully
   evaluated source type, including children of nested struct declarations. *)
Theorem abi_caller_abi_type_submap_induction:
  (!env ty. !tv large.
    evaluate_type env ty = SOME tv /\ env SUBMAP large ==>
    vyper_to_abi_type env ty = vyper_to_abi_type large ty) /\
  (!env tys acc. !tvs large.
    evaluate_types env tys acc = SOME tvs /\ env SUBMAP large ==>
    vyper_to_abi_types env tys = vyper_to_abi_types large tys)
Proof
  ho_match_mp_tac evaluate_type_ind >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule_all >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      rename1 `evaluate_type env (ArrayT elem_ty bound) = SOME tv` >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      Cases_on `bound` >> simp[] >> first_x_assum drule_all >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      drule_all FLOOKUP_SUBMAP >> strip_tac >>
      simp[] >> sym_tac >> first_x_assum irule >>
      irule abi_caller_submap_delete >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  first_x_assum (fn th => drule_all (cj 1 th)) >> strip_tac >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_caller_abi_type_submap:
  small SUBMAP large /\ evaluate_type small ty = SOME tv ==>
  vyper_to_abi_type small ty = vyper_to_abi_type large ty
Proof
  metis_tac[abi_caller_abi_type_submap_induction]
QED
