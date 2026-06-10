(* Target property helpers for algebraic optimization proofs.
 *
 * TOP-LEVEL:
 *   ao_fn_targets_chain_tail_var
 *   ao_fn_targets_chain_var_is_key
 *   ao_fn_targets_key_is_output
 *   fn_insts_blocks_map_offset
 *)

Theory aoTargetProps
Ancestors
  algebraicOptDefs venomInst
Libs
  BasicProvers

Triviality iszero_step_chain_tail_var[local]:
  !h acc.
    (!v chain k. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    (!v chain k. ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w)
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  rpt gen_tac >>
  TRY (strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  simp[alistTheory.ALOOKUP_def] >>
  IF_CASES_TAC >> strip_tac >> gvs[listTheory.LENGTH_SNOC] >>
  TRY (res_tac >> simp[] >> NO_TAC) >>
  Cases_on `k < LENGTH x` >>
  gvs[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  TRY (res_tac >> simp[] >> NO_TAC) >>
  rpt (qpat_x_assum `!v chain k. _` kall_tac) >>
  rpt (qpat_x_assum `!chain. _` kall_tac) >>
  rpt (qpat_x_assum `!k. _` kall_tac) >>
  FIRST [
    qmatch_goalsub_abbrev_tac `(SNOC _ _)❲idx❳` >>
    `idx = LENGTH x` by (
      qunabbrev_tac `idx` >>
      qpat_x_assum `~(_ < LENGTH _)` mp_tac >>
      qpat_x_assum `_ < SUC _` mp_tac >>
      DECIDE_TAC) >>
    gvs[listTheory.EL_LENGTH_SNOC],
    Cases_on `k` >> gvs[] >>
    rename1 `SUC n` >> Cases_on `n` >> gvs[] >>
    gvs[listTheory.EL_restricted, listTheory.HD]
  ]
QED

Triviality foldl_chain_tail_var[local]:
  !insts acc.
    (!v chain k. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    (!v chain k. ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v =
       SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac iszero_step_chain_tail_var >>
  first_assum ACCEPT_TAC
QED

Theorem ao_fn_targets_chain_tail_var:
  !fn v chain k.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    ?w. EL k chain = Var w
Proof
  rpt strip_tac >>
  `!v' ch k'. ALOOKUP (ao_compute_fn_iszero_targets fn) v' = SOME ch /\
     0 < k' /\ k' < LENGTH ch ==> ?w. EL k' ch = Var w` by
    (simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
     match_mp_tac foldl_chain_tail_var >> simp[alistTheory.ALOOKUP_def]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED


Triviality snoc_var_el_cases[local]:
  !prev key k w.
    0 < k /\ k < LENGTH (SNOC (Var key) prev) /\
    EL k (SNOC (Var key) prev) = Var w ==>
    w = key \/ (k < LENGTH prev /\ EL k prev = Var w)
Proof
  rpt strip_tac >>
  Cases_on `k < LENGTH prev`
  >- (disj2_tac >> gvs[listTheory.EL_SNOC])
  >- (disj1_tac >>
      `k = LENGTH prev` by gvs[listTheory.LENGTH_SNOC] >>
      gvs[listTheory.EL_LENGTH_SNOC])
QED

Triviality chain_var_is_key_extend[local]:
  !acc key chain_val.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) /\
    (!k w. 0 < k /\ k < LENGTH chain_val /\ EL k chain_val = Var w ==>
       w = key \/ ALOOKUP acc w <> NONE) ==>
    (!v chain k w.
       ALOOKUP ((key, chain_val) :: acc) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP ((key, chain_val) :: acc) w <> NONE)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  strip_tac >>
  simp[alistTheory.ALOOKUP_def] >>
  Cases_on `v = key` >> Cases_on `w = key` >> gvs[]
  >- (first_x_assum (qspecl_then [`k`, `w`] mp_tac) >> gvs[])
  >- (first_x_assum (qspecl_then [`v`, `chain`, `k`, `w`] mp_tac) >> gvs[])
QED

Triviality iszero_step_cases[local]:
  !acc h. ao_compute_iszero_step acc h = acc \/
    ?out prev. ao_compute_iszero_step acc h = (out, SNOC (Var out) prev) :: acc /\
      (LENGTH prev = 1 \/ ?s. ALOOKUP acc s = SOME prev)
Proof
  rpt gen_tac >> simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  disj2_tac >> simp[] >> metis_tac[]
QED

Triviality iszero_step_chain_var_is_key[local]:
  !acc h.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) ==>
    (!v chain k w. ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP (ao_compute_iszero_step acc h) w <> NONE)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`acc`, `h`] strip_assume_tac iszero_step_cases
  >- (pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_x_assum `ao_compute_iszero_step _ _ = _` SUBST_ALL_TAC >>
      qspecl_then [`acc`, `out`, `SNOC (Var out) prev`]
        (MATCH_MP_TAC o BETA_RULE) chain_var_is_key_extend >>
      conj_tac
      >- (rpt strip_tac >> res_tac)
      >- (rpt strip_tac >>
          drule_all snoc_var_el_cases >> strip_tac >> gvs[]))
  >- (qpat_x_assum `ao_compute_iszero_step _ _ = _` SUBST_ALL_TAC >>
      qspecl_then [`acc`, `out`, `SNOC (Var out) prev`]
        (MATCH_MP_TAC o BETA_RULE) chain_var_is_key_extend >>
      conj_tac
      >- (rpt strip_tac >> res_tac)
      >- (rpt strip_tac >>
          Cases_on `k < LENGTH prev`
          >- (disj2_tac >>
              `EL k prev = Var w` by
                (qpat_x_assum `EL k (SNOC _ _) = _` mp_tac >>
                 simp[listTheory.EL_SNOC]) >>
              res_tac)
          >- (disj1_tac >>
              `k = LENGTH prev` by
                (qpat_x_assum `k < LENGTH (SNOC _ _)` mp_tac >>
                 simp[listTheory.LENGTH_SNOC]) >>
              qpat_x_assum `EL k (SNOC _ _) = _` mp_tac >>
              simp[listTheory.EL_LENGTH_SNOC])))
QED

Triviality foldl_chain_var_is_key[local]:
  !insts acc.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) ==>
    (!v chain k w.
       ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP (FOLDL ao_compute_iszero_step acc insts) w <> NONE)
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac iszero_step_chain_var_is_key >>
  first_assum ACCEPT_TAC
QED

Theorem ao_fn_targets_chain_var_is_key:
  !fn v chain k w.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
    ALOOKUP (ao_compute_fn_iszero_targets fn) w <> NONE
Proof
  rpt strip_tac >>
  `!v' chain' k' w'.
     ALOOKUP (ao_compute_fn_iszero_targets fn) v' = SOME chain' /\
     0 < k' /\ k' < LENGTH chain' /\ EL k' chain' = Var w' ==>
     ALOOKUP (ao_compute_fn_iszero_targets fn) w' <> NONE` by
    (simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
     match_mp_tac foldl_chain_var_is_key >> simp[alistTheory.ALOOKUP_def]) >>
  metis_tac[]
QED

Triviality iszero_step_key_output[local]:
  !acc h v chain.
    ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
    ALOOKUP acc v = NONE ==>
    MEM v h.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ALOOKUP (ao_compute_iszero_step _ _) _ = _` mp_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[alistTheory.ALOOKUP_def] >> IF_CASES_TAC >> gvs[]
QED

Triviality foldl_iszero_key_output[local]:
  !insts acc v chain.
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    ALOOKUP acc v = NONE ==>
    ?inst. MEM inst insts /\ MEM v inst.inst_outputs
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `ao_compute_iszero_step acc h` >>
  Cases_on `ALOOKUP (ao_compute_iszero_step acc h) v`
  >- (first_x_assum (qspecl_then
        [`ao_compute_iszero_step acc h`, `v`, `chain`] mp_tac) >>
      simp[] >> metis_tac[])
  >- (`MEM v h.inst_outputs` by metis_tac[iszero_step_key_output] >>
      metis_tac[])
QED

Theorem ao_fn_targets_key_is_output:
  !fn v chain.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain ==>
    ?inst. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs
Proof
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  metis_tac[foldl_iszero_key_output, alistTheory.ALOOKUP_def]
QED

Theorem fn_insts_blocks_map_offset:
  !bbs inst.
    MEM inst (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) bbs)) ==>
    ?inst0. MEM inst0 (fn_insts_blocks bbs) /\
            inst = ao_handle_offset_inst inst0
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

