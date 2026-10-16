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

