(* Algebraic Optimization — Well-formedness & SSA Preservation
 *
 * Key lemmas:
 *   ao_fresh_id_gt_mid     — fresh IDs are > max_id
 *   ao_fresh_id_inj        — fresh IDs are injective in (id, slot)
 *   ao_transform_function preserves wf_function and ssa_form
 *)

Theory algebraicOptWf
Ancestors
  algebraicOptDefs venomWf
Libs
  pairLib

(* ===== ao_fresh_id properties ===== *)

Theorem ao_fresh_id_gt:
  !mid id slot. ao_fresh_id mid id slot > mid
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_ge:
  !mid id slot. ao_fresh_id mid id slot >= mid + 1
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_inj:
  !mid id1 slot1 id2 slot2.
    slot1 < 3 /\ slot2 < 3 /\
    ao_fresh_id mid id1 slot1 = ao_fresh_id mid id2 slot2 ==>
    id1 = id2 /\ slot1 = slot2
Proof
  simp[ao_fresh_id_def] >> rpt strip_tac >>
  `id1 * 3 + slot1 = id2 * 3 + slot2` by simp[] >>
  `(id1 * 3 + slot1) MOD 3 = (id2 * 3 + slot2) MOD 3` by simp[] >>
  `slot1 MOD 3 = slot2 MOD 3` by metis_tac[arithmeticTheory.MOD_TIMES] >>
  `slot1 = slot2` by metis_tac[arithmeticTheory.LESS_MOD] >>
  fs[]
QED

(* FOLDL MAX monotone: a <= FOLDL MAX a l *)
Triviality foldl_max_base[local]:
  !(l:num list) a. a <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  `MAX a h <= FOLDL MAX (MAX a h) l` suffices_by simp[] >>
  metis_tac[]
QED

(* FOLDL MAX monotone in accumulator *)
Triviality foldl_max_mono[local]:
  !(l:num list) a b. a <= b ==> FOLDL MAX a l <= FOLDL MAX b l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[arithmeticTheory.MAX_DEF]
QED

(* MEM x l ==> x <= FOLDL MAX a l *)
Triviality foldl_max_mem[local]:
  !(l:num list) x a. MEM x l ==> x <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  DISCH_THEN DISJ_CASES_TAC
  >- (gvs[] >>
      `MAX a x <= FOLDL MAX (MAX a x) l` by simp[foldl_max_base] >>
      simp[])
  >- (`x <= FOLDL MAX a l` by (first_x_assum irule >> simp[]) >>
      `FOLDL MAX a l <= FOLDL MAX (MAX a h) l` by
        (irule foldl_max_mono >> simp[]) >>
      simp[])
QED

(* Any original ID <= fn_max_inst_id *)
Theorem fn_max_inst_id_bound:
  !fn inst. MEM inst (fn_insts fn) ==> inst.inst_id <= fn_max_inst_id fn
Proof
  rpt strip_tac >>
  simp[fn_max_inst_id_def] >>
  irule foldl_max_mem >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* ===== Phase 1: offset preserves inst_id ===== *)

Theorem ao_handle_offset_inst_preserves_id:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt CASE_TAC >> simp[]
QED

