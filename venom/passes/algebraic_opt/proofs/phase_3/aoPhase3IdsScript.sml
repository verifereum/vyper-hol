(* Phase 3 WF: instruction-id distinctness for ao_transform_block.
 *
 * TOP-LEVEL:
 *   ao_phase3_inst_ids_distinct — fn_inst_ids_distinct preserved by the
 *     phase-3 rewrite, given all original ids are bounded by mid.
 *
 * Strategy (mirrors phase 4): every transformed instruction keeps the
 * original id (<= mid) exactly once; helper instructions get fresh ids
 * ao_fresh_id mid (original id) slot (> mid), injective in (id, slot).
 * Split the flattened id list into the <= mid part (= original ids) and
 * the > mid part (fresh ids), each distinct.
 *)

Theory aoPhase3Ids
Ancestors
  algebraicOptDefs venomInst venomWf passSimulationDefs passSimulationProps
  indexedLists rich_list
Libs
  pairLib BasicProvers

(* ===== ao_fresh_id arithmetic ===== *)

Triviality ao_fresh_id_gt[local]:
  !mid id slot. mid < ao_fresh_id mid id slot
Proof
  simp[ao_fresh_id_def]
QED

Triviality ao_fresh_id_inj3[local]:
  !mid a sa b sb.
    sa < 3 /\ sb < 3 /\ ao_fresh_id mid a sa = ao_fresh_id mid b sb ==> a = b
Proof
  rw[ao_fresh_id_def]
QED

(* ===== id preservation for resolve / flips ===== *)

Triviality resolve_id[local]:
  !targets inst. (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality pre_flip_id[local]:
  !inst. (ao_pre_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_id[local]:
  !inst. (ao_post_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality map_post_flip_ids[local]:
  !l. MAP (\i. i.inst_id) (MAP ao_post_flip_inst l) =
      MAP (\i. i.inst_id) l
Proof
  Induct >> simp[post_flip_id]
QED

(* ===== id-distinctness invariant for a single transformed instruction ===== *)

Definition idok_def:
  idok mid base (ids:num list) <=>
    FILTER (\id. id <= mid) ids = [base] /\
    ALL_DISTINCT (FILTER (\id. ~(id <= mid)) ids) /\
    (!x. MEM x ids /\ ~(x <= mid) ==> ?s. s < 3 /\ x = ao_fresh_id mid base s)
End

Triviality idok_single[local]:
  !mid base. base <= mid ==> idok mid base [base]
Proof
  rw[idok_def]
QED

Triviality idok_gt_form[local]:
  !mid base ids y.
    idok mid base ids /\ MEM y ids /\ ~(y <= mid) ==>
    ?s. s < 3 /\ y = ao_fresh_id mid base s
Proof
  rw[idok_def] >> metis_tac[]
QED

(* ===== id lists for each per-opcode helper ===== *)

(* simple opts never introduce fresh ids *)
Triviality opt_shift_ids[local]:
  !inst. MAP (\i. i.inst_id) (ao_opt_shift inst) = [inst.inst_id]
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[]
QED

Triviality opt_signextend_ids[local]:
  !ra lbl idx inst.
    MAP (\i. i.inst_id) (ao_opt_signextend ra lbl idx inst) = [inst.inst_id]
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_exp_ids[local]:
  !inst. MAP (\i. i.inst_id) (ao_opt_exp inst) = [inst.inst_id]
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[]
QED

Triviality opt_addsub_ids[local]:
  !inst. MAP (\i. i.inst_id) (ao_opt_addsub inst) = [inst.inst_id]
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_and_ids[local]:
  !inst. MAP (\i. i.inst_id) (ao_opt_and inst) = [inst.inst_id]
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[]
QED

Triviality opt_muldiv_ids[local]:
  !inst. MAP (\i. i.inst_id) (ao_opt_muldiv inst) = [inst.inst_id]
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_or_ids[local]:
  !dfg inst. MAP (\i. i.inst_id) (ao_opt_or dfg inst) = [inst.inst_id]
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[]
QED

(* eq: one branch introduces a single fresh helper (slot 0) *)
Triviality opt_eq_idok[local]:
  !mid dfg inst. inst.inst_id <= mid ==>
    idok mid inst.inst_id (MAP (\i. i.inst_id) (ao_opt_eq mid dfg inst))
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >>
  gvs[idok_def, ao_fresh_id_def] >> rw[] >> gvs[] >>
  qexists_tac `0` >> simp[ao_fresh_id_def]
QED

(* comparator helpers: up to two fresh helpers (slots 0, 1) *)
Triviality cmp_prefer_iz_zero_idok[local]:
  !mid id op1 inst. inst.inst_id = id /\ id <= mid ==>
    idok mid id (MAP (\i. i.inst_id) (ao_cmp_prefer_iz_zero mid id op1 inst))
Proof
  rw[ao_cmp_prefer_iz_zero_def] >>
  gvs[idok_def, ao_fresh_id_def] >> rw[] >> gvs[] >>
  qexists_tac `0` >> simp[ao_fresh_id_def]
QED

Triviality cmp_prefer_iz_max_idok[local]:
  !mid id op1 inst. inst.inst_id = id /\ id <= mid ==>
    idok mid id (MAP (\i. i.inst_id) (ao_cmp_prefer_iz_max mid id op1 inst))
Proof
  rw[ao_cmp_prefer_iz_max_def] >>
  gvs[idok_def, ao_fresh_id_def] >> rw[] >> gvs[] >>
  ((qexists_tac `0` >> simp[ao_fresh_id_def] >> NO_TAC) ORELSE
   (qexists_tac `1` >> simp[ao_fresh_id_def]))
QED

Triviality cmp_prefer_iz_general_idok[local]:
  !mid id op1 op2 inst. inst.inst_id = id /\ id <= mid ==>
    idok mid id (MAP (\i. i.inst_id) (ao_cmp_prefer_iz_general mid id op1 op2 inst))
Proof
  rw[ao_cmp_prefer_iz_general_def] >>
  gvs[idok_def, ao_fresh_id_def] >> rw[] >> gvs[] >>
  ((qexists_tac `0` >> simp[ao_fresh_id_def] >> NO_TAC) ORELSE
   (qexists_tac `1` >> simp[ao_fresh_id_def]))
QED

Triviality opt_comparator_idok[local]:
  !mid dfg ra lbl idx inst. inst.inst_id <= mid ==>
    idok mid inst.inst_id
      (MAP (\i. i.inst_id) (ao_opt_comparator mid dfg ra lbl idx inst))
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  FIRST [
    irule idok_single >> simp[],
    irule cmp_prefer_iz_zero_idok >> simp[],
    irule cmp_prefer_iz_max_idok >> simp[],
    irule cmp_prefer_iz_general_idok >> simp[],
    (gvs[idok_def, ao_fresh_id_def] >> rw[] >> gvs[] >>
     qexists_tac `0` >> simp[ao_fresh_id_def])
  ]
QED

(* ===== peephole and transform_inst ===== *)

Triviality peephole_idok[local]:
  !mid dfg ra lbl idx inst. inst.inst_id <= mid ==>
    idok mid inst.inst_id
      (MAP (\i. i.inst_id) (ao_peephole_inst mid dfg ra lbl idx inst))
Proof
  rpt strip_tac >>
  rw[ao_peephole_inst_def] >>
  simp[opt_shift_ids, opt_signextend_ids, opt_exp_ids, opt_addsub_ids,
       opt_and_ids, opt_muldiv_ids, opt_or_ids] >>
  TRY (irule idok_single >> simp[] >> NO_TAC) >>
  FIRST [
    irule opt_eq_idok >> simp[],
    irule opt_comparator_idok >> simp[]
  ]
QED

Triviality producer_ids[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==> MAP (\i. i.inst_id) r = [inst.inst_id]
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[]
QED

Triviality transform_inst_idok[local]:
  !mid dfg ra lbl idx targets inst. inst.inst_id <= mid ==>
    idok mid inst.inst_id
      (MAP (\i. i.inst_id)
        (ao_transform_inst mid dfg ra lbl idx targets inst))
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM, resolve_id, map_post_flip_ids] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >>
       simp[resolve_id, map_post_flip_ids]) >>
  FIRST [
    irule idok_single >> simp[],
    (drule producer_ids >> strip_tac >>
     gvs[map_post_flip_ids, resolve_id] >> irule idok_single >> simp[]),
    (qspecl_then [`mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_idok >>
     impl_tac >- gvs[pre_flip_id, resolve_id] >>
     simp[pre_flip_id, resolve_id, map_post_flip_ids])
  ]
QED

(* ===== pieces: distinctness over a flattened list of transformed insts ===== *)

Triviality pieces_le[local]:
  !mid pieces.
    EVERY (\p. SND p <> [] ==> idok mid (FST p) (SND p)) pieces /\
    EVERY (\p. ?ids. SND p = ids) pieces /\
    EVERY (\p. idok mid (FST p) (SND p)) pieces ==>
    FILTER (\id. id <= mid) (FLAT (MAP SND pieces)) = MAP FST pieces
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB] >>
  fs[idok_def]
QED

Triviality pieces_gt_mem[local]:
  !mid pieces y.
    EVERY (\p. idok mid (FST p) (SND p)) pieces /\
    MEM y (FILTER (\id. ~(id <= mid)) (FLAT (MAP SND pieces))) ==>
    ?b s. MEM b (MAP FST pieces) /\ s < 3 /\ y = ao_fresh_id mid b s
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.MEM_FILTER] >> gvs[]
  >- (fs[idok_def] >> res_tac >> metis_tac[])
  >- (first_x_assum drule >> simp[listTheory.MEM_FILTER] >>
      strip_tac >> metis_tac[])
QED

Triviality pieces_gt[local]:
  !mid pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. idok mid (FST p) (SND p)) pieces ==>
    ALL_DISTINCT
      (FILTER (\id. ~(id <= mid)) (FLAT (MAP SND pieces)))
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  PURE_REWRITE_TAC[listTheory.MAP, pairTheory.SND, listTheory.FLAT,
    listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >- fs[idok_def]
  >- (first_x_assum irule >> fs[])
  >- (rpt strip_tac >>
      rename1 `MEM y (FILTER _ h1)` >>
      `MEM y h1 /\ ~(y <= mid)` by
        (qpat_x_assum `MEM y (FILTER _ h1)` mp_tac >>
         simp[listTheory.MEM_FILTER]) >>
      `?s1. s1 < 3 /\ y = ao_fresh_id mid h0 s1` by
        (qspecl_then [`mid`, `h0`, `h1`, `y`] mp_tac idok_gt_form >> fs[]) >>
      `?b s2. MEM b (MAP FST pieces) /\ s2 < 3 /\
              y = ao_fresh_id mid b s2` by
        (irule pieces_gt_mem >> fs[]) >>
      gvs[] >>
      `h0 = b` by metis_tac[ao_fresh_id_inj3] >>
      gvs[])
QED

(* ===== MAPi fusion ===== *)

Triviality map_fst_mapi_pair[local]:
  !l (f:num -> 'a -> 'b) (g:'a -> 'c).
    MAP FST (MAPi (\i x. (g x, f i x)) l) = MAP g l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`f o SUC`, `g`] mp_tac) >>
  simp[combinTheory.o_DEF]
QED

Triviality map_snd_mapi_pair[local]:
  !l (f:num -> 'a -> 'b) (g:'a -> 'c).
    MAP SND (MAPi (\i x. (g x, f i x)) l) = MAPi (\i x. f i x) l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`f o SUC`, `g`] mp_tac) >>
  simp[combinTheory.o_DEF]
QED

Triviality map_flat_mapi[local]:
  !l (f:'b -> 'c) (g:num -> 'a -> 'b list).
    MAP f (FLAT (MAPi g l)) = FLAT (MAPi (\i x. MAP f (g i x)) l)
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  simp[listTheory.MAP_FLAT, listTheory.MAP_MAP_o] >>
  first_x_assum (qspecl_then [`f`, `g o SUC`] mp_tac) >>
  simp[combinTheory.o_DEF, listTheory.MAP_FLAT, listTheory.MAP_MAP_o]
QED

(* ===== block / function plumbing ===== *)

Definition block_pieces_def:
  block_pieces mid dfg ra targets bb =
    MAPi (\idx inst.
      (inst.inst_id,
       MAP (\i. i.inst_id)
         (ao_transform_inst mid dfg ra bb.bb_label idx targets inst)))
      bb.bb_instructions
End

Triviality block_pieces_fst[local]:
  !mid dfg ra targets bb.
    MAP FST (block_pieces mid dfg ra targets bb) =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[block_pieces_def] >>
  qspecl_then [`bb.bb_instructions`,
    `\idx inst. MAP (\i. i.inst_id)
       (ao_transform_inst mid dfg ra bb.bb_label idx targets inst)`,
    `\i. i.inst_id`] mp_tac map_fst_mapi_pair >>
  simp[]
QED

(* ao_resolve_phis_block (the PHI post-pass in ao_transform_block) only
   rewrites PHI operands, so it preserves every instruction's id. *)
Triviality ao_resolve_phis_block_inst_ids[local]:
  MAP (\i. i.inst_id) (ao_resolve_phis_block targets bb).bb_instructions =
  MAP (\i. i.inst_id) bb.bb_instructions
Proof
  simp[ao_resolve_phis_block_def, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rw[ao_resolve_iszero_inst_def]
QED

Triviality block_pieces_snd_flat[local]:
  !mid dfg ra targets bb.
    FLAT (MAP SND (block_pieces mid dfg ra targets bb)) =
    MAP (\i. i.inst_id)
      (ao_transform_block mid dfg ra targets bb).bb_instructions
Proof
  rw[block_pieces_def] >>
  simp[ao_transform_block_def, ao_resolve_phis_block_inst_ids] >>
  qspecl_then [`bb.bb_instructions`,
    `\idx inst. MAP (\i. i.inst_id)
       (ao_transform_inst mid dfg ra bb.bb_label idx targets inst)`,
    `\i. i.inst_id`] mp_tac map_snd_mapi_pair >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [`bb.bb_instructions`, `\i. i.inst_id`,
    `\idx inst. ao_transform_inst mid dfg ra bb.bb_label idx targets inst`]
    mp_tac map_flat_mapi >>
  simp[]
QED

Definition all_pieces_def:
  all_pieces mid dfg ra targets fn =
    FLAT (MAP (block_pieces mid dfg ra targets) fn.fn_blocks)
End

Triviality all_pieces_fst[local]:
  !mid dfg ra targets fn.
    MAP FST (all_pieces mid dfg ra targets fn) =
    MAP (\i. i.inst_id) (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[all_pieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def, block_pieces_fst]
QED

Triviality all_pieces_snd_flat[local]:
  !mid dfg ra targets fn.
    FLAT (MAP SND (all_pieces mid dfg ra targets fn)) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id)
      (ao_transform_block mid dfg ra targets bb).bb_instructions) fn.fn_blocks)
Proof
  rpt gen_tac >>
  simp[all_pieces_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[block_pieces_snd_flat]
QED

(* mem_fn_insts_blocks shared from passSimulationProps *)

Triviality all_pieces_idok[local]:
  !mid dfg ra targets fn.
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid) ==>
    EVERY (\p. idok mid (FST p) (SND p)) (all_pieces mid dfg ra targets fn)
Proof
  rw[all_pieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_pieces_def, indexedListsTheory.MEM_MAPi] >>
  irule transform_inst_idok >>
  first_x_assum irule >>
  simp[fn_insts_def] >>
  irule mem_fn_insts_blocks >>
  qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
  simp[listTheory.MEM_EL] >> metis_tac[]
QED

(* ===== top-level ===== *)

Triviality all_distinct_le_split[local]:
  !(l:num list) mid.
    ALL_DISTINCT (FILTER (\id. id <= mid) l) /\
    ALL_DISTINCT (FILTER (\id. ~(id <= mid)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h <= mid` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  qexists_tac `mid` >> simp[] >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Triviality map_inst_id_fn_insts[local]:
  !fn. MAP (\i. i.inst_id) (fn_insts fn) =
       FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)
Proof
  gen_tac >> simp[fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality pieces_all_distinct[local]:
  !mid pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. idok mid (FST p) (SND p)) pieces ==>
    ALL_DISTINCT (FLAT (MAP SND pieces))
Proof
  rpt strip_tac >>
  `FILTER (\id. id <= mid) (FLAT (MAP SND pieces)) = MAP FST pieces` by
    (irule pieces_le >> rpt conj_tac >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (FILTER (\id. ~(id <= mid)) (FLAT (MAP SND pieces)))` by
    (irule pieces_gt >> asm_rewrite_tac[]) >>
  irule all_distinct_le_split >> qexists_tac `mid` >>
  asm_rewrite_tac[]
QED

Theorem ao_phase3_inst_ids_distinct:
  !mid dfg ra targets fn.
    fn_inst_ids_distinct fn /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid) ==>
    fn_inst_ids_distinct
      (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >>
  simp[fn_inst_ids_distinct_def, function_map_transform_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  qspecl_then [`mid`, `dfg`, `ra`, `targets`, `fn`] mp_tac all_pieces_snd_flat >>
  disch_then (SUBST1_TAC o SYM) >>
  qspecl_then [`mid`, `all_pieces mid dfg ra targets fn`]
    mp_tac pieces_all_distinct >>
  impl_tac
  >- (conj_tac
      >- (simp[all_pieces_fst, map_inst_id_fn_insts] >>
          fs[fn_inst_ids_distinct_def])
      >- metis_tac[all_pieces_idok]) >>
  disch_then ACCEPT_TAC
QED

val _ = export_theory();
