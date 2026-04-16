(*
 * Memmerging — Well-formedness Preservation (Proofs)
 *
 * All proof infrastructure for bb_well_formed / wf_function preservation.
 * Re-exported by mmWfScript.sml.
 *)

Theory mmWfProofs
Ancestors
  mmCorrectnessProofs mmTransform
  venomExecSemantics venomInst venomState venomWf venomInstProofs
  pred_set finite_map list rich_list arithmetic words alist
  mmCopyEquiv mmCopy mmScan passSharedField
  dfgAnalysisProps dfgDefs passSimulationDefs passSimulationProps

(* ===== Structural helpers for wf preservation ===== *)

(* General: LAST of FLAT MAP when last element maps to singleton *)
Theorem last_flat_map_singleton[local]:
  !f l. l <> [] /\ (!x. f x <> []) /\ f (LAST l) = [LAST l] ==>
        LAST (FLAT (MAP f l)) = LAST l
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l = []`
  >- (gvs[LAST_DEF] >> Cases_on `f h` >> fs[])
  >> gvs[LAST_DEF] >>
     `FLAT (MAP f l) <> []` by
       (Cases_on `l` >> fs[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
        metis_tac[list_CASES, NOT_NIL_CONS]) >>
     simp[LAST_APPEND_NOT_NIL]
QED

(* General: FLAT MAP preserves non-empty when all elements map to non-empty *)
Theorem flat_map_nonempty[local]:
  !f l. l <> [] /\ (!x. f x <> []) ==> FLAT (MAP f l) <> []
Proof
  Cases_on `l` >> simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> Cases_on `f h` >> fs[]
QED

(* ===== FLAT MAP well-formedness toolkit ===== *)

(* General: FLAT (MAP f insts) preserves bb_well_formed when f satisfies:
   1. f maps each inst to a non-empty list
   2. f maps the terminator (LAST) to [same_terminator]
   3. f maps non-terminators to lists of non-terminators
   4. f maps PHIs to lists of PHIs, non-PHIs to lists of non-PHIs *)
(* Helper: EL in FLAT (MAP f l) corresponds to some EL in f (EL k l) *)
Theorem el_flat_map_decompose[local]:
  !f l i. i < LENGTH (FLAT (MAP f l)) ==>
    ?k j. k < LENGTH l /\ j < LENGTH (f (EL k l)) /\
          EL i (FLAT (MAP f l)) = EL j (f (EL k l))
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `i < LENGTH (f h)`
  >- (qexistsl_tac [`0`, `i`] >> simp[EL_APPEND1])
  >> `i - LENGTH (f h) < LENGTH (FLAT (MAP f l))` by
       (fs[LENGTH_FLAT, MAP_MAP_o, NOT_LESS] >>
        fs[LENGTH_APPEND]) >>
     first_x_assum drule >> strip_tac >>
     qexistsl_tac [`SUC k`, `j`] >>
     simp[EL_APPEND2]
QED

(*  FLAT (MAP f insts) = FLAT (MAP f (FRONT insts)) ++ f (LAST insts) *)
Theorem flat_map_front_last[local]:
  !f l. l <> [] ==>
    FLAT (MAP f l) = FLAT (MAP f (FRONT l)) ++ f (LAST l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l` >> simp[FRONT_DEF, LAST_DEF]
QED

(* Every element of FRONT l satisfies P when only the last of l doesn't *)
Theorem every_front[local]:
  !(P:'a -> bool) l. l <> [] /\
    (!k. k < LENGTH l /\ ~P (EL k l) ==> k = PRE (LENGTH l))
    ==> EVERY P (FRONT l)
Proof
  rpt strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH l` by
    (Cases_on `l` >> gvs[LENGTH_FRONT_CONS]) >>
  `EL n (FRONT l) = EL n l` by
    (irule EL_FRONT >> simp[NULL_EQ]) >>
  gvs[] >> CCONTR_TAC >> gvs[] >>
  `n = PRE (LENGTH l)` by metis_tac[] >>
  Cases_on `l` >> gvs[LENGTH_FRONT_CONS]
QED

(* PHI prefix preserved by FLAT MAP when f preserves PHI/non-PHI *)
Theorem flat_map_phi_prefix[local]:
  !f l i j.
    (!x. MEM x l /\ x.inst_opcode = PHI ==>
      EVERY (\y. y.inst_opcode = PHI) (f x)) /\
    (!x. MEM x l /\ x.inst_opcode <> PHI ==>
      EVERY (\y. y.inst_opcode <> PHI) (f x)) /\
    (!p q. p < q /\ q < LENGTH l /\ (EL q l).inst_opcode = PHI ==>
      (EL p l).inst_opcode = PHI) /\
    i < j /\ j < LENGTH (FLAT (MAP f l)) /\
    (EL j (FLAT (MAP f l))).inst_opcode = PHI
    ==>
    (EL i (FLAT (MAP f l))).inst_opcode = PHI
Proof
  gen_tac >> Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `j < LENGTH (f h)`
  >- (* j in f h, so i also in f h. h must be PHI. *)
     (`i < LENGTH (f h)` by simp[] >>
      Cases_on `h.inst_opcode = PHI`
      >- (fs[EVERY_EL, EL_APPEND1] >> metis_tac[MEM])
      >> fs[EVERY_EL, EL_APPEND1] >> metis_tac[MEM])
  >> Cases_on `i < LENGTH (f h)`
  >- (* i in f h, j in FLAT (MAP f l). h must be PHI. *)
     (`j - LENGTH (f h) < LENGTH (FLAT (MAP f l))` by
        (fs[NOT_LESS, LENGTH_APPEND]) >>
      drule el_flat_map_decompose >> strip_tac >>
      `(EL (j - LENGTH (f h)) (FLAT (MAP f l))).inst_opcode = PHI` by
        (fs[NOT_LESS] >> gvs[EL_APPEND2]) >>
      `(EL k l).inst_opcode = PHI` by
        (CCONTR_TAC >> `MEM (EL k l) l` by metis_tac[MEM_EL] >>
         `EVERY (\y. y.inst_opcode <> PHI) (f (EL k l))` by
           (first_x_assum irule >> simp[]) >>
         fs[EVERY_EL] >> first_x_assum (qspec_then `j'` mp_tac) >> gvs[]) >>
      `h.inst_opcode = PHI` by
        (first_x_assum (qspecl_then [`0`, `SUC k`] mp_tac) >> simp[]) >>
      `EVERY (\y. y.inst_opcode = PHI) (f h)` by
        (first_x_assum irule >> simp[]) >>
      fs[EVERY_EL, EL_APPEND1])
  >> (* both i and j in FLAT (MAP f l), apply IH *)
     (fs[NOT_LESS] >>
      `i - LENGTH (f h) < j - LENGTH (f h)` by simp[] >>
      `j - LENGTH (f h) < LENGTH (FLAT (MAP f l))` by
        (gvs[LENGTH_APPEND]) >>
      `(EL (j - LENGTH (f h)) (FLAT (MAP f l))).inst_opcode = PHI` by
        gvs[EL_APPEND2] >>
      `(EL (i - LENGTH (f h)) (FLAT (MAP f l))).inst_opcode = PHI` by
        (qpat_x_assum `!i' j'. _ /\ i' < j' /\ _ ==> _`
           (qspecl_then [`i - LENGTH (f h)`, `j - LENGTH (f h)`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> simp[] >>
           rpt strip_tac >>
           qpat_x_assum `!p q. p < q /\ q < SUC _ /\ _ ==> _`
             (qspecl_then [`SUC p`, `SUC q`] mp_tac) >> simp[]) >>
         simp[]) >>
      gvs[EL_APPEND2])
QED

(* Helper: EVERY distributes over FLAT MAP FRONT *)
Theorem every_flat_map_front[local]:
  !(P:'a -> bool) Q (f:'a -> 'a list) l.
    l <> [] /\ EVERY P (FRONT l) /\
    (!x. MEM x l /\ P x ==> EVERY Q (f x)) ==>
    EVERY Q (FLAT (MAP f (FRONT l)))
Proof
  rpt strip_tac >>
  simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  `MEM x l` by metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
  `P x` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY Q (f x)` by metis_tac[] >>
  fs[EVERY_MEM]
QED

(* Conjunct 3: only last is terminator in FLAT (MAP f l) *)
Theorem flat_map_only_last_terminator[local]:
  !f l i.
    l <> [] /\ (!x. f x <> []) /\
    (!x. MEM x l /\ ~is_terminator x.inst_opcode ==>
      EVERY (\y. ~is_terminator y.inst_opcode) (f x)) /\
    is_terminator (LAST l).inst_opcode /\
    (!k. k < LENGTH l /\ is_terminator (EL k l).inst_opcode ==>
      k = PRE (LENGTH l)) /\
    f (LAST l) = [LAST l] /\
    i < LENGTH (FLAT (MAP f l)) /\
    is_terminator (EL i (FLAT (MAP f l))).inst_opcode
    ==>
    i = PRE (LENGTH (FLAT (MAP f l)))
Proof
  Induct_on `l` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `l`
  >- (
    (* Base: l = [], so list is [h]. f(h) = [h], trivial *)
    gvs[LAST_DEF] >> simp[]
  ) >>
  (* Step: l = h'::t, list is h::(h'::t) *)
  rename [`h::(h'::t)`] >>
  Cases_on `is_terminator h.inst_opcode`
  >- (
    (* h is terminator => h must be LAST, but LAST is h'::t's last. Contradiction:
       only-last-terminator says k=PRE(LENGTH(h::h'::t)) but h is at k=0 *)
    first_x_assum (qspecl_then [`0`] mp_tac) >> simp[]
  ) >>
  (* h is not terminator, so f(h) is all non-terminators *)
  `EVERY (\y. ~is_terminator y.inst_opcode) (f h)` by metis_tac[MEM] >>
  (* i must be >= LENGTH (f h), otherwise EL i is in f(h) which is non-terminator *)
  Cases_on `i < LENGTH (f h)`
  >- (
    fs[EL_APPEND1] >>
    `~is_terminator (EL i (f h)).inst_opcode` by (fs[EVERY_EL] >> res_tac) >>
    metis_tac[]
  ) >>
  fs[NOT_LESS] >>
  `i - LENGTH (f h) < LENGTH (FLAT (MAP f (h'::t)))` by
    fs[LENGTH_APPEND] >>
  `EL i (f h ++ FLAT (MAP f (h'::t))) =
   EL (i - LENGTH (f h)) (FLAT (MAP f (h'::t)))` by
    simp[EL_APPEND2] >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`f`, `i - LENGTH (f h)`] mp_tac) >>
  impl_tac
  >- (
    rpt conj_tac >> simp[] >> rpt strip_tac
    >- metis_tac[MEM]
    >- (gvs[LAST_CONS])
    >- (first_x_assum (qspecl_then [`SUC k`] mp_tac) >> simp[])
    >- (gvs[LAST_CONS])
  ) >>
  simp[LENGTH_APPEND]
QED

Theorem flat_map_bb_well_formed[local]:
  !f bb.
    bb_well_formed bb /\
    (!inst. f inst <> []) /\
    (is_terminator (LAST bb.bb_instructions).inst_opcode ==>
      f (LAST bb.bb_instructions) = [LAST bb.bb_instructions]) /\
    (!inst. MEM inst bb.bb_instructions /\
            ~is_terminator inst.inst_opcode ==>
      EVERY (\i. ~is_terminator i.inst_opcode) (f inst)) /\
    (!inst. MEM inst bb.bb_instructions /\
            inst.inst_opcode = PHI ==>
      EVERY (\i. i.inst_opcode = PHI) (f inst)) /\
    (!inst. MEM inst bb.bb_instructions /\
            inst.inst_opcode <> PHI ==>
      EVERY (\i. i.inst_opcode <> PHI) (f inst))
    ==>
    bb_well_formed (bb with bb_instructions := FLAT (MAP f bb.bb_instructions))
Proof
  rpt strip_tac >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  fs[bb_well_formed_def] >>
  rpt conj_tac
  (* 1. Non-empty *)
  >- (irule flat_map_nonempty >> simp[])
  (* 2. LAST is terminator *)
  >- (drule last_flat_map_singleton >> simp[])
  (* 3. Only last is terminator *)
  >- (rpt strip_tac >>
      irule flat_map_only_last_terminator >> simp[] >> metis_tac[])
  (* 4. PHI prefix *)
  >> (rpt strip_tac >>
      irule flat_map_phi_prefix >> simp[] >> metis_tac[])
QED


(* General: bb_succs depends only on LAST when non-empty *)
Theorem bb_succs_same_last[local]:
  !bb insts. bb.bb_instructions <> [] /\ insts <> [] /\
    LAST insts = LAST bb.bb_instructions ==>
    bb_succs (bb with bb_instructions := insts) = bb_succs bb
Proof
  rpt strip_tac >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  Cases_on `insts` >> fs[]
QED

Theorem bb_succs_same_last_general[local]:
  !bb1 bb2. bb1.bb_instructions <> [] /\ bb2.bb_instructions <> [] /\
    LAST bb1.bb_instructions = LAST bb2.bb_instructions ==>
    bb_succs bb1 = bb_succs bb2
Proof
  rpt strip_tac >> simp[bb_succs_def] >>
  Cases_on `bb1.bb_instructions` >> Cases_on `bb2.bb_instructions` >> fs[]
QED

(* ===== Scan ID tracking: IDs in scan results come from fn_insts ===== *)

(* find_dload_mstore_pair results come from DLOAD instructions *)
Theorem find_dload_pair_dload_id[local]:
  !dfg inst dp. find_dload_mstore_pair dfg inst = SOME dp ==>
    dp.dp_dload_id = inst.inst_id /\ inst.inst_opcode = DLOAD
Proof
  rpt strip_tac >> gvs[find_dload_mstore_pair_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED

(* find_dload_mstore_pair: dp_mstore_id comes from dfg_get_uses *)
Theorem find_dload_pair_mstore_in_uses[local]:
  !dfg inst dp. find_dload_mstore_pair dfg inst = SOME dp ==>
    ?use_inst out_var. dfg_get_uses dfg out_var = [use_inst] /\
      use_inst.inst_opcode = MSTORE /\ dp.dp_mstore_id = use_inst.inst_id
Proof
  rw[find_dload_mstore_pair_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* apply_groups_inst/apply_memzero_inst identity when not in nop_set/rep_map *)
Theorem apply_groups_inst_identity[local]:
  !mode nop_set rep_map inst.
    ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = NONE ==>
    apply_groups_inst mode nop_set rep_map inst = [inst]
Proof
  simp[apply_groups_inst_def]
QED

Theorem apply_memzero_inst_identity[local]:
  !nop_set rep_map inst.
    ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = NONE ==>
    apply_memzero_inst nop_set rep_map inst = [inst]
Proof
  simp[apply_memzero_inst_def]
QED

(* ===== Non-terminator bridge lemmas ===== *)

Theorem is_zero_store_not_term[local]:
  !inst. is_zero_store inst ==> ~is_terminator inst.inst_opcode
Proof rw[is_zero_store_def] >> EVAL_TAC
QED

Theorem is_cds_copy_not_term[local]:
  !dfg inst. is_calldatasize_copy dfg inst ==> ~is_terminator inst.inst_opcode
Proof rw[is_calldatasize_copy_def] >> EVAL_TAC
QED

Theorem mode_load_not_term[local]:
  !mode. ~is_terminator (mode_load_opcode mode)
Proof Cases >> EVAL_TAC
QED

Theorem mode_copy_not_term[local]:
  !mode. ~is_terminator (mode_copy_opcode mode)
Proof Cases >> EVAL_TAC
QED

Theorem mstore_not_term[local]:
  ~is_terminator MSTORE
Proof EVAL_TAC
QED

Theorem terminator_no_outputs[local]:
  !inst. inst_wf inst /\ is_terminator inst.inst_opcode ==> inst.inst_outputs = []
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* IDs in sort_ids_by_block come from the input ids list *)
Theorem sort_ids_by_block_mem[local]:
  !insts ids x. MEM x (sort_ids_by_block insts ids) ==> MEM x ids
Proof
  rw[sort_ids_by_block_def, LET_THM, MEM_FILTER]
QED

(* IDs in nop_ids_of_group come from cg_inst_ids *)
Theorem nop_ids_of_group_subset[local]:
  !dfg mode insts cg.
    set (nop_ids_of_group dfg mode insts cg) SUBSET set cg.cg_inst_ids
Proof
  rw[nop_ids_of_group_def, LET_THM, SUBSET_DEF] >>
  Cases_on `REVERSE (sort_ids_by_block insts cg.cg_inst_ids)` >> simp[] >>
  rpt strip_tac >> fs[MEM_FILTER, MEM_REVERSE] >>
  metis_tac[sort_ids_by_block_mem, MEM, MEM_REVERSE]
QED

(* IDs in nop_ids_of_groups come from cg_inst_ids of some group *)
Theorem nop_ids_mem[local]:
  !dfg mode insts groups id.
    MEM id (nop_ids_of_groups dfg mode insts groups) ==>
    ?cg. MEM cg groups /\ MEM id cg.cg_inst_ids
Proof
  rw[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `y` >> simp[] >>
  metis_tac[nop_ids_of_group_subset, SUBSET_DEF]
QED

(* IDs in rep_map_of_groups come from cg_inst_ids of some group *)
Theorem rep_map_mem[local]:
  !insts groups id cg.
    ALOOKUP (rep_map_of_groups insts groups) id = SOME cg ==>
    ?cg'. MEM cg' groups /\ MEM id cg'.cg_inst_ids
Proof
  rw[rep_map_of_groups_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP, MEM_FILTER] >>
  Cases_on `rep_of_group insts y'` >> gvs[] >>
  fs[rep_of_group_def, LET_THM] >>
  Cases_on `REVERSE (sort_ids_by_block insts y'.cg_inst_ids)` >> gvs[] >>
  metis_tac[sort_ids_by_block_mem, MEM_REVERSE, MEM]
QED

(* ===== ALL_DISTINCT injectivity helper ===== *)

Theorem all_distinct_map_neq[local]:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\
             x <> y ==> f x <> f y
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  `n < LENGTH (MAP f l) /\ n' < LENGTH (MAP f l)` by simp[] >>
  `EL n (MAP f l) = EL n' (MAP f l)` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* fn_insts_blocks ID map = FLAT of per-block ID maps *)
Theorem fn_insts_blocks_map_id[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* fn_inst_ids_distinct: same inst_id implies same instruction *)
Theorem fn_inst_ids_distinct_inj[local]:
  !fn x y. fn_inst_ids_distinct fn /\ MEM x (fn_insts fn) /\
            MEM y (fn_insts fn) /\ x.inst_id = y.inst_id ==> x = y
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))`
    by fs[fn_inst_ids_distinct_def, GSYM fn_insts_blocks_map_id] >>
  fs[fn_insts_def] >> gvs[MEM_EL] >>
  `n < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) /\
   n' < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[] >>
  `EL n (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) =
   EL n' (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

(* ===== Scan invariant: all IDs in scan results trace to fn_insts ===== *)

(* Helper: merge_adjacent preserves the set of all cg_inst_ids *)
Theorem merge_adjacent_ids[local]:
  !copies id. (?cg. MEM cg (merge_adjacent copies) /\ MEM id cg.cg_inst_ids) <=>
              (?cg. MEM cg copies /\ MEM id cg.cg_inst_ids)
Proof
  ho_match_mp_tac merge_adjacent_ind >> rw[]
  >- simp[merge_adjacent_def]
  >- simp[merge_adjacent_def]
  >> simp[Once merge_adjacent_def] >>
  IF_CASES_TAC >> simp[]
  >- (
    (* merge case *)
    EQ_TAC >> rpt strip_tac >> gvs[]
    >- (
      (* -> : cg = copy_merge c1 c2 *)
      gvs[copy_merge_def, MEM_APPEND] >> metis_tac[])
    >- (
      (* -> : MEM cg rest, use IH *)
      `?cg'. (cg' = copy_merge c1 c2 \/ MEM cg' rest) /\ MEM id cg'.cg_inst_ids`
        by metis_tac[] >>
      gvs[copy_merge_def, MEM_APPEND] >> metis_tac[])
    >- (
      (* <- : cg = c1 *)
      `MEM id (copy_merge c1 c2).cg_inst_ids` by simp[copy_merge_def] >>
      metis_tac[])
    >- (
      (* <- : cg = c2 *)
      `MEM id (copy_merge c1 c2).cg_inst_ids` by simp[copy_merge_def] >>
      metis_tac[])
    >> (* <- : MEM cg rest *)
    metis_tac[])
  >> (* no merge case *)
  EQ_TAC >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Helper: insert_sorted preserves IDs + adds new_cg *)
Theorem insert_sorted_ids[local]:
  !copies new_cg id.
    (?cg. MEM cg (insert_sorted copies new_cg) /\ MEM id cg.cg_inst_ids) <=>
    MEM id new_cg.cg_inst_ids \/
    (?cg. MEM cg copies /\ MEM id cg.cg_inst_ids)
Proof
  Induct
  >- simp[insert_sorted_def]
  >> simp[insert_sorted_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[merge_adjacent_ids]
QED

(* add_copy preserves IDs + adds new_cg *)
Theorem add_copy_ids[local]:
  !copies new_cg id.
    (?cg. MEM cg (add_copy copies new_cg) /\ MEM id cg.cg_inst_ids) <=>
    MEM id new_cg.cg_inst_ids \/
    (?cg. MEM cg copies /\ MEM id cg.cg_inst_ids)
Proof
  simp[add_copy_def, merge_adjacent_ids, insert_sorted_ids]
QED

(* flush_copies preserves the total set of IDs (copies + flushed) *)
Theorem flush_copies_ids[local]:
  !ss to_flush id.
    (!cg. MEM cg to_flush ==> MEM cg ss.ss_copies) ==>
    (((?cg. MEM cg (flush_copies ss to_flush).ss_copies /\ MEM id cg.cg_inst_ids) \/
      (?cg. MEM cg (flush_copies ss to_flush).ss_flushed /\ MEM id cg.cg_inst_ids)) <=>
     ((?cg. MEM cg ss.ss_copies /\ MEM id cg.cg_inst_ids) \/
      (?cg. MEM cg ss.ss_flushed /\ MEM id cg.cg_inst_ids)))
Proof
  simp[flush_copies_def, MEM_FILTER, MEM_APPEND] >> rpt gen_tac >>
  disch_tac >> EQ_TAC >> rpt strip_tac >> gvs[] >>
  Cases_on `MEM cg to_flush` >> gvs[] >> metis_tac[]
QED

(* hard_barrier preserves total IDs *)
Theorem hard_barrier_ids[local]:
  !ss id.
    ((?cg. MEM cg (hard_barrier ss).ss_copies /\ MEM id cg.cg_inst_ids) \/
     (?cg. MEM cg (hard_barrier ss).ss_flushed /\ MEM id cg.cg_inst_ids)) <=>
    ((?cg. MEM cg ss.ss_copies /\ MEM id cg.cg_inst_ids) \/
     (?cg. MEM cg ss.ss_flushed /\ MEM id cg.cg_inst_ids))
Proof
  rw[hard_barrier_def] >> simp[] >>
  EQ_TAC >> rpt strip_tac >> gvs[MEM_APPEND] >> metis_tac[]
QED

(* Abbreviation for "id is in some group's cg_inst_ids in ss" *)
Definition scan_has_id_def:
  scan_has_id ss id <=>
    (?cg. MEM cg ss.ss_copies /\ MEM id cg.cg_inst_ids) \/
    (?cg. MEM cg ss.ss_flushed /\ MEM id cg.cg_inst_ids)
End

(* hard_barrier preserves scan_has_id *)
Theorem hard_barrier_has_id[local]:
  !ss id. scan_has_id (hard_barrier ss) id <=> scan_has_id ss id
Proof
  simp[scan_has_id_def, hard_barrier_ids]
QED

Theorem flush_copies_has_id[local]:
  !ss to_flush id.
    (!cg. MEM cg to_flush ==> MEM cg ss.ss_copies) ==>
    (scan_has_id (flush_copies ss to_flush) id <=> scan_has_id ss id)
Proof
  simp[scan_has_id_def, flush_copies_ids]
QED

Theorem hazard_subset_copies[local]:
  (!copies new_cg cg. MEM cg (waw_hazards copies new_cg) ==> MEM cg copies) /\
  (!copies new_cg cg. MEM cg (raw_hazards copies new_cg) ==> MEM cg copies) /\
  (!copies new_cg cg. MEM cg (war_hazards copies new_cg) ==> MEM cg copies) /\
  (!copies iv cg. MEM cg (copies_that_overwrite copies iv) ==> MEM cg copies)
Proof
  simp[waw_hazards_def, raw_hazards_def, war_hazards_def,
       copies_that_overwrite_def, MEM_FILTER]
QED

Theorem flush_copies_has_id_filter[local]:
  !ss f id.
    scan_has_id (flush_copies ss (FILTER f ss.ss_copies)) id <=> scan_has_id ss id
Proof
  rpt gen_tac >> simp[flush_copies_has_id, MEM_FILTER]
QED

Theorem flush_hazards_has_id[local]:
  !mode ss new_cg id.
    scan_has_id (flush_hazards mode ss new_cg) id <=> scan_has_id ss id
Proof
  rpt gen_tac >> simp[flush_hazards_def, LET_THM,
    waw_hazards_def, raw_hazards_def, war_hazards_def,
    copies_that_overwrite_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[flush_copies_has_id, MEM_FILTER]
QED

Theorem invalidate_loads_has_id[local]:
  !ss iv id. scan_has_id (invalidate_loads ss iv) id <=> scan_has_id ss id
Proof
  simp[scan_has_id_def, invalidate_loads_def]
QED

Theorem add_copy_has_id[local]:
  !copies new_cg id.
    (?cg. MEM cg (add_copy copies new_cg) /\ MEM id cg.cg_inst_ids) <=>
    MEM id new_cg.cg_inst_ids \/
    (?cg. MEM cg copies /\ MEM id cg.cg_inst_ids)
Proof
  simp[add_copy_ids]
QED

Theorem scan_has_id_loads_irrel[local]:
  !ss x id. scan_has_id (ss with ss_loads := x) id <=> scan_has_id ss id
Proof
  simp[scan_has_id_def]
QED

Theorem scan_load_has_id[local]:
  !mode ss inst id.
    scan_has_id (scan_load mode ss inst) id ==> scan_has_id ss id
Proof
  rpt gen_tac >> simp[scan_load_def, LET_THM] >>
  rpt (CASE_TAC >> simp[hard_barrier_has_id]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[scan_has_id_loads_irrel, flush_copies_has_id, MEM_FILTER,
       copies_that_overwrite_def]
QED


(* Bridge: scan_has_id after adding a copy group to ss_copies *)
Theorem scan_has_id_add_copy[local]:
  !ss new_cg id.
    scan_has_id (ss with ss_copies := add_copy ss.ss_copies new_cg) id <=>
    MEM id new_cg.cg_inst_ids \/ scan_has_id ss id
Proof
  simp[scan_has_id_def, add_copy_has_id] >> metis_tac[]
QED

Theorem scan_store_has_id[local]:
  !dfg mode ss inst id.
    scan_has_id (scan_store dfg mode ss inst) id ==>
    scan_has_id ss id \/
    inst.inst_id = id \/
    (?v li. dfg_get_def dfg v = SOME li /\ li.inst_id = id)
Proof
  rpt gen_tac >> simp[scan_store_def, LET_THM] >>
  rpt (CASE_TAC >> simp[hard_barrier_has_id]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[scan_has_id_add_copy, flush_hazards_has_id, invalidate_loads_has_id] >>
  strip_tac >> gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem scan_bulk_copy_has_id[local]:
  !mode ss inst id.
    scan_has_id (scan_bulk_copy mode ss inst) id ==>
    scan_has_id ss id \/ inst.inst_id = id
Proof
  rpt gen_tac >> simp[scan_bulk_copy_def, LET_THM] >>
  rpt (CASE_TAC >> simp[hard_barrier_has_id]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[scan_has_id_add_copy, flush_hazards_has_id, invalidate_loads_has_id] >>
  strip_tac >> gvs[]
QED

(* Per-step: scan_inst preserves scan_has_id or adds inst/dfg id *)
Theorem scan_inst_has_id[local]:
  !dfg mode ss inst id.
    scan_has_id (scan_inst dfg mode ss inst) id ==>
    scan_has_id ss id \/
    (inst.inst_id = id /\ ~is_terminator inst.inst_opcode) \/
    (?v li. dfg_get_def dfg v = SOME li /\ li.inst_id = id)
Proof
  rpt gen_tac >> simp[scan_inst_def] >>
  rpt IF_CASES_TAC >> gvs[] >> strip_tac >>
  imp_res_tac scan_load_has_id >>
  imp_res_tac scan_store_has_id >>
  imp_res_tac scan_bulk_copy_has_id >>
  gvs[hard_barrier_has_id] >>
  metis_tac[mstore_not_term, mode_copy_not_term, mode_load_not_term]
QED

(* FOLDL invariant for main scan: ids in scan result come from acc or instructions *)
Theorem scan_foldl_ids_inv[local]:
  !dfg mode insts ss id.
    scan_has_id (FOLDL (scan_inst dfg mode) ss insts) id ==>
    scan_has_id ss id \/
    (?inst. MEM inst insts /\ inst.inst_id = id /\
            ~is_terminator inst.inst_opcode) \/
    (?v li. dfg_get_def dfg v = SOME li /\ li.inst_id = id)
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  drule scan_inst_has_id >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* ===== ss_loads invariant: variables in ss_loads were loaded by
   mode_load_opcode instructions in the processed prefix ===== *)

(* scan_load: either adds load output or hard_barriers *)
Theorem scan_load_loads_inv[local]:
  !mode ss inst var.
    var IN FDOM (scan_load mode ss inst).ss_loads ==>
    var IN FDOM ss.ss_loads \/ MEM var inst.inst_outputs
Proof
  rpt gen_tac >> simp[scan_load_def, LET_THM] >>
  rpt (CASE_TAC >> simp[hard_barrier_def, FDOM_DRESTRICT,
       flush_copies_def, FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
  rpt (IF_CASES_TAC >> simp[flush_copies_def, FDOM_DRESTRICT,
       FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
  strip_tac >> gvs[FDOM_FUPDATE]
QED

(* Helper: flush_copies doesn't change ss_loads *)
Theorem flush_copies_loads[local]:
  !ss x. (flush_copies ss x).ss_loads = ss.ss_loads
Proof
  simp[flush_copies_def]
QED

(* Helper: flush_hazards doesn't change ss_loads *)
Theorem flush_hazards_loads[local]:
  !mode ss cg. (flush_hazards mode ss cg).ss_loads = ss.ss_loads
Proof
  rw[flush_hazards_def, LET_THM, flush_copies_def]
QED

(* Helper: invalidate_loads only removes from ss_loads *)
Theorem invalidate_loads_loads_sub[local]:
  !ss iv var.
    var IN FDOM (invalidate_loads ss iv).ss_loads ==>
    var IN FDOM ss.ss_loads
Proof
  simp[invalidate_loads_def, FDOM_DRESTRICT]
QED

(* scan_store: only removes from ss_loads or hard_barriers *)
Theorem scan_store_loads_inv[local]:
  !dfg mode ss inst var.
    var IN FDOM (scan_store dfg mode ss inst).ss_loads ==>
    var IN FDOM ss.ss_loads
Proof
  rpt gen_tac >> simp[scan_store_def, LET_THM] >>
  rpt CASE_TAC >> simp[hard_barrier_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[flush_hazards_loads, invalidate_loads_def, FDOM_DRESTRICT]
QED

(* scan_bulk_copy: only removes from ss_loads or hard_barriers *)
Theorem scan_bulk_copy_loads_inv[local]:
  !mode ss inst var.
    var IN FDOM (scan_bulk_copy mode ss inst).ss_loads ==>
    var IN FDOM ss.ss_loads
Proof
  rpt gen_tac >> simp[scan_bulk_copy_def, LET_THM] >>
  rpt CASE_TAC >> simp[hard_barrier_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[flush_hazards_loads, invalidate_loads_def, FDOM_DRESTRICT]
QED

(* scan_inst: ss_loads vars come from prior state or load instructions *)
Theorem scan_inst_loads_inv[local]:
  !dfg mode ss inst var.
    var IN FDOM (scan_inst dfg mode ss inst).ss_loads ==>
    var IN FDOM ss.ss_loads \/
    (inst.inst_opcode = mode_load_opcode mode /\ MEM var inst.inst_outputs)
Proof
  rpt gen_tac >> simp[scan_inst_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (strip_tac >> drule scan_load_loads_inv >> strip_tac >> gvs[] >>
       metis_tac[]) >>
  TRY (strip_tac >> drule scan_store_loads_inv >> metis_tac[]) >>
  TRY (strip_tac >> drule scan_bulk_copy_loads_inv >> metis_tac[]) >>
  simp[hard_barrier_def]
QED

(* FOLDL invariant: ss_loads vars come from mode_load_opcode instructions *)
Theorem scan_foldl_loads_inv[local]:
  !dfg mode insts ss var.
    var IN FDOM (FOLDL (scan_inst dfg mode) ss insts).ss_loads ==>
    var IN FDOM ss.ss_loads \/
    (?inst. MEM inst insts /\ inst.inst_opcode = mode_load_opcode mode /\
            MEM var inst.inst_outputs)
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  drule scan_inst_loads_inv >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* Per-step memzero helper *)
Definition memzero_has_id_def:
  memzero_has_id mz id <=>
    (?cg. MEM cg mz.mz_copies /\ MEM id cg.cg_inst_ids) \/
    (?cg. MEM cg mz.mz_flushed /\ MEM id cg.cg_inst_ids)
End

Theorem scan_inst_memzero_has_id[local]:
  !dfg mz inst id.
    memzero_has_id (scan_inst_memzero dfg mz inst) id ==>
    memzero_has_id mz id \/
    (inst.inst_id = id /\ ~is_terminator inst.inst_opcode)
Proof
  rpt gen_tac >> simp[scan_inst_memzero_def, memzero_has_id_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt (CASE_TAC >> gvs[memzero_barrier_def, MEM_APPEND]) >>
  gvs[add_copy_def] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac insert_sorted_ids >> gvs[copy_memzero_def] >>
       metis_tac[is_zero_store_not_term, is_cds_copy_not_term]) >>
  TRY (imp_res_tac merge_adjacent_ids >> gvs[] >>
       imp_res_tac insert_sorted_ids >> gvs[copy_memzero_def] >>
       metis_tac[is_zero_store_not_term, is_cds_copy_not_term]) >>
  gvs[memzero_barrier_def, MEM_APPEND] >> metis_tac[]
QED

(* Memzero scan invariant (simpler: no dfg_get_def).
   Strengthened: inst case includes ~is_terminator. *)
Theorem scan_memzero_foldl_ids_inv[local]:
  !dfg insts mz id.
    ((?cg. MEM cg (FOLDL (scan_inst_memzero dfg) mz insts).mz_copies /\
           MEM id cg.cg_inst_ids) \/
     (?cg. MEM cg (FOLDL (scan_inst_memzero dfg) mz insts).mz_flushed /\
           MEM id cg.cg_inst_ids)) ==>
    ((?cg. MEM cg mz.mz_copies /\ MEM id cg.cg_inst_ids) \/
     (?cg. MEM cg mz.mz_flushed /\ MEM id cg.cg_inst_ids)) \/
    (?inst. MEM inst insts /\ inst.inst_id = id /\
            ~is_terminator inst.inst_opcode)
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> disch_then assume_tac >>
  `memzero_has_id (FOLDL (scan_inst_memzero dfg)
     (scan_inst_memzero dfg mz h) insts) id`
    by (simp[memzero_has_id_def] >> metis_tac[]) >>
  first_x_assum drule >> simp[memzero_has_id_def] >>
  disch_then assume_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  `memzero_has_id (scan_inst_memzero dfg mz h) id`
    by (simp[memzero_has_id_def] >> metis_tac[]) >>
  drule scan_inst_memzero_has_id >>
  simp[memzero_has_id_def] >> metis_tac[]
QED

(* ===== Key bridge: terminator ID not in scan results ===== *)

(* fn_insts includes all block instructions *)
Theorem fn_insts_mem_block[local]:
  !fn bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rpt strip_tac >>
  simp[fn_insts_def] >>
  `!bbs. MEM bb bbs ==> MEM inst (fn_insts_blocks bbs)` suffices_by metis_tac[] >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[]
QED

(* Reverse direction: MEM in fn_insts implies MEM in some block *)
Theorem fn_insts_mem_block_rev[local]:
  !fn inst. MEM inst (fn_insts fn) ==>
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  rpt strip_tac >> gvs[fn_insts_def] >>
  `!bbs. MEM inst (fn_insts_blocks bbs) ==>
         ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions`
    suffices_by metis_tac[] >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* fn_inst_wf + MEM in fn_insts => inst_wf *)
Theorem fn_inst_wf_mem[local]:
  !fn inst. fn_inst_wf fn /\ MEM inst (fn_insts fn) ==> inst_wf inst
Proof
  rpt strip_tac >> imp_res_tac fn_insts_mem_block_rev >>
  fs[fn_inst_wf_def] >> metis_tac[]
QED

(* Terminators in fn_insts have no outputs *)
Theorem fn_inst_wf_terminator_no_outputs[local]:
  !fn inst.
    fn_inst_wf fn /\ MEM inst (fn_insts fn) /\
    is_terminator inst.inst_opcode ==>
    inst.inst_outputs = []
Proof
  rpt strip_tac >> imp_res_tac fn_inst_wf_mem >>
  imp_res_tac terminator_no_outputs >> gvs[]
QED

(* fn_inst_ids_distinct implies per-block ALL_DISTINCT *)
Theorem all_distinct_flat_imp[local]:
  !xss xs. ALL_DISTINCT (FLAT xss) /\ MEM xs xss ==> ALL_DISTINCT xs
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem fn_inst_ids_distinct_block[local]:
  !fn bb. fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[fn_inst_ids_distinct_def] >>
  drule_then (qspec_then `MAP (\i. i.inst_id) bb.bb_instructions` mp_tac)
    all_distinct_flat_imp >>
  impl_tac >- (simp[MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

(* General: MEM in MAP THE (FILTER IS_SOME (MAP f l)) gives SOME witness *)
Theorem mem_map_the_filter_some[local]:
  !f l x. MEM x (MAP THE (FILTER IS_SOME (MAP f l))) ==>
    ?y. MEM y l /\ f y = SOME x
Proof
  gen_tac >> Induct >> rw[] >>
  Cases_on `f h` >> gvs[] >> metis_tac[]
QED

(* Bridge: MEM in find_dload_pairs gives back the SOME witness *)
Theorem find_dload_pairs_mem[local]:
  !dfg insts dp.
    MEM dp (find_dload_pairs dfg insts) ==>
    ?inst. MEM inst insts /\ find_dload_mstore_pair dfg inst = SOME dp
Proof
  rw[find_dload_pairs_def] >> imp_res_tac mem_map_the_filter_some >> metis_tac[]
QED

(* Helper: every dp in find_dload_pairs has dp_mstore_id from an MSTORE in fn_insts *)
Theorem find_dload_pairs_mstore_ids[local]:
  !dfg fn bb dp.
    dfg = dfg_build_function fn /\
    MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
    ?mst. MEM mst (fn_insts fn) /\ mst.inst_opcode = MSTORE /\
          dp.dp_mstore_id = mst.inst_id
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac find_dload_pairs_mem >>
  imp_res_tac find_dload_pair_mstore_in_uses >>
  `MEM use_inst (dfg_get_uses (dfg_build_function fn) out_var)` by simp[] >>
  imp_res_tac dfg_build_function_uses_sound >>
  metis_tac[]
QED

(* Key: terminator ID not in dload_nops *)
Theorem term_id_not_in_dload_nops[local]:
  !dfg fn bb.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    let pairs = find_dload_pairs dfg bb.bb_instructions;
        dload_nops = MAP (\dp. dp.dp_dload_id) pairs
    in ~MEM (LAST bb.bb_instructions).inst_id dload_nops
Proof
  rw[LET_THM] >> SPOSE_NOT_THEN strip_assume_tac >>
  gvs[MEM_MAP] >>
  imp_res_tac find_dload_pairs_mem >>
  imp_res_tac find_dload_pair_dload_id >> gvs[] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `~is_terminator DLOAD` by EVAL_TAC >>
  `inst <> LAST bb.bb_instructions` by (strip_tac >> gvs[]) >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by (
    irule MEM_LAST_NOT_NIL >> fs[bb_well_formed_def]) >>
  imp_res_tac fn_inst_ids_distinct_block >>
  metis_tac[all_distinct_map_neq]
QED

(* Key: terminator ID not in dload mstore_map *)
Theorem term_id_not_in_mstore_map[local]:
  !fn bb.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    let dfg = dfg_build_function fn;
        pairs = find_dload_pairs dfg bb.bb_instructions;
        mstore_map = MAP (\dp. (dp.dp_mstore_id, dp)) pairs
    in ALOOKUP mstore_map (LAST bb.bb_instructions).inst_id = NONE
Proof
  rw[LET_THM] >> SPOSE_NOT_THEN strip_assume_tac >>
  qpat_x_assum `_ <> NONE` (mp_tac o REWRITE_RULE [ALOOKUP_NONE]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >> rpt strip_tac >>
  drule find_dload_pairs_mem >> strip_tac >>
  drule find_dload_pair_mstore_in_uses >> strip_tac >>
  `MEM use_inst (dfg_get_uses (dfg_build_function fn) out_var)` by simp[] >>
  drule dfg_build_function_uses_sound >> strip_tac >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `~is_terminator MSTORE` by EVAL_TAC >>
  `MEM (LAST bb.bb_instructions) (fn_insts fn)` by (
    irule fn_insts_mem_block >> fs[bb_well_formed_def] >>
    metis_tac[MEM_LAST_NOT_NIL]) >>
  `(LAST bb.bb_instructions).inst_id = use_inst.inst_id` by gvs[] >>
  metis_tac[fn_inst_ids_distinct_inj]
QED

(* ALL_DISTINCT (MAP f xs) implies f-injectivity on xs *)
Theorem all_distinct_map_inv[local]:
  !f xs a b. ALL_DISTINCT (MAP f xs) /\ MEM a xs /\ MEM b xs /\
             f a = f b ==> a = b
Proof
  Induct_on `xs` >> rw[MEM_MAP, ALL_DISTINCT] >> gvs[MEM_MAP] >>
  metis_tac[]
QED

(* PHI ID not in dload_nops: PHI opcode ≠ DLOAD *)
Theorem phi_id_not_in_dload_nops[local]:
  !dfg fn bb inst.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    ~MEM inst.inst_id
      (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions))
Proof
  rpt strip_tac >> gvs[MEM_MAP] >>
  imp_res_tac find_dload_pairs_mem >>
  imp_res_tac find_dload_pair_dload_id >> gvs[] >>
  imp_res_tac fn_inst_ids_distinct_block >>
  `inst' = inst` by metis_tac[all_distinct_map_inv] >> gvs[]
QED

(* PHI ID not in mstore_map: PHI opcode ≠ MSTORE *)
Theorem phi_id_not_in_mstore_map[local]:
  !fn bb phi_inst.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI ==>
    ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
      (find_dload_pairs (dfg_build_function fn) bb.bb_instructions))
      phi_inst.inst_id = NONE
Proof
  rpt strip_tac >> SPOSE_NOT_THEN strip_assume_tac >>
  qpat_x_assum `_ <> NONE` (mp_tac o REWRITE_RULE [ALOOKUP_NONE]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >> rpt strip_tac >>
  drule find_dload_pairs_mem >> strip_tac >>
  drule find_dload_pair_mstore_in_uses >> strip_tac >>
  `MEM use_inst (dfg_get_uses (dfg_build_function fn) out_var)` by simp[] >>
  drule dfg_build_function_uses_sound >> strip_tac >>
  `MEM phi_inst (fn_insts fn)` by (
    irule fn_insts_mem_block >> metis_tac[]) >>
  `phi_inst.inst_id = use_inst.inst_id` by gvs[] >>
  `phi_inst = use_inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[]
QED

(* scan_block result groups have IDs from non-terminator fn_insts *)
Theorem scan_block_ids_from_fn[local]:
  !dfg mode fn bb cg id.
    dfg = dfg_build_function fn /\
    MEM cg (scan_block dfg mode bb).ss_flushed /\
    MEM id cg.cg_inst_ids ==>
    (?inst. MEM inst bb.bb_instructions /\ inst.inst_id = id /\
            ~is_terminator inst.inst_opcode) \/
    (?inst v. MEM inst (fn_insts fn) /\ inst.inst_id = id /\
              MEM v inst.inst_outputs)
Proof
  rpt strip_tac >> gvs[scan_block_def, LET_THM] >>
  `scan_has_id (hard_barrier (FOLDL (scan_inst (dfg_build_function fn) mode)
    empty_scan_state bb.bb_instructions)) id` by (
    fs[scan_has_id_def, hard_barrier_def, MEM_APPEND] >>
    metis_tac[]) >>
  gvs[hard_barrier_has_id] >>
  drule scan_foldl_ids_inv >> strip_tac
  >- gvs[scan_has_id_def, empty_scan_state_def]
  >- metis_tac[]
  >> imp_res_tac dfg_build_function_correct >> metis_tac[]
QED

(* scan_block_memzero result groups have IDs from non-terminator bb insts *)
Theorem scan_block_memzero_ids_from_bb[local]:
  !dfg bb cg id.
    MEM cg (scan_block_memzero dfg bb).mz_flushed /\
    MEM id cg.cg_inst_ids ==>
    ?inst. MEM inst bb.bb_instructions /\ inst.inst_id = id /\
           ~is_terminator inst.inst_opcode
Proof
  rw[scan_block_memzero_def, LET_THM] >>
  gvs[memzero_barrier_def, MEM_APPEND] >>
  mp_tac (Q.SPECL [`dfg`, `bb.bb_instructions`,
    `empty_memzero_state`, `id`] scan_memzero_foldl_ids_inv) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> gvs[empty_memzero_state_def] >> metis_tac[]
QED

(* Shared contradiction: non-terminator inst with terminator's ID in distinct list *)
Theorem term_id_contradiction[local]:
  !insts inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    MEM inst insts /\
    inst.inst_id = (LAST insts).inst_id /\
    ~is_terminator inst.inst_opcode ==> F
Proof
  rpt strip_tac >>
  `MEM (LAST insts) insts` by metis_tac[MEM_LAST_NOT_NIL] >>
  `inst = LAST insts` by (
    CCONTR_TAC >> imp_res_tac all_distinct_map_neq >> gvs[]) >>
  gvs[]
QED

(* Shared contradiction: dfg inst with terminator's ID in wf function *)
Theorem term_id_dfg_contradiction[local]:
  !fn bb inst v.
    fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    MEM inst (fn_insts fn) /\
    inst.inst_id = (LAST bb.bb_instructions).inst_id /\
    MEM v inst.inst_outputs ==> F
Proof
  rpt strip_tac >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `MEM (LAST bb.bb_instructions) (fn_insts fn)` by
    (irule fn_insts_mem_block >> fs[bb_well_formed_def] >>
     metis_tac[MEM_LAST_NOT_NIL]) >>
  `inst = LAST bb.bb_instructions` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions`
    by metis_tac[MEM_LAST_NOT_NIL] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (fs[fn_inst_wf_def] >> metis_tac[]) >>
  imp_res_tac terminator_no_outputs >> gvs[]
QED

(* ===== Sub-transform LAST preservation via term_unique ===== *)

(* All outputs of apply_memzero_inst preserve inst_id *)
Theorem apply_memzero_ids[local]:
  !nop_set rep_map inst inst'.
    MEM inst' (apply_memzero_inst nop_set rep_map inst) ==>
    inst'.inst_id = inst.inst_id
Proof
  rw[apply_memzero_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  BasicProvers.every_case_tac >> gvs[mk_zero_store_inst_def,
    mk_calldatasize_inst_def, mk_memzero_calldatacopy_def]
QED

(* All outputs of apply_groups_inst preserve inst_id *)
Theorem apply_groups_ids[local]:
  !mode nop_set rep_map inst inst'.
    MEM inst' (apply_groups_inst mode nop_set rep_map inst) ==>
    inst'.inst_id = inst.inst_id
Proof
  rw[apply_groups_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  BasicProvers.every_case_tac >> gvs[mk_bulk_copy_inst_def,
    mk_load_inst_def, mk_mstore_from_load_def]
QED

(* Weakened term_id_contradiction: uses uniqueness instead of ALL_DISTINCT *)
Theorem term_unique_contradiction[local]:
  !insts inst term.
    LAST insts = term /\
    (!i. MEM i insts /\ i.inst_id = term.inst_id ==> i = term) /\
    MEM inst insts /\
    inst.inst_id = term.inst_id /\
    ~is_terminator inst.inst_opcode /\
    is_terminator term.inst_opcode ==> F
Proof
  metis_tac[]
QED

(* ALL_DISTINCT implies terminator ID uniqueness *)
Theorem all_distinct_term_unique[local]:
  !insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    insts <> [] ==>
    !i. MEM i insts /\ i.inst_id = (LAST insts).inst_id ==> i = LAST insts
Proof
  rpt strip_tac >>
  `MEM (LAST insts) insts` by metis_tac[MEM_LAST_NOT_NIL] >>
  CCONTR_TAC >> imp_res_tac all_distinct_map_neq >> gvs[]
QED

(* Weakened memzero scan: terminator ID not in scan results *)
Theorem term_id_not_in_memzero_scan_weak[local]:
  !dfg bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) ==>
    let scan_result = scan_block_memzero dfg bb;
        groups = scan_result.mz_flushed;
        nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups;
        rep_map = rep_map_of_groups bb.bb_instructions groups
    in ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
       ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE
Proof
  rw[LET_THM] >> rpt conj_tac
  >- (strip_tac >> imp_res_tac nop_ids_mem >>
      drule scan_block_memzero_ids_from_bb >> disch_then drule >> strip_tac >>
      metis_tac[term_unique_contradiction])
  >> (qmatch_goalsub_abbrev_tac `ALOOKUP rm key = NONE` >>
      Cases_on `ALOOKUP rm key` >> simp[] >>
      gvs[Abbr `rm`, Abbr `key`] >>
      imp_res_tac rep_map_mem >>
      drule scan_block_memzero_ids_from_bb >> disch_then drule >> strip_tac >>
      metis_tac[term_unique_contradiction])
QED

(* Weakened mode scan: terminator ID not in scan results *)
(* Core lemma: scan group IDs never include the terminator's ID *)
Theorem scan_group_id_not_terminator[local]:
  !dfg fn bb mode cg id.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    MEM (LAST bb.bb_instructions) (fn_insts fn) /\
    MEM cg (scan_block dfg mode bb).ss_flushed /\
    MEM id cg.cg_inst_ids ==>
    id <> (LAST bb.bb_instructions).inst_id
Proof
  rpt strip_tac >>
  drule_all scan_block_ids_from_fn >> strip_tac
  >- metis_tac[term_unique_contradiction]
  >> (`inst = LAST bb.bb_instructions`
        by metis_tac[fn_inst_ids_distinct_inj] >>
      gvs[] >> imp_res_tac fn_inst_wf_terminator_no_outputs >> gvs[])
QED

Theorem term_id_not_in_mode_scan_weak[local]:
  !dfg fn bb mode.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    MEM (LAST bb.bb_instructions) (fn_insts fn) ==>
    let scan_result = scan_block dfg mode bb;
        groups = scan_result.ss_flushed;
        nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups;
        rep_map = rep_map_of_groups bb.bb_instructions groups
    in ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
       ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE
Proof
  rpt gen_tac >> strip_tac >>
  CONV_TAC (SIMP_CONV (srw_ss()) [LET_THM]) >>
  rpt conj_tac
  >- (
    strip_tac >> imp_res_tac nop_ids_mem >>
    metis_tac[scan_group_id_not_terminator])
  >> (
    qmatch_goalsub_abbrev_tac `ALOOKUP rm key = NONE` >>
    Cases_on `ALOOKUP rm key` >> simp[] >>
    gvs[Abbr `rm`, Abbr `key`] >>
    imp_res_tac rep_map_mem >>
    metis_tac[scan_group_id_not_terminator])
QED

(* FLAT MAP preserves "term_unique" when f preserves inst_id.
   Decomposed into three independent claims for efficiency. *)
Theorem flat_map_term_unique[local]:
  !f insts term.
    LAST insts = term /\
    insts <> [] /\
    (!x. f x <> []) /\
    f term = [term] /\
    (!i. MEM i insts /\ i.inst_id = term.inst_id ==> i = term) /\
    (!i i'. MEM i insts /\ MEM i' (f i) ==> i'.inst_id = i.inst_id)
    ==>
    LAST (FLAT (MAP f insts)) = term /\
    FLAT (MAP f insts) <> [] /\
    (!j. MEM j (FLAT (MAP f insts)) /\ j.inst_id = term.inst_id ==> j = term)
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- simp[last_flat_map_singleton]
  >- simp[flat_map_nonempty]
  >> rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     `j.inst_id = y.inst_id` by metis_tac[] >>
     `y = LAST insts` by metis_tac[] >>
     gvs[]
QED

(* Helper: dload transform preserves instruction IDs *)
Theorem dload_preserves_ids[local]:
  !dfg bb.
    MAP (\i. i.inst_id) (transform_block_dload dfg bb).bb_instructions =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[transform_block_dload_def, LET_THM, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[MAP_EQ_f] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  rpt CASE_TAC >> gvs[mk_dloadbytes_inst_def]
QED

(* transform_block_dload preserves LAST *)
Theorem transform_block_dload_last[local]:
  !fn bb.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    LAST (transform_block_dload (dfg_build_function fn) bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  rw[transform_block_dload_def, LET_THM] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[LAST_MAP] >>
  mp_tac (Q.SPECL [`dfg_build_function fn`, `fn`, `bb`] term_id_not_in_dload_nops) >>
  mp_tac (Q.SPECL [`fn`, `bb`] term_id_not_in_mstore_map) >>
  simp[LET_THM] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[] >>
  CASE_TAC >> gvs[]
QED

(* apply_memzero_inst always returns a non-empty list *)
Theorem apply_memzero_inst_nonempty[local]:
  !nop_set rep_map x. apply_memzero_inst nop_set rep_map x <> []
Proof
  rw[apply_memzero_inst_def] >> rpt CASE_TAC
QED

(* apply_groups_inst always returns a non-empty list *)
Theorem apply_groups_inst_nonempty[local]:
  !mode nop_set rep_map x. apply_groups_inst mode nop_set rep_map x <> []
Proof
  rw[apply_groups_inst_def] >> rpt CASE_TAC
QED

(* Memzero LAST preservation using weak preconditions *)
Theorem memzero_last_weak[local]:
  !dfg bb term.
    LAST bb.bb_instructions = term /\
    bb.bb_instructions <> [] /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) ==>
    LAST (transform_block_memzero dfg bb).bb_instructions = term
Proof
  rw[transform_block_memzero_def, LET_THM] >>
  mp_tac (Q.SPECL [`dfg`, `bb`] term_id_not_in_memzero_scan_weak) >>
  simp[LET_THM] >> rpt strip_tac >>
  simp[last_flat_map_singleton, apply_memzero_inst_nonempty,
       apply_memzero_inst_identity]
QED

(* Mode LAST preservation using weak preconditions *)
Theorem mode_last_weak[local]:
  !dfg fn bb mode term.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\
    LAST bb.bb_instructions = term /\
    bb.bb_instructions <> [] /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    MEM term (fn_insts fn) ==>
    LAST (transform_block_mode dfg mode bb).bb_instructions = term
Proof
  rpt gen_tac >> strip_tac >>
  CONV_TAC (SIMP_CONV (srw_ss()) [transform_block_mode_def, LET_THM]) >>
  mp_tac (Q.SPECL [`dfg_build_function fn`, `fn`, `bb`, `mode`]
          term_id_not_in_mode_scan_weak) >>
  simp[LET_THM] >> rpt strip_tac >>
  simp[last_flat_map_singleton, apply_groups_inst_nonempty,
       apply_groups_inst_identity]
QED

(* Memzero FLAT MAP preserves term_unique *)
Theorem memzero_preserves_term_unique[local]:
  !dfg bb term.
    LAST bb.bb_instructions = term /\
    bb.bb_instructions <> [] /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) ==>
    let bb' = transform_block_memzero dfg bb in
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = term /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)
Proof
  rw[transform_block_memzero_def, LET_THM] >>
  mp_tac (Q.SPECL [`dfg`, `bb`] term_id_not_in_memzero_scan_weak) >>
  simp[LET_THM] >> rpt strip_tac
  >- metis_tac[flat_map_nonempty, apply_memzero_inst_nonempty]
  >- simp[last_flat_map_singleton, apply_memzero_inst_nonempty,
          apply_memzero_inst_identity]
  >> gvs[MEM_FLAT, MEM_MAP] >>
     metis_tac[apply_memzero_ids, apply_memzero_inst_identity, MEM]
QED

(* Mode FLAT MAP preserves term_unique *)
Theorem mode_preserves_term_unique[local]:
  !dfg fn bb mode term.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\
    LAST bb.bb_instructions = term /\
    bb.bb_instructions <> [] /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    MEM term (fn_insts fn) ==>
    let bb' = transform_block_mode dfg mode bb in
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = term /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)
Proof
  rpt gen_tac >> strip_tac >>
  rw[transform_block_mode_def, LET_THM] >>
  mp_tac (Q.SPECL [`dfg_build_function fn`, `fn`, `bb`, `mode`]
          term_id_not_in_mode_scan_weak) >>
  simp[LET_THM] >> rpt strip_tac
  >- metis_tac[flat_map_nonempty, apply_groups_inst_nonempty]
  >- simp[last_flat_map_singleton, apply_groups_inst_nonempty,
          apply_groups_inst_identity]
  >> gvs[MEM_FLAT, MEM_MAP] >>
     metis_tac[apply_groups_ids, apply_groups_inst_identity, MEM]
QED

Theorem transform_block_succs[local]:
  !fn bb.
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    bb_succs (transform_block (dfg_build_function fn) bb) = bb_succs bb
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  (* Establish initial conditions *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator term.inst_opcode` by fs[bb_well_formed_def, Abbr `term`] >>
  imp_res_tac fn_inst_ids_distinct_block >>
  `!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term`
    by metis_tac[all_distinct_term_unique, Abbr `term`] >>
  `MEM term (fn_insts fn)`
    by (irule fn_insts_mem_block >> metis_tac[MEM_LAST_NOT_NIL, Abbr `term`]) >>
  (* Step 1: dload (MAP, preserves everything) *)
  qabbrev_tac `bb1 = transform_block_dload dfg bb` >>
  `LAST bb1.bb_instructions = term` by (
    simp[Abbr `bb1`, Abbr `dfg`] >>
    mp_tac (Q.SPECL [`fn`, `bb`] transform_block_dload_last) >>
    simp[Abbr `term`]) >>
  `bb1.bb_instructions <> []` by
    (simp[Abbr `bb1`, transform_block_dload_def, LET_THM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb1.bb_instructions)` by
    simp[Abbr `bb1`, dload_preserves_ids] >>
  `!i. MEM i bb1.bb_instructions /\ i.inst_id = term.inst_id ==> i = term`
    by metis_tac[all_distinct_term_unique] >>
  (* Step 2: memzero *)
  qabbrev_tac `bb2 = transform_block_memzero dfg bb1` >>
  `bb2.bb_instructions <> [] /\ LAST bb2.bb_instructions = term /\
   (!i. MEM i bb2.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb2`] >>
    mp_tac (Q.SPECL [`dfg`, `bb1`, `term`] memzero_preserves_term_unique) >>
    simp[LET_THM]) >>
  (* Step 3: CalldataMerge *)
  qabbrev_tac `bb3 = transform_block_mode dfg CalldataMerge bb2` >>
  `bb3.bb_instructions <> [] /\ LAST bb3.bb_instructions = term /\
   (!i. MEM i bb3.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb3`] >>
    mp_tac (Q.SPECL [`dfg`, `fn`, `bb2`, `CalldataMerge`, `term`]
            mode_preserves_term_unique) >>
    simp[LET_THM, Abbr `dfg`]) >>
  (* Step 4: DloadMerge *)
  qabbrev_tac `bb4 = transform_block_mode dfg DloadMerge bb3` >>
  `bb4.bb_instructions <> [] /\ LAST bb4.bb_instructions = term /\
   (!i. MEM i bb4.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb4`] >>
    mp_tac (Q.SPECL [`dfg`, `fn`, `bb3`, `DloadMerge`, `term`]
            mode_preserves_term_unique) >>
    simp[LET_THM, Abbr `dfg`]) >>
  (* Step 5: Mem2Mem *)
  qabbrev_tac `bb5 = transform_block_mode dfg Mem2Mem bb4` >>
  `bb5.bb_instructions <> [] /\ LAST bb5.bb_instructions = term /\
   (!i. MEM i bb5.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb5`] >>
    mp_tac (Q.SPECL [`dfg`, `fn`, `bb4`, `Mem2Mem`, `term`]
            mode_preserves_term_unique) >>
    simp[LET_THM, Abbr `dfg`]) >>
  (* Conclude: transform_block = bb5, use bb_succs_same_last_general *)
  `transform_block dfg bb = bb5` by
    simp[transform_block_def, LET_THM, Abbr `dfg`,
         Abbr `bb1`, Abbr `bb2`, Abbr `bb3`, Abbr `bb4`, Abbr `bb5`] >>
  fs[] >> irule bb_succs_same_last_general >> fs[Abbr `term`]
QED

(* ===== PHI exclusion from scan groups ===== *)

(* Stronger scan_store_has_id: dfg lookups come from ss_loads *)
Theorem scan_store_has_id_strong[local]:
  !dfg mode ss inst id.
    scan_has_id (scan_store dfg mode ss inst) id ==>
    scan_has_id ss id \/
    inst.inst_id = id \/
    (?v li. v IN FDOM ss.ss_loads /\
            dfg_get_def dfg v = SOME li /\ li.inst_id = id)
Proof
  rpt gen_tac >> simp[scan_store_def, LET_THM] >>
  rpt (CASE_TAC >> simp[hard_barrier_has_id]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[scan_has_id_add_copy, flush_hazards_has_id, invalidate_loads_has_id] >>
  strip_tac >> gvs[MEM_APPEND, flookup_thm] >> metis_tac[]
QED

(* Stronger scan_inst_has_id: direct adds have specific opcodes,
   dfg lookups connected to ss_loads *)
Theorem scan_inst_has_id_strong[local]:
  !dfg mode ss inst id.
    scan_has_id (scan_inst dfg mode ss inst) id ==>
    scan_has_id ss id \/
    (inst.inst_id = id /\ inst.inst_opcode = MSTORE) \/
    (inst.inst_id = id /\ inst.inst_opcode = mode_copy_opcode mode) \/
    (?v li. v IN FDOM ss.ss_loads /\
            dfg_get_def dfg v = SOME li /\ li.inst_id = id)
Proof
  rpt gen_tac >> simp[scan_inst_def] >>
  rpt IF_CASES_TAC >> gvs[] >> strip_tac >>
  imp_res_tac scan_load_has_id >>
  imp_res_tac scan_store_has_id_strong >>
  imp_res_tac scan_bulk_copy_has_id >>
  gvs[hard_barrier_has_id] >>
  metis_tac[]
QED

(* FOLDL version: IDs come from MSTORE/copy insts, or from dfg lookups
   where the variable was in ss_loads at that point *)
Theorem scan_foldl_ids_inv_strong[local]:
  !dfg mode insts ss id.
    scan_has_id (FOLDL (scan_inst dfg mode) ss insts) id ==>
    scan_has_id ss id \/
    (?inst. MEM inst insts /\ inst.inst_id = id /\
            (inst.inst_opcode = MSTORE \/
             inst.inst_opcode = mode_copy_opcode mode)) \/
    (?v li. dfg_get_def dfg v = SOME li /\ li.inst_id = id /\
            (v IN FDOM ss.ss_loads \/
             (?load_inst. MEM load_inst insts /\
                          load_inst.inst_opcode = mode_load_opcode mode /\
                          MEM v load_inst.inst_outputs)))
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  TRY (
    qpat_x_assum `scan_has_id (scan_inst _ _ _ _) _` (mp_tac o MATCH_MP scan_inst_has_id_strong) >>
    strip_tac >> gvs[] >> metis_tac[]) >>
  (* dfg case: v IN FDOM (scan_inst dfg mode ss h).ss_loads *)
  drule scan_inst_loads_inv >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* Scan block IDs: strong version with opcode + ss_loads connection *)
Theorem scan_block_ids_from_fn_strong[local]:
  !dfg mode fn bb cg id.
    dfg = dfg_build_function fn /\
    MEM cg (scan_block dfg mode bb).ss_flushed /\
    MEM id cg.cg_inst_ids ==>
    (?inst. MEM inst bb.bb_instructions /\ inst.inst_id = id /\
            (inst.inst_opcode = MSTORE \/
             inst.inst_opcode = mode_copy_opcode mode)) \/
    (?inst v load_inst. MEM inst (fn_insts fn) /\ inst.inst_id = id /\
              MEM v inst.inst_outputs /\
              MEM load_inst bb.bb_instructions /\
              load_inst.inst_opcode = mode_load_opcode mode /\
              MEM v load_inst.inst_outputs)
Proof
  rpt strip_tac >> gvs[scan_block_def, LET_THM] >>
  `scan_has_id (hard_barrier (FOLDL (scan_inst (dfg_build_function fn) mode)
    empty_scan_state bb.bb_instructions)) id` by (
    fs[scan_has_id_def, hard_barrier_def, MEM_APPEND] >>
    metis_tac[]) >>
  gvs[hard_barrier_has_id] >>
  drule scan_foldl_ids_inv_strong >> strip_tac
  >- gvs[scan_has_id_def, empty_scan_state_def]
  >- metis_tac[]
  >> (imp_res_tac dfg_build_function_correct >>
      gvs[empty_scan_state_def, FDOM_FEMPTY] >> metis_tac[])
QED

(* scan_inst_memzero: direct adds have specific opcodes *)
Theorem scan_inst_memzero_has_id_strong[local]:
  !dfg mz inst id.
    memzero_has_id (scan_inst_memzero dfg mz inst) id ==>
    memzero_has_id mz id \/
    (inst.inst_id = id /\
     (inst.inst_opcode = MSTORE \/ inst.inst_opcode = CALLDATACOPY))
Proof
  rpt gen_tac >> simp[scan_inst_memzero_def, memzero_has_id_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt (CASE_TAC >> gvs[memzero_barrier_def, MEM_APPEND]) >>
  gvs[add_copy_def] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac insert_sorted_ids >> gvs[copy_memzero_def] >>
       metis_tac[is_zero_store_def, is_calldatasize_copy_def]) >>
  TRY (imp_res_tac merge_adjacent_ids >> gvs[] >>
       imp_res_tac insert_sorted_ids >> gvs[copy_memzero_def] >>
       metis_tac[is_zero_store_def, is_calldatasize_copy_def]) >>
  gvs[memzero_barrier_def, MEM_APPEND] >> metis_tac[]
QED

(* FOLDL version for memzero *)
Theorem scan_memzero_foldl_ids_inv_strong[local]:
  !dfg insts mz id.
    memzero_has_id (FOLDL (scan_inst_memzero dfg) mz insts) id ==>
    memzero_has_id mz id \/
    (?inst. MEM inst insts /\ inst.inst_id = id /\
            (inst.inst_opcode = MSTORE \/ inst.inst_opcode = CALLDATACOPY))
Proof
  Induct_on `insts` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `memzero_has_id (FOLDL (scan_inst_memzero dfg)
     (scan_inst_memzero dfg mz h) insts) id`
    by (simp[memzero_has_id_def] >> metis_tac[]) >>
  first_x_assum drule >> simp[memzero_has_id_def] >>
  disch_then assume_tac >> gvs[] >>
  TRY (metis_tac[]) >>
  `memzero_has_id (scan_inst_memzero dfg mz h) id`
    by (simp[memzero_has_id_def] >> metis_tac[]) >>
  drule scan_inst_memzero_has_id_strong >>
  simp[memzero_has_id_def] >> metis_tac[]
QED

(* Memzero scan group IDs come from MSTORE/CALLDATACOPY instructions *)
Theorem scan_block_memzero_ids_from_bb_strong[local]:
  !dfg bb cg id.
    MEM cg (scan_block_memzero dfg bb).mz_flushed /\
    MEM id cg.cg_inst_ids ==>
    ?inst. MEM inst bb.bb_instructions /\ inst.inst_id = id /\
           (inst.inst_opcode = MSTORE \/ inst.inst_opcode = CALLDATACOPY)
Proof
  rw[scan_block_memzero_def, LET_THM] >>
  gvs[memzero_barrier_def, MEM_APPEND] >>
  mp_tac (Q.SPECL [`dfg`, `bb.bb_instructions`,
    `empty_memzero_state`, `id`] scan_memzero_foldl_ids_inv_strong) >>
  (impl_tac >- (simp[memzero_has_id_def] >> metis_tac[])) >>
  strip_tac >> gvs[empty_memzero_state_def, memzero_has_id_def] >>
  metis_tac[]
QED

(* ALL_DISTINCT on FLAT: elements from different sublists are disjoint *)
Theorem all_distinct_flat_disjoint[local]:
  !xss l1 l2. ALL_DISTINCT (FLAT xss) /\
    MEM l1 xss /\ MEM l2 xss /\ l1 <> l2 ==>
    !v. MEM v l1 ==> ~MEM v l2
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (fs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_FLAT])
  >- (fs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_FLAT])
  >> (fs[ALL_DISTINCT_APPEND] >> metis_tac[])
QED

(* ALL_DISTINCT on FLAT of MAP: shared element implies same source *)
Theorem all_distinct_flat_map_inj[local]:
  !xs (f:'a -> 'b list) a b v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM a xs /\ MEM b xs /\
    MEM v (f a) /\ MEM v (f b) ==> a = b
Proof
  Induct >> rw[] >> fs[ALL_DISTINCT_APPEND] >>
  TRY (first_x_assum irule >> metis_tac[] >> NO_TAC) >>
  `F` suffices_by simp[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

(* SSA: two instructions sharing an output variable must be identical *)
Theorem ssa_unique_definer[local]:
  !fn i1 i2 v.
    ssa_form fn /\ MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> i1 = i2
Proof
  rpt strip_tac >>
  qpat_x_assum `ssa_form _` (strip_assume_tac o REWRITE_RULE[ssa_form_def]) >>
  drule (INST_TYPE [alpha |-> ``:instruction``, beta |-> ``:string``]
    all_distinct_flat_map_inj) >>
  disch_then (qspecl_then [`i1`, `i2`, `v`] mp_tac) >> simp[]
QED

(* PHI IDs never appear in mode scan groups.
   Works for intermediate blocks where ALL_DISTINCT may be lost:
   requires per-PHI uniqueness + mode_load with outputs in fn_insts.
   The inst_outputs <> [] weakening is safe because scan_block_ids_from_fn_strong
   case 3 requires MEM v load_inst.inst_outputs (so outputs must be non-empty). *)
Theorem phi_id_not_in_mode_scan_gen[local]:
  !dfg fn mode bb cg id.
    dfg = dfg_build_function fn /\
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (* PHI instructions have unique IDs in the block *)
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\
                  phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\
                  i.inst_id = phi_inst.inst_id ==> i = phi_inst) /\
    (* PHI instructions are in fn_insts *)
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (* mode_load instructions with outputs are in fn_insts *)
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\
         i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)) /\
    MEM cg (scan_block dfg mode bb).ss_flushed /\
    MEM id cg.cg_inst_ids ==>
    !phi_inst. MEM phi_inst bb.bb_instructions /\
               phi_inst.inst_opcode = PHI ==>
    phi_inst.inst_id <> id
Proof
  rpt strip_tac >>
  drule_all scan_block_ids_from_fn_strong >> strip_tac >>
  TRY (
    (* Cases 1-2: inst in bb with MSTORE/mode_copy opcode *)
    CCONTR_TAC >> gvs[] >>
    (* inst has same ID as phi_inst and is in bb — by uniqueness, inst = phi_inst *)
    `inst = phi_inst` by metis_tac[] >>
    gvs[] >>
    Cases_on `mode` >> gvs[mode_copy_opcode_def] >> NO_TAC
  ) >>
  (* Case 3: id from dfg_get_def — inst is in fn_insts, load_inst has
     mode_load_opcode so also in fn_insts by precondition *)
  CCONTR_TAC >> gvs[] >>
  `MEM phi_inst (fn_insts fn)` by metis_tac[] >>
  `load_inst.inst_outputs <> []` by
    (Cases_on `load_inst.inst_outputs` >> fs[]) >>
  `MEM load_inst (fn_insts fn)` by metis_tac[] >>
  `inst = phi_inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  pop_assum SUBST_ALL_TAC >>
  `load_inst = phi_inst` by (
    match_mp_tac ssa_unique_definer >> qexistsl_tac [`fn`, `v`] >>
    fs[]) >>
  gvs[] >>
  Cases_on `mode` >> gvs[mode_load_opcode_def]
QED

(* PHI IDs never appear in memzero scan groups *)
Theorem phi_id_not_in_memzero_scan[local]:
  !dfg bb cg id.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM cg (scan_block_memzero dfg bb).mz_flushed /\
    MEM id cg.cg_inst_ids ==>
    !phi_inst. MEM phi_inst bb.bb_instructions /\
               phi_inst.inst_opcode = PHI ==>
    phi_inst.inst_id <> id
Proof
  rpt strip_tac >>
  drule_all scan_block_memzero_ids_from_bb_strong >>
  strip_tac >> CCONTR_TAC >> gvs[] >>
  `inst = phi_inst` by metis_tac[all_distinct_map_inv] >>
  gvs[]
QED

(* ===== Opcode PHI inequality lemmas ===== *)

Theorem nop_not_phi[local]:
  NOP <> PHI
Proof
  simp[]
QED

Theorem mstore_not_phi[local]:
  MSTORE <> PHI
Proof
  simp[]
QED

Theorem dloadbytes_not_phi[local]:
  DLOADBYTES <> PHI
Proof
  simp[]
QED

Theorem calldatasize_not_phi[local]:
  CALLDATASIZE <> PHI
Proof
  simp[]
QED

Theorem calldatacopy_not_phi[local]:
  CALLDATACOPY <> PHI
Proof
  simp[]
QED

Theorem mode_copy_not_phi[local]:
  !mode. mode_copy_opcode mode <> PHI
Proof
  Cases >> simp[mode_copy_opcode_def]
QED

Theorem mode_load_not_phi[local]:
  !mode. mode_load_opcode mode <> PHI
Proof
  Cases >> simp[mode_load_opcode_def]
QED

(* ===== MAP bb_well_formed (for dload) ===== *)

Theorem map_bb_well_formed[local]:
  !f bb.
    bb_well_formed bb /\
    (!inst. (f inst).inst_id = inst.inst_id) /\
    (is_terminator (LAST bb.bb_instructions).inst_opcode ==>
      f (LAST bb.bb_instructions) = LAST bb.bb_instructions) /\
    (!inst. MEM inst bb.bb_instructions /\
            ~is_terminator inst.inst_opcode ==>
      ~is_terminator (f inst).inst_opcode) /\
    (!inst. MEM inst bb.bb_instructions /\
            inst.inst_opcode = PHI ==> (f inst).inst_opcode = PHI) /\
    (!inst. MEM inst bb.bb_instructions /\
            inst.inst_opcode <> PHI ==> (f inst).inst_opcode <> PHI)
    ==>
    bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  rw[bb_well_formed_def] >>
  gvs[LAST_MAP, EL_MAP] >>
  rpt strip_tac >| [
    (* Goal 1: i = PRE (LENGTH ...) — contrapositive of terminator *)
    first_x_assum irule >> simp[] >>
    CCONTR_TAC >> fs[] >>
    imp_res_tac EL_MEM >> res_tac,
    (* Goal 2: (f ...❲i❳).inst_opcode = PHI — PHI prefix transfer *)
    CCONTR_TAC >> fs[] >>
    imp_res_tac LESS_TRANS >>
    imp_res_tac EL_MEM >>
    res_tac >> metis_tac[]
  ]
QED

(* ===== Per-sub-transform bb_well_formed ===== *)

(* Dload sub-transform preserves bb_well_formed *)
Theorem transform_block_dload_wf[local]:
  !fn bb.
    fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    bb_well_formed (transform_block_dload (dfg_build_function fn) bb)
Proof
  rpt strip_tac >>
  simp[transform_block_dload_def, LET_THM] >>
  irule map_bb_well_formed >> simp[] >>
  rpt conj_tac >| [
    (* 1: inst_id preserved *)
    rw[] >> rpt CASE_TAC >> simp[mk_nop_from_def, mk_dloadbytes_inst_def],
    (* 2: non-terminator preserved *)
    rw[] >> rpt CASE_TAC >>
    simp[mk_nop_from_def, is_terminator_def, mk_dloadbytes_inst_def],
    (* 3: non-PHI preserved *)
    rw[] >> rpt CASE_TAC >> gvs[mk_nop_from_def, mk_dloadbytes_inst_def],
    (* 4: PHI preserved — show identity via exclusion *)
    rpt strip_tac >>
    imp_res_tac phi_id_not_in_dload_nops >>
    imp_res_tac phi_id_not_in_mstore_map >> simp[],
    (* 5: terminator identity — show identity via exclusion *)
    strip_tac >>
    imp_res_tac term_id_not_in_dload_nops >>
    imp_res_tac term_id_not_in_mstore_map >>
    gvs[LET_THM]
  ]
QED

(* Memzero sub-transform preserves bb_well_formed *)
Theorem transform_block_memzero_wf[local]:
  !dfg bb.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    bb_well_formed bb ==>
    bb_well_formed (transform_block_memzero dfg bb)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!i. MEM i bb.bb_instructions /\
       i.inst_id = (LAST bb.bb_instructions).inst_id ==>
       i = LAST bb.bb_instructions` by metis_tac[all_distinct_term_unique] >>
  simp[transform_block_memzero_def, LET_THM] >>
  irule flat_map_bb_well_formed >> simp[] >> rpt conj_tac >| [
    simp[apply_memzero_inst_nonempty],
    rw[apply_memzero_inst_def, EVERY_DEF] >> rpt CASE_TAC >>
    simp[mk_nop_from_def, is_terminator_def, mk_zero_store_inst_def,
         mk_calldatasize_inst_def, mk_memzero_calldatacopy_def, LET_THM],
    rw[apply_memzero_inst_def, EVERY_DEF] >> rpt CASE_TAC >>
    simp[mk_nop_from_def, mk_zero_store_inst_def,
         mk_calldatasize_inst_def, mk_memzero_calldatacopy_def, LET_THM],
    rpt strip_tac >>
    `apply_memzero_inst
       (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
          (scan_block_memzero dfg bb).mz_flushed)
       (rep_map_of_groups bb.bb_instructions
          (scan_block_memzero dfg bb).mz_flushed)
       inst = [inst]` suffices_by simp[EVERY_DEF] >>
    irule apply_memzero_inst_identity >> conj_tac >| [
      rpt strip_tac >> imp_res_tac nop_ids_mem >>
      metis_tac[phi_id_not_in_memzero_scan],
      Cases_on `ALOOKUP
        (rep_map_of_groups bb.bb_instructions
          (scan_block_memzero dfg bb).mz_flushed)
        inst.inst_id` >> simp[] >>
      imp_res_tac rep_map_mem >>
      metis_tac[phi_id_not_in_memzero_scan]
    ],
    rpt strip_tac >> irule apply_memzero_inst_identity >>
    imp_res_tac term_id_not_in_memzero_scan_weak >> gvs[LET_THM]
  ]
QED

(* Wrapper around phi_id_not_in_mode_scan_gen with fewer hypotheses.
   Bundles fn-level facts so callers only provide block-level facts.
   This avoids metis_tac timeout when used inside proof branches. *)
Theorem mode_phi_exclusion[local]:
  !fn dfg mode bb phi_inst cg id'.
    dfg = dfg_build_function fn /\
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\
                  phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\
                  i.inst_id = phi_inst.inst_id ==> i = phi_inst) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\
         i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)) /\
    MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
    MEM cg (scan_block dfg mode bb).ss_flushed /\
    MEM id' cg.cg_inst_ids ==>
    phi_inst.inst_id <> id'
Proof
  rpt gen_tac >> strip_tac >>
  irule phi_id_not_in_mode_scan_gen >>
  conj_tac >- fs[] >>
  qexistsl_tac [`bb`, `cg`, `dfg`, `fn`, `mode`] >> fs[]
QED

(* Mode sub-transform preserves bb_well_formed.
   Weakened: mode_load precondition requires inst_outputs <> [] (needed for
   intermediate blocks where dload creates empty-output DLOADBYTES). *)
Theorem transform_block_mode_wf[local]:
  !fn dfg mode bb.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\
    fn_inst_ids_distinct fn /\ ssa_form fn /\
    bb_well_formed bb /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\
                  phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\
                  i.inst_id = phi_inst.inst_id ==> i = phi_inst) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\
         i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)) /\
    MEM (LAST bb.bb_instructions) (fn_insts fn) ==>
    bb_well_formed (transform_block_mode dfg mode bb)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[transform_block_mode_def, LET_THM] >>
  irule flat_map_bb_well_formed >> simp[] >> rpt conj_tac >| [
    (* 1: non-empty *)
    simp[apply_groups_inst_nonempty],
    (* 2: non-terminator *)
    rw[apply_groups_inst_def, EVERY_DEF, LET_THM] >> rpt CASE_TAC >>
    simp[mk_nop_from_def, is_terminator_def,
         mk_bulk_copy_inst_def, mk_load_inst_def,
         mk_mstore_from_load_def, LET_THM] >>
    Cases_on `mode` >> simp[mode_copy_opcode_def, mode_load_opcode_def, is_terminator_def],
    (* 3: non-PHI *)
    rw[apply_groups_inst_def, EVERY_DEF, LET_THM] >> rpt CASE_TAC >>
    simp[mk_nop_from_def, mk_bulk_copy_inst_def,
         mk_load_inst_def, mk_mstore_from_load_def] >>
    Cases_on `mode` >> simp[mode_copy_opcode_def, mode_load_opcode_def],
    (* 4: PHI identity — inst is PHI, show it's not in nop/rep sets *)
    rpt strip_tac >>
    `apply_groups_inst mode
       (nop_ids_of_groups (dfg_build_function fn) mode bb.bb_instructions
          (scan_block (dfg_build_function fn) mode bb).ss_flushed)
       (rep_map_of_groups bb.bb_instructions
          (scan_block (dfg_build_function fn) mode bb).ss_flushed)
       inst = [inst]` suffices_by simp[EVERY_DEF] >>
    irule apply_groups_inst_identity >>
    (conj_tac >| [
      rpt strip_tac >> imp_res_tac nop_ids_mem >>
      imp_res_tac mode_phi_exclusion >> metis_tac[],
      Cases_on `ALOOKUP
        (rep_map_of_groups bb.bb_instructions
          (scan_block (dfg_build_function fn) mode bb).ss_flushed)
        inst.inst_id` >> simp[] >>
      imp_res_tac rep_map_mem >>
      imp_res_tac mode_phi_exclusion >> metis_tac[]
    ]),
    (* 5: terminator identity *)
    rpt strip_tac >> irule apply_groups_inst_identity >>
    imp_res_tac term_id_not_in_mode_scan_weak >> gvs[LET_THM]
  ]
QED

(* ===== General FLAT MAP predicate toolkit ===== *)

(* General: P-outputs of FLAT(MAP f l) equal their source, hence are in l.
   Condition: any P-output from any source must equal that source. *)
Theorem flat_map_pred_from[local]:
  !P f l inst.
    MEM inst (FLAT (MAP f l)) /\ P inst /\
    (!x x'. MEM x l /\ MEM x' (f x) /\ P x' ==> x' = x) ==>
    MEM inst l
Proof
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

(* General: phi_id_unique preserved through FLAT MAP when f is identity on PHI,
   non-PHI produces non-PHI, and all outputs share source's inst_id *)
Theorem flat_map_phi_id_unique[local]:
  !f l.
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
    (* f is identity on PHI *)
    (!x. MEM x l /\ x.inst_opcode = PHI ==> f x = [x]) /\
    (* f on non-PHI produces only non-PHI *)
    (!x x'. MEM x l /\ x.inst_opcode <> PHI /\ MEM x' (f x) ==>
            x'.inst_opcode <> PHI) /\
    (* f preserves inst_id *)
    (!x x'. MEM x l /\ MEM x' (f x) ==> x'.inst_id = x.inst_id) ==>
    (!phi_inst i.
       MEM phi_inst (FLAT (MAP f l)) /\ phi_inst.inst_opcode = PHI /\
       MEM i (FLAT (MAP f l)) /\ i.inst_id = phi_inst.inst_id ==>
       i = phi_inst)
Proof
  rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  (* phi_inst comes from y, i comes from y' *)
  `phi_inst.inst_id = y.inst_id` by metis_tac[] >>
  `i.inst_id = y'.inst_id` by metis_tac[] >>
  `y.inst_id = y'.inst_id` by metis_tac[] >>
  `y = y'` by metis_tac[all_distinct_map_inv] >>
  gvs[] >>
  (* Both from same source y. y must be PHI (otherwise phi_inst couldn't be PHI) *)
  Cases_on `y.inst_opcode = PHI` >- gvs[] >>
  metis_tac[]
QED

(* Weaker version: uses phi_id_unique instead of ALL_DISTINCT.
   Works for intermediate blocks where ALL_DISTINCT is lost. *)
Theorem flat_map_phi_id_unique_weak[local]:
  !f l.
    (* phi_id_unique of input *)
    (!phi_inst i. MEM phi_inst l /\ phi_inst.inst_opcode = PHI /\
                  MEM i l /\ i.inst_id = phi_inst.inst_id ==> i = phi_inst) /\
    (* f is identity on PHI *)
    (!x. MEM x l /\ x.inst_opcode = PHI ==> f x = [x]) /\
    (* f on non-PHI produces only non-PHI *)
    (!x x'. MEM x l /\ x.inst_opcode <> PHI /\ MEM x' (f x) ==>
            x'.inst_opcode <> PHI) /\
    (* f preserves inst_id *)
    (!x x'. MEM x l /\ MEM x' (f x) ==> x'.inst_id = x.inst_id) ==>
    (!phi_inst i.
       MEM phi_inst (FLAT (MAP f l)) /\ phi_inst.inst_opcode = PHI /\
       MEM i (FLAT (MAP f l)) /\ i.inst_id = phi_inst.inst_id ==>
       i = phi_inst)
Proof
  rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  (* phi_inst comes from y, i comes from y'. y must be PHI. *)
  Cases_on `y.inst_opcode = PHI` >- (
    (* f y = [y], so phi_inst = y *)
    `f y = [y]` by metis_tac[] >>
    `MEM phi_inst [y]` by metis_tac[MEM] >>
    fs[MEM] >>
    (* Now phi_inst = y. i from y', i.inst_id = y'.inst_id, phi_inst.inst_id = y.inst_id *)
    (* y' must be PHI too, otherwise contradiction with phi_id_unique *)
    Cases_on `y'.inst_opcode = PHI` >- (
      `f y' = [y']` by metis_tac[] >>
      `MEM i [y']` by metis_tac[MEM] >>
      fs[MEM] >>
      (* y' and y both PHI in l with same id *)
      metis_tac[]) >>
    (* y' non-PHI. All outputs non-PHI. But y'.inst_id = y.inst_id = phi_inst.inst_id *)
    `y'.inst_id = y.inst_id` by metis_tac[] >>
    (* y is PHI in l, y' in l with same id => y' = y by phi_id_unique *)
    `y' = y` by metis_tac[] >>
    (* But y is PHI and y' is non-PHI — contradiction *)
    fs[]) >>
  (* y non-PHI: phi_inst from f y, but all outputs of non-PHI are non-PHI *)
  metis_tac[]
QED

(* PHI in dload output came from input — dload is MAP, identity on PHI *)
Theorem dload_phi_from[local]:
  !fn bb inst.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    MEM inst (transform_block_dload (dfg_build_function fn) bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    MEM inst bb.bb_instructions
Proof
  rpt strip_tac >>
  gvs[transform_block_dload_def, LET_THM, MEM_MAP] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def, mk_dloadbytes_inst_def] >>
  rpt (CASE_TAC >> gvs[mk_dloadbytes_inst_def])
QED

(* Memzero: apply_memzero_inst is identity on PHI when PHI IDs not in scan *)
Theorem apply_memzero_inst_phi_identity[local]:
  !dfg bb inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    apply_memzero_inst
      (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
         (scan_block_memzero dfg bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
         (scan_block_memzero dfg bb).mz_flushed)
      inst = [inst]
Proof
  rpt strip_tac >> irule apply_memzero_inst_identity >>
  conj_tac >| [
    rpt strip_tac >> imp_res_tac nop_ids_mem >>
    metis_tac[phi_id_not_in_memzero_scan],
    Cases_on `ALOOKUP
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero dfg bb).mz_flushed) inst.inst_id` >> simp[] >>
    imp_res_tac rep_map_mem >>
    metis_tac[phi_id_not_in_memzero_scan]]
QED

(* Memzero: non-PHI source produces only non-PHI outputs *)
Theorem apply_memzero_inst_non_phi[local]:
  !nop_set rep_map inst inst'.
    inst.inst_opcode <> PHI /\
    MEM inst' (apply_memzero_inst nop_set rep_map inst) ==>
    inst'.inst_opcode <> PHI
Proof
  rw[apply_memzero_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  BasicProvers.every_case_tac >> gvs[mk_zero_store_inst_def,
    mk_calldatasize_inst_def, mk_memzero_calldatacopy_def]
QED

(* Mode: apply_groups_inst is identity on PHI when PHI IDs not in scan *)
Theorem apply_groups_inst_phi_identity[local]:
  !dfg fn mode bb inst.
    dfg = dfg_build_function fn /\
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\
                  phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\
                  i.inst_id = phi_inst.inst_id ==> i = phi_inst) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\
         i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)) /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    apply_groups_inst mode
      (nop_ids_of_groups (dfg_build_function fn) mode bb.bb_instructions
         (scan_block (dfg_build_function fn) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
         (scan_block (dfg_build_function fn) mode bb).ss_flushed)
      inst = [inst]
Proof
  rpt strip_tac >> irule apply_groups_inst_identity >>
  conj_tac >| [
    rpt strip_tac >> imp_res_tac nop_ids_mem >>
    imp_res_tac mode_phi_exclusion >> metis_tac[],
    Cases_on `ALOOKUP
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn) mode bb).ss_flushed)
      inst.inst_id` >> simp[] >>
    imp_res_tac rep_map_mem >>
    imp_res_tac mode_phi_exclusion >> metis_tac[]]
QED

(* Mode: non-PHI source produces only non-PHI outputs *)
Theorem apply_groups_inst_non_phi[local]:
  !mode nop_set rep_map inst inst'.
    inst.inst_opcode <> PHI /\
    MEM inst' (apply_groups_inst mode nop_set rep_map inst) ==>
    inst'.inst_opcode <> PHI
Proof
  rw[apply_groups_inst_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  Cases_on `mode` >>
  gvs[mode_copy_opcode_def, mode_load_opcode_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  gvs[mk_bulk_copy_inst_def, mk_load_inst_def,
    mk_mstore_from_load_def, mode_copy_opcode_def, mode_load_opcode_def]
QED

(* Mode load opcode passthrough: memzero doesn't create mode_load opcodes *)
Theorem apply_memzero_inst_mode_load_passthrough[local]:
  !m nop_set rep_map inst inst'.
    MEM inst' (apply_memzero_inst nop_set rep_map inst) /\
    inst'.inst_opcode = mode_load_opcode m /\ inst'.inst_outputs <> [] ==>
    inst' = inst
Proof
  rw[apply_memzero_inst_def, LET_THM] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  BasicProvers.every_case_tac >>
  gvs[mk_zero_store_inst_def, mk_calldatasize_inst_def,
    mk_memzero_calldatacopy_def] >>
  Cases_on `m` >> gvs[mode_load_opcode_def]
QED

(* Mode load opcode passthrough: apply_groups_inst mode doesn't create
   mode_load_opcode m for m <> mode *)
Theorem apply_groups_inst_mode_load_passthrough[local]:
  !mode m nop_set rep_map inst inst'.
    m <> mode /\
    MEM inst' (apply_groups_inst mode nop_set rep_map inst) /\
    inst'.inst_opcode = mode_load_opcode m /\ inst'.inst_outputs <> [] ==>
    inst' = inst
Proof
  rw[apply_groups_inst_def, LET_THM] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  Cases_on `mode` >>
  gvs[mode_copy_opcode_def, mode_load_opcode_def] >>
  BasicProvers.every_case_tac >>
  gvs[mk_bulk_copy_inst_def, mk_load_inst_def,
    mk_mstore_from_load_def, mode_copy_opcode_def, mode_load_opcode_def] >>
  Cases_on `m` >> gvs[mode_load_opcode_def]
QED

(* Dload doesn't create mode_load opcodes with non-empty outputs *)
Theorem dload_mode_load_passthrough[local]:
  !fn bb inst m.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    MEM inst (transform_block_dload (dfg_build_function fn) bb).bb_instructions /\
    inst.inst_opcode = mode_load_opcode m /\ inst.inst_outputs <> [] ==>
    MEM inst bb.bb_instructions
Proof
  rpt strip_tac >>
  gvs[transform_block_dload_def, LET_THM, MEM_MAP] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def, mk_dloadbytes_inst_def] >>
  rpt (CASE_TAC >> gvs[mk_dloadbytes_inst_def])
QED

(* Mode load passthrough: transform_block_mode mode' preserves
   mode_load m instructions when m <> mode' *)
Theorem mode_load_passthrough[local]:
  !dfg mode mode' bb inst.
    mode <> mode' /\
    MEM inst (transform_block_mode dfg mode' bb).bb_instructions /\
    inst.inst_opcode = mode_load_opcode mode /\ inst.inst_outputs <> [] ==>
    MEM inst bb.bb_instructions
Proof
  rpt strip_tac >>
  gvs[transform_block_mode_def, LET_THM] >>
  irule flat_map_pred_from >>
  qexists_tac `\i. i.inst_opcode = mode_load_opcode mode /\ i.inst_outputs <> []` >>
  qexists_tac `apply_groups_inst mode'
    (nop_ids_of_groups dfg mode' bb.bb_instructions
       (scan_block dfg mode' bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
       (scan_block dfg mode' bb).ss_flushed)` >>
  simp[] >> rpt strip_tac >>
  metis_tac[apply_groups_inst_mode_load_passthrough]
QED

(* One memzero step preserves all invariants needed by mode steps *)
Theorem memzero_step_wf[local]:
  !fn dfg bb term.
    bb_well_formed bb /\
    bb.bb_instructions <> [] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    LAST bb.bb_instructions = term /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\ i.inst_id = phi_inst.inst_id ==>
                  i = phi_inst) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!m i. MEM i bb.bb_instructions /\
           i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
           MEM i (fn_insts fn)) /\
    MEM term (fn_insts fn) ==>
    let bb' = transform_block_memzero dfg bb in
    bb_well_formed bb' /\
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = term /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    (!phi_inst i. MEM phi_inst bb'.bb_instructions /\ phi_inst.inst_opcode = PHI /\
                  MEM i bb'.bb_instructions /\ i.inst_id = phi_inst.inst_id ==>
                  i = phi_inst) /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!m i. MEM i bb'.bb_instructions /\
           i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
           MEM i (fn_insts fn)) /\
    MEM term (fn_insts fn)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb' = transform_block_memzero dfg bb` >>
  qabbrev_tac `mz_nop = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
                           (scan_block_memzero dfg bb).mz_flushed` >>
  qabbrev_tac `mz_rep = rep_map_of_groups bb.bb_instructions
                           (scan_block_memzero dfg bb).mz_flushed` >>
  `bb'.bb_instructions =
     FLAT (MAP (apply_memzero_inst mz_nop mz_rep) bb.bb_instructions)` by
    simp[Abbr `bb'`, Abbr `mz_nop`, Abbr `mz_rep`,
         transform_block_memzero_def, LET_THM] >>
  (* 1. bb_well_formed *)
  `bb_well_formed bb'` by
    (simp[Abbr `bb'`] >> irule transform_block_memzero_wf >> fs[]) >>
  (* 2. term_unique *)
  `bb'.bb_instructions <> [] /\ LAST bb'.bb_instructions = term /\
   (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb'`] >>
    mp_tac (Q.SPECL [`dfg`, `bb`, `term`] memzero_preserves_term_unique) >>
    simp[LET_THM]) >>
  (* 3. PHI in bb' came from bb *)
  `!i. MEM i bb'.bb_instructions /\ i.inst_opcode = PHI ==>
       MEM i bb.bb_instructions` by (
    rpt strip_tac >> irule flat_map_pred_from >>
    qexists_tac `\i. i.inst_opcode = PHI` >>
    qexists_tac `apply_memzero_inst mz_nop mz_rep` >>
    simp[] >> rpt strip_tac >>
    Cases_on `x.inst_opcode = PHI` >- (
      `apply_memzero_inst mz_nop mz_rep x = [x]` by (
        simp[Abbr `mz_nop`, Abbr `mz_rep`] >>
        irule apply_memzero_inst_phi_identity >> metis_tac[]) >>
      gvs[MEM]) >>
    metis_tac[apply_memzero_inst_non_phi]) >>
  (* 4. phi_id_unique — use ALL_DISTINCT version *)
  `!phi_inst i. MEM phi_inst bb'.bb_instructions /\ phi_inst.inst_opcode = PHI /\
     MEM i bb'.bb_instructions /\ i.inst_id = phi_inst.inst_id ==> i = phi_inst` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`apply_memzero_inst mz_nop mz_rep`,
                      `bb.bb_instructions`] flat_map_phi_id_unique) >>
    (impl_tac >- (
      rpt conj_tac
      >- fs[]
      >- (rpt strip_tac >> simp[Abbr `mz_nop`, Abbr `mz_rep`] >>
          irule apply_memzero_inst_phi_identity >> metis_tac[])
      >- metis_tac[apply_memzero_inst_non_phi]
      >> metis_tac[apply_memzero_ids])) >>
    disch_then irule >> gvs[]) >>
  (* 5. mode_load passthrough *)
  `!m i. MEM i bb'.bb_instructions /\
         i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
         MEM i bb.bb_instructions` by (
    rpt strip_tac >> irule flat_map_pred_from >>
    qexists_tac `\i. i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> []` >>
    qexists_tac `apply_memzero_inst mz_nop mz_rep` >>
    simp[] >> rpt strip_tac >>
    metis_tac[apply_memzero_inst_mode_load_passthrough]) >>
  (* Conclude *)
  `transform_block_memzero dfg bb = bb'` by simp[Abbr `bb'`] >>
  simp[LET_THM] >> metis_tac[]
QED

(* One mode step preserves structural invariants.
   Only needs current mode's mode_load in fn_insts (for phi exclusion).
   Does NOT track mode_load passthrough — caller handles that separately. *)
Theorem mode_step_wf[local]:
  !fn dfg mode bb term.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\
    fn_inst_ids_distinct fn /\ ssa_form fn /\
    bb_well_formed bb /\
    bb.bb_instructions <> [] /\
    LAST bb.bb_instructions = term /\
    is_terminator term.inst_opcode /\
    (!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    (!phi_inst i. MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
                  MEM i bb.bb_instructions /\ i.inst_id = phi_inst.inst_id ==>
                  i = phi_inst) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\
         i.inst_outputs <> [] ==> MEM i (fn_insts fn)) /\
    MEM term (fn_insts fn) ==>
    let bb' = transform_block_mode dfg mode bb in
    bb_well_formed bb' /\
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = term /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term) /\
    (!phi_inst i. MEM phi_inst bb'.bb_instructions /\ phi_inst.inst_opcode = PHI /\
                  MEM i bb'.bb_instructions /\ i.inst_id = phi_inst.inst_id ==>
                  i = phi_inst) /\
    (!i. MEM i bb'.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb' = transform_block_mode dfg mode bb` >>
  qabbrev_tac `nop_set = nop_ids_of_groups dfg mode bb.bb_instructions
                           (scan_block dfg mode bb).ss_flushed` >>
  qabbrev_tac `rep_map = rep_map_of_groups bb.bb_instructions
                           (scan_block dfg mode bb).ss_flushed` >>
  `bb'.bb_instructions =
     FLAT (MAP (apply_groups_inst mode nop_set rep_map) bb.bb_instructions)` by
    simp[Abbr `bb'`, Abbr `nop_set`, Abbr `rep_map`,
         transform_block_mode_def, LET_THM] >>
  (* 1. bb_well_formed *)
  `bb_well_formed bb'` by (
    simp[Abbr `bb'`] >> irule transform_block_mode_wf >> metis_tac[]) >>
  (* 2. term_unique *)
  `bb'.bb_instructions <> [] /\ LAST bb'.bb_instructions = term /\
   (!i. MEM i bb'.bb_instructions /\ i.inst_id = term.inst_id ==> i = term)` by (
    simp[Abbr `bb'`] >>
    mp_tac (Q.SPECL [`dfg`, `fn`, `bb`, `mode`, `term`] mode_preserves_term_unique) >>
    simp[LET_THM]) >>
  (* Pre-establish: PHI in bb' came from bb *)
  `!i. MEM i bb'.bb_instructions /\ i.inst_opcode = PHI ==>
       MEM i bb.bb_instructions` by (
    rpt strip_tac >> irule flat_map_pred_from >>
    qexists_tac `\i. i.inst_opcode = PHI` >>
    qexists_tac `apply_groups_inst mode nop_set rep_map` >>
    simp[] >> rpt strip_tac >>
    Cases_on `x.inst_opcode = PHI` >- (
      `apply_groups_inst mode nop_set rep_map x = [x]` by (
        simp[Abbr `nop_set`, Abbr `rep_map`] >>
        irule apply_groups_inst_phi_identity >> metis_tac[]) >>
      gvs[MEM]) >>
    metis_tac[apply_groups_inst_non_phi]) >>
  (* 3. phi_id_unique for bb' — use flat_map_phi_id_unique_weak *)
  `!phi_inst i. MEM phi_inst bb'.bb_instructions /\ phi_inst.inst_opcode = PHI /\
     MEM i bb'.bb_instructions /\ i.inst_id = phi_inst.inst_id ==> i = phi_inst` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`apply_groups_inst mode nop_set rep_map`,
                      `bb.bb_instructions`] flat_map_phi_id_unique_weak) >>
    (impl_tac >- (
      rpt conj_tac
      >- metis_tac[]
      >- (rpt strip_tac >> simp[Abbr `nop_set`, Abbr `rep_map`] >>
          irule apply_groups_inst_phi_identity >> metis_tac[])
      >- metis_tac[apply_groups_inst_non_phi]
      >> metis_tac[apply_groups_ids])) >>
    disch_then irule >> gvs[]) >>
  (* Conclude *)
  `transform_block_mode dfg mode bb = bb'` by simp[Abbr `bb'`] >>
  simp[LET_THM]
QED

(* ===== Obligations ===== *)

(* Fresh names introduced by the transform:
   - "__mm_load_<id>" from mode sub-passes (32-byte non-mstore rep)
   - "__mz_cds_<id>" from memzero sub-pass (cg_length > 32)
   These must not collide with any existing output variable. *)
Definition mm_fresh_outputs_def:
  mm_fresh_outputs fn =
    let dfg = dfg_build_function fn in
    BIGUNION (IMAGE (λbb.
      let bb1 = transform_block_dload dfg bb in
      let bb2 = transform_block_memzero dfg bb1 in
      let bb3 = transform_block_mode dfg CalldataMerge bb2 in
      let bb4 = transform_block_mode dfg DloadMerge bb3 in
      mm_block_fresh_memzero dfg bb1 ∪
      mm_block_fresh_mode dfg CalldataMerge bb2 ∪
      mm_block_fresh_mode dfg DloadMerge bb3 ∪
      mm_block_fresh_mode dfg Mem2Mem bb4
    ) (set fn.fn_blocks))
End

Definition mm_fresh_names_ok_def:
  mm_fresh_names_ok fn ⇔
    DISJOINT (mm_fresh_outputs fn)
             (set (FLAT (MAP (λi. i.inst_outputs) (fn_insts fn))))
End

(* ===== SSA preservation infrastructure ===== *)

Triviality fn_insts_blocks_flat[local]:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* Dload sub-pass: each instruction is either NOP'd or original *)
Triviality dload_output_traced[local]:
  !dfg bb inst.
    MEM inst (transform_block_dload dfg bb).bb_instructions ==>
    inst.inst_outputs = [] \/ MEM inst bb.bb_instructions
Proof
  rw[transform_block_dload_def, LET_THM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  rpt IF_CASES_TAC >> gvs[mk_nop_from_def] >>
  CASE_TAC >> gvs[mk_dloadbytes_inst_def]
QED

(* Memzero sub-pass: each output variable is from the input block or fresh *)
Triviality memzero_output_traced[local]:
  !dfg bb inst v.
    MEM inst (transform_block_memzero dfg bb).bb_instructions /\
    MEM v inst.inst_outputs ==>
    (?orig. MEM orig bb.bb_instructions /\ MEM v orig.inst_outputs) \/
    v IN mm_block_fresh_memzero dfg bb
Proof
  rw[transform_block_memzero_def, LET_THM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  fs[apply_memzero_inst_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def,
      mk_calldatasize_inst_def, mk_memzero_calldatacopy_def] >>
  TRY (disj1_tac >> metis_tac[] >> NO_TAC) >>
  disj2_tac >> simp[mm_block_fresh_memzero_def, LET_THM] >>
  disj2_tac >> metis_tac[]
QED

(* Mode sub-pass: each output variable is from the input block or fresh *)
Triviality mode_output_traced[local]:
  !dfg mode bb inst v.
    MEM inst (transform_block_mode dfg mode bb).bb_instructions /\
    MEM v inst.inst_outputs ==>
    (?orig. MEM orig bb.bb_instructions /\ MEM v orig.inst_outputs) \/
    v IN mm_block_fresh_mode dfg mode bb
Proof
  rw[transform_block_mode_def, LET_THM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  fs[apply_groups_inst_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def,
      mk_load_inst_def, mk_mstore_from_load_def] >>
  TRY (disj1_tac >> metis_tac[] >> NO_TAC) >>
  disj2_tac >> simp[mm_block_fresh_mode_def, LET_THM] >>
  disj2_tac >> metis_tac[]
QED

(* Full transform: each output variable is original or in mm_fresh_outputs *)
Triviality transform_block_output_mem[local]:
  !fn bb v.
    MEM bb fn.fn_blocks /\
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (transform_block (dfg_build_function fn) bb).bb_instructions)) ==>
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) \/
    v IN mm_fresh_outputs fn
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  gvs[MEM_FLAT, MEM_MAP] >>
  fs[transform_block_def, LET_THM] >>
  qabbrev_tac `bb1 = transform_block_dload dfg bb` >>
  qabbrev_tac `bb2 = transform_block_memzero dfg bb1` >>
  qabbrev_tac `bb3 = transform_block_mode dfg CalldataMerge bb2` >>
  qabbrev_tac `bb4 = transform_block_mode dfg DloadMerge bb3` >>
  (* Track v backwards: Mem2Mem → DloadMerge → CalldataMerge → memzero → dload *)
  `(?orig. MEM orig bb4.bb_instructions /\ MEM v orig.inst_outputs) \/
   v IN mm_block_fresh_mode dfg Mem2Mem bb4` by
    metis_tac[mode_output_traced] >>
  TRY (disj2_tac >> simp[mm_fresh_outputs_def, LET_THM,
    Abbr`bb4`,Abbr`bb3`,Abbr`bb2`,Abbr`bb1`] >>
    simp[PULL_EXISTS] >> qexists_tac `bb` >> simp[] >> NO_TAC) >>
  `(?orig. MEM orig bb3.bb_instructions /\ MEM v orig.inst_outputs) \/
   v IN mm_block_fresh_mode dfg DloadMerge bb3` by
    metis_tac[mode_output_traced] >>
  TRY (disj2_tac >> simp[mm_fresh_outputs_def, LET_THM,
    Abbr`bb3`,Abbr`bb2`,Abbr`bb1`] >>
    simp[PULL_EXISTS] >> qexists_tac `bb` >> simp[] >> NO_TAC) >>
  `(?orig. MEM orig bb2.bb_instructions /\ MEM v orig.inst_outputs) \/
   v IN mm_block_fresh_mode dfg CalldataMerge bb2` by
    metis_tac[mode_output_traced] >>
  TRY (disj2_tac >> simp[mm_fresh_outputs_def, LET_THM,
    Abbr`bb2`,Abbr`bb1`] >>
    simp[PULL_EXISTS] >> qexists_tac `bb` >> simp[] >> NO_TAC) >>
  `(?orig. MEM orig bb1.bb_instructions /\ MEM v orig.inst_outputs) \/
   v IN mm_block_fresh_memzero dfg bb1` by
    metis_tac[memzero_output_traced] >>
  TRY (disj2_tac >> simp[mm_fresh_outputs_def, LET_THM, Abbr`bb1`] >>
    simp[PULL_EXISTS] >> qexists_tac `bb` >> simp[] >> NO_TAC) >>
  (* v from dload output — either empty outputs or original instruction *)
  disj1_tac >> fs[Abbr `bb1`] >>
  metis_tac[dload_output_traced, MEM]
QED

Triviality flat_map_flat_map[local]:
  !f g l. FLAT (MAP f (FLAT (MAP g l))) =
          FLAT (MAP (FLAT o MAP f o g) l)
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[FLAT_APPEND, MAP_APPEND]
QED

Theorem mm_preserves_ssa_form:
  ∀fn. ssa_form fn ∧ fn_inst_ids_distinct fn ∧ mm_fresh_names_ok fn ⇒
       ssa_form (transform_function fn)
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
     transform_function_def, LET_THM,
     function_map_transform_def, MAP_MAP_o, combinTheory.o_DEF,
     flat_map_flat_map] >>
  cheat
QED

(* Main theorem: transform_block preserves bb_well_formed *)
Theorem transform_block_wf[local]:
  !fn bb.
    fn_inst_wf fn /\ wf_function fn /\
    fn_inst_ids_distinct fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    bb_well_formed (transform_block (dfg_build_function fn) bb)
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  (* Establish base facts *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator term.inst_opcode` by fs[bb_well_formed_def, Abbr `term`] >>
  imp_res_tac fn_inst_ids_distinct_block >>
  `!i. MEM i bb.bb_instructions /\ i.inst_id = term.inst_id ==> i = term`
    by metis_tac[all_distinct_term_unique, Abbr `term`] >>
  `MEM term (fn_insts fn)`
    by (irule fn_insts_mem_block >> metis_tac[MEM_LAST_NOT_NIL, Abbr `term`]) >>
  (* PHI facts for original bb *)
  `!phi_inst i. MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
     MEM i bb.bb_instructions /\ i.inst_id = phi_inst.inst_id ==> i = phi_inst`
    by metis_tac[all_distinct_map_inv] >>
  `!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)`
    by (rpt strip_tac >> irule fn_insts_mem_block >> metis_tac[]) >>
  (* Step 1: dload (MAP, preserves ids and all PHI facts) *)
  qabbrev_tac `bb1 = transform_block_dload dfg bb` >>
  `bb_well_formed bb1` by
    (simp[Abbr `bb1`, Abbr `dfg`] >> irule transform_block_dload_wf >>
     metis_tac[]) >>
  `bb1.bb_instructions <> []` by
    (simp[Abbr `bb1`, transform_block_dload_def, LET_THM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb1.bb_instructions)` by
    simp[Abbr `bb1`, dload_preserves_ids] >>
  `LAST bb1.bb_instructions = term` by (
    simp[Abbr `bb1`, Abbr `dfg`] >>
    mp_tac (Q.SPECL [`fn`, `bb`] transform_block_dload_last) >>
    simp[Abbr `term`]) >>
  `!i. MEM i bb1.bb_instructions /\ i.inst_id = term.inst_id ==> i = term`
    by metis_tac[all_distinct_term_unique] >>
  (* Dload PHI identity: PHI in bb1 = PHI in bb *)
  `!i. MEM i bb1.bb_instructions /\ i.inst_opcode = PHI ==>
       MEM i bb.bb_instructions` by (
    rpt strip_tac >> irule dload_phi_from >>
    simp[Abbr `bb1`, Abbr `dfg`] >> metis_tac[]) >>
  `!i. MEM i bb1.bb_instructions /\ i.inst_opcode = PHI ==>
       MEM i (fn_insts fn)` by metis_tac[] >>
  `!phi_inst i. MEM phi_inst bb1.bb_instructions /\ phi_inst.inst_opcode = PHI /\
     MEM i bb1.bb_instructions /\ i.inst_id = phi_inst.inst_id ==> i = phi_inst`
    by metis_tac[all_distinct_map_inv] >>
  (* mode_load_in_fn for bb1: dload passthrough + fn_insts_mem_block *)
  `!m i. MEM i bb1.bb_instructions /\
         i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)` by (
    rpt strip_tac >>
    `MEM i bb.bb_instructions` by (
      simp[Abbr `bb1`, Abbr `dfg`] >>
      irule dload_mode_load_passthrough >> metis_tac[]) >>
    irule fn_insts_mem_block >> metis_tac[]) >>
  (* Step 2: memzero via memzero_step_wf *)
  mp_tac (Q.SPECL [`fn`, `dfg`, `bb1`, `term`] memzero_step_wf) >>
  simp[LET_THM] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  qabbrev_tac `bb2 = transform_block_memzero dfg bb1` >>
  (* Step 3: CalldataMerge via mode_step_wf
     mode_load CalldataMerge bb2 in fn_insts — from memzero_step_wf *)
  mp_tac (Q.SPECL [`fn`, `dfg`, `CalldataMerge`, `bb2`, `term`] mode_step_wf) >>
  simp[LET_THM] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  (* Establish DloadMerge and Mem2Mem mode_load passthroughs BEFORE abbreviating bb3.
     This avoids the Abbrev expansion issue with irule mode_load_passthrough. *)
  `!i. MEM i (transform_block_mode dfg CalldataMerge bb2).bb_instructions /\
       i.inst_opcode = mode_load_opcode DloadMerge /\ i.inst_outputs <> [] ==>
       MEM i (fn_insts fn)` by (
    rpt strip_tac >>
    `MEM i bb2.bb_instructions` by (
      match_mp_tac mode_load_passthrough >>
      qexistsl_tac [`dfg`, `DloadMerge`, `CalldataMerge`] >>
      simp[TypeBase.distinct_of ``:merge_mode``]) >>
    metis_tac[]) >>
  `!i. MEM i (transform_block_mode dfg CalldataMerge bb2).bb_instructions /\
       i.inst_opcode = mode_load_opcode Mem2Mem /\ i.inst_outputs <> [] ==>
       MEM i (fn_insts fn)` by (
    rpt strip_tac >>
    `MEM i bb2.bb_instructions` by (
      match_mp_tac mode_load_passthrough >>
      qexistsl_tac [`dfg`, `Mem2Mem`, `CalldataMerge`] >>
      simp[TypeBase.distinct_of ``:merge_mode``]) >>
    metis_tac[]) >>
  qabbrev_tac `bb3 = transform_block_mode dfg CalldataMerge bb2` >>
  (* Step 4: DloadMerge *)
  mp_tac (Q.SPECL [`fn`, `dfg`, `DloadMerge`, `bb3`, `term`] mode_step_wf) >>
  SIMP_TAC std_ss [LET_THM] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  (* Establish Mem2Mem mode_load passthrough BEFORE abbreviating bb4 *)
  `!i. MEM i (transform_block_mode dfg DloadMerge bb3).bb_instructions /\
       i.inst_opcode = mode_load_opcode Mem2Mem /\ i.inst_outputs <> [] ==>
       MEM i (fn_insts fn)` by (
    rpt strip_tac >>
    `MEM i bb3.bb_instructions` by (
      match_mp_tac mode_load_passthrough >>
      qexistsl_tac [`dfg`, `Mem2Mem`, `DloadMerge`] >>
      simp[TypeBase.distinct_of ``:merge_mode``]) >>
    metis_tac[]) >>
  qabbrev_tac `bb4 = transform_block_mode dfg DloadMerge bb3` >>
  (* Step 5: Mem2Mem *)
  mp_tac (Q.SPECL [`fn`, `dfg`, `Mem2Mem`, `bb4`, `term`] mode_step_wf) >>
  SIMP_TAC std_ss [LET_THM] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  (* Final: goal is bb_well_formed (transform_block dfg bb).
     Expand transform_block in goal, expand let bindings, expand Abbrevs, match. *)
  PURE_ONCE_REWRITE_TAC [transform_block_def] >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  qunabbrev_tac `bb4` >> qunabbrev_tac `bb3` >>
  qunabbrev_tac `bb2` >> qunabbrev_tac `bb1` >>
  qunabbrev_tac `dfg` >>
  first_x_assum ACCEPT_TAC
QED

(* fmt_preserves_wf_function variant with MEM bb fn.fn_blocks *)
Theorem fmt_preserves_wf_function_mem[local]:
  !bt fn.
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks /\ bb_well_formed bb ==> bb_well_formed (bt bb)) /\
    (!bb. MEM bb fn.fn_blocks /\ bb_well_formed bb ==> bb_succs (bt bb) = bb_succs bb) /\
    fn_inst_ids_distinct (function_map_transform bt fn)
    ==>
    wf_function fn ==> wf_function (function_map_transform bt fn)
Proof
  rw[wf_function_def, function_map_transform_def] >>
  gvs[fn_labels_def, MAP_MAP_o, fn_has_entry_def,
      MEM_MAP, fn_succs_closed_def, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[] >> res_tac >> metis_tac[]
QED

Theorem mm_preserves_wf_function:
  ∀fn. fn_inst_wf fn ∧ wf_function fn ∧ ssa_form fn ∧
       fn_inst_ids_distinct (transform_function fn) ⇒
       wf_function (transform_function fn)
Proof
  rpt strip_tac >>
  `transform_function fn =
   function_map_transform (transform_block (dfg_build_function fn)) fn`
    by simp[transform_function_eq] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule fmt_preserves_wf_function_mem >>
  simp[transform_block_label] >> rpt conj_tac
  >- (rpt strip_tac >> irule transform_block_wf >>
      fs[wf_function_def])
  >- (rpt strip_tac >> irule transform_block_succs >>
      fs[wf_function_def])
  >> fs[GSYM transform_function_eq]
QED
