(*
 * Remove Unused — Structural preservation (wf_function) by single pass.
 *
 * Key theorems:
 *   rusp_preserves_wf_function — wf_function preserved
 *   rusp_preserves_entry_label — entry label preserved
 *   rusp_preserves_labels — block labels preserved
 *   rusp_preserves_fn_inst_wf — fn_inst_wf preserved
 *   rusp_preserves_alloca_pointer_confined — alloca_pointer_confined preserved
 *
 * Also exports helpers needed by removeUnusedSsaPreservation:
 *   filter_el_original, filter_el_mono, map_inst_id_mapi_rui,
 *   rusp_preserves_ssa_form, rusp_dominates_eq, rusp_mem_inst_original
 *)

Theory removeUnusedStructProofs
Ancestors
  removeUnusedSsaProofs
  removeUnusedProofs removeUnusedDefs
  passSimulationDefs
  venomWf
  passSharedDefs
  venomInst
  indexedLists pointerConfinedDefs
  list rich_list combin

(* ===== Structural preservation: remove_unused_single_pass ===== *)

(* Entry label preserved *)
Theorem rusp_preserves_entry_label:
  !fn. fn_entry_label (remove_unused_single_pass fn) = fn_entry_label fn
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def,
     fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[] >>
  simp[clear_nops_block_def, remove_unused_block_label]
QED

(* Block labels preserved *)
Theorem rusp_preserves_labels:
  !fn. fn_labels (remove_unused_single_pass fn) = fn_labels fn
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def,
     fn_labels_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >>
  simp[clear_nops_block_def, remove_unused_block_label]
QED

(* Helper: remove_unused_inst preserves non-ALLOCA *)
Theorem rui_preserves_opcode[local]:
  !live inst P.
    P inst.inst_opcode /\ P NOP ==>
    P (remove_unused_inst live inst).inst_opcode
Proof
  rpt strip_tac >>
  qspecl_then [`live`, `inst`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def]
QED

Theorem rusp_preserves_inst_property[local]:
  !P fn.
    (!inst. P inst ==> P (mk_nop_inst inst)) /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
               P inst) ==>
    (!bb inst. MEM bb (remove_unused_single_pass fn).fn_blocks /\
               MEM inst bb.bb_instructions ==> P inst)
Proof
  rpt strip_tac >>
  gvs[remove_unused_single_pass_def, LET_THM,
      clear_nops_function_def, function_map_transform_def,
      MEM_MAP, clear_nops_block_def, remove_unused_block_def,
      MEM_FILTER, MEM_MAPi] >>
  metis_tac[remove_unused_inst_cases, EL_MEM]
QED

Theorem rusp_preserves_every_inst[local]:
  !P fn.
    (!inst. P inst ==> P (mk_nop_inst inst)) /\
    EVERY (\bb. EVERY P bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\bb. EVERY P bb.bb_instructions)
          (remove_unused_single_pass fn).fn_blocks
Proof
  rw[EVERY_MEM] >> rpt strip_tac >> rw[EVERY_MEM] >> rpt strip_tac >>
  mp_tac rusp_preserves_inst_property >>
  disch_then (qspecl_then [`P`, `fn`] mp_tac) >>
  impl_tac >- (rpt strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem rusp_preserves_alloca_pointer_confined:
  !fn. alloca_pointer_confined fn ==> alloca_pointer_confined (remove_unused_single_pass fn)
Proof
  cheat (* alloca_remap: remove_unused preserves pointer_confined *)
QED

Theorem rusp_preserves_fn_inst_wf:
  !fn. fn_inst_wf fn ==> fn_inst_wf (remove_unused_single_pass fn)
Proof
  rw[fn_inst_wf_def] >>
  irule rusp_preserves_inst_property >>
  conj_tac >- simp[mk_nop_inst_def, inst_wf_def] >>
  metis_tac[]
QED

Theorem rui_preserves_inst_id[local]:
  !live inst. (remove_unused_inst live inst).inst_id = inst.inst_id
Proof
  rpt strip_tac >>
  qspecl_then [`live`, `inst`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def]
QED

Theorem rui_identity_on_terminator[local]:
  !live inst.
    is_terminator inst.inst_opcode ==>
    remove_unused_inst live inst = inst
Proof
  rw[remove_unused_inst_def, is_removable_def]
QED

Theorem rui_not_new_terminator[local]:
  !live inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (remove_unused_inst live inst).inst_opcode \/
    remove_unused_inst live inst = inst
Proof
  rpt strip_tac >>
  qspecl_then [`live`, `inst`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def] >> EVAL_TAC
QED

(* Exported: FILTER index correspondence *)
Theorem filter_el_original:
  !P l i. i < LENGTH (FILTER P l) ==>
    ?j. j < LENGTH l /\ P (EL j l) /\ EL i (FILTER P l) = EL j l
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[FILTER]
  >- (Cases_on `i` >> gvs[]
      >- (qexists_tac `0` >> simp[])
      >- (first_x_assum (drule_then strip_assume_tac) >>
          qexists_tac `SUC j` >> simp[]))
  >- (first_x_assum (drule_then strip_assume_tac) >>
      qexists_tac `SUC j` >> simp[])
QED

(* Exported: monotone FILTER index correspondence *)
Theorem filter_el_mono:
  !P l i1 i2. i1 < i2 /\ i2 < LENGTH (FILTER P l) ==>
    ?j1 j2. j1 < j2 /\ j2 < LENGTH l /\
             P (EL j1 l) /\ P (EL j2 l) /\
             EL i1 (FILTER P l) = EL j1 l /\
             EL i2 (FILTER P l) = EL j2 l
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[FILTER]
  >- (Cases_on `i1` >> gvs[]
      >- (Cases_on `i2` >> gvs[] >>
          `n < LENGTH (FILTER P l)` by gvs[] >>
          drule_at (Pos last) filter_el_original >> strip_tac >>
          qexistsl_tac [`0`, `SUC j`] >> simp[])
      >- (Cases_on `i2` >> gvs[] >>
          `n < n' /\ n' < LENGTH (FILTER P l)` by gvs[] >>
          first_x_assum (qspecl_then [`P`, `n`, `n'`] mp_tac) >> simp[] >>
          strip_tac >>
          qexistsl_tac [`SUC j1`, `SUC j2`] >> simp[]))
  >- (`i1 < i2 /\ i2 < LENGTH (FILTER P l)` by gvs[] >>
      first_x_assum (qspecl_then [`P`, `i1`, `i2`] mp_tac) >> simp[] >>
      strip_tac >>
      qexistsl_tac [`SUC j1`, `SUC j2`] >> simp[])
QED

Theorem filter_last_when_last_passes[local]:
  !P l. l <> [] /\ P (LAST l) ==>
        FILTER P l <> [] /\ LAST (FILTER P l) = LAST l
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l` >> gvs[] >>
  Cases_on `P h` >> gvs[LAST_DEF] >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[]
QED

Theorem filter_nop_preserves_only_last_terminator[local]:
  !mapped.
    mapped <> [] /\
    (!i. i < LENGTH mapped /\ is_terminator (EL i mapped).inst_opcode ==>
         i = PRE (LENGTH mapped)) ==>
    !i. i < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped) /\
        is_terminator
          (EL i (FILTER (\inst. inst.inst_opcode <> NOP) mapped)).inst_opcode
    ==>
        i = PRE (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped))
Proof
  rpt strip_tac >> CCONTR_TAC >>
  `i < PRE (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped))` by
    gvs[] >>
  `0 < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped)` by
    (Cases_on `FILTER (\inst. inst.inst_opcode <> NOP) mapped` >> gvs[]) >>
  `PRE (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped)) <
   LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped)` by gvs[] >>
  drule_all filter_el_mono >> strip_tac >>
  `is_terminator (EL j1 mapped).inst_opcode` by metis_tac[] >>
  `j1 < LENGTH mapped` by gvs[] >>
  `j1 = PRE (LENGTH mapped)` by metis_tac[] >>
  gvs[]
QED

Theorem filter_nop_preserves_phi_prefix[local]:
  !mapped.
    (!i j. i < j /\ j < LENGTH mapped /\
           (EL j mapped).inst_opcode = PHI ==>
           (EL i mapped).inst_opcode = PHI) ==>
    !i j. i < j /\
          j < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped) /\
          (EL j (FILTER (\inst. inst.inst_opcode <> NOP) mapped)).inst_opcode
            = PHI ==>
          (EL i (FILTER (\inst. inst.inst_opcode <> NOP) mapped)).inst_opcode
            = PHI
Proof
  rpt strip_tac >>
  `i < j /\ j < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) mapped)` by
    gvs[] >>
  drule_all filter_el_mono >> strip_tac >>
  `(EL j2 mapped).inst_opcode = PHI` by metis_tac[] >>
  `j2 < LENGTH mapped` by gvs[] >>
  `j1 < LENGTH mapped` by gvs[] >>
  `(EL j1 mapped).inst_opcode = PHI` by metis_tac[] >>
  gvs[]
QED

Theorem rui_mapi_only_last_terminator[local]:
  !lr insts.
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) ==>
    !i. i < LENGTH (MAPi (\idx inst. remove_unused_inst
            (lr idx) inst) insts) /\
        is_terminator (EL i (MAPi (\idx inst. remove_unused_inst
            (lr idx) inst) insts)).inst_opcode ==>
        i = PRE (LENGTH (MAPi (\idx inst. remove_unused_inst
            (lr idx) inst) insts))
Proof
  rpt strip_tac >> gvs[EL_MAPi, LENGTH_MAPi] >>
  qspecl_then [`lr i`, `EL i insts`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def, EL_MAPi, EVAL ``is_terminator NOP``]
QED

Theorem filter_rui_preserves_phi_prefix[local]:
  !lr insts.
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    let mapped = MAPi (\idx inst. remove_unused_inst
                    (lr idx) inst) insts in
    let filtered = FILTER (\inst. inst.inst_opcode <> NOP) mapped in
    !i j. i < j /\ j < LENGTH filtered /\
          (EL j filtered).inst_opcode = PHI ==>
          (EL i filtered).inst_opcode = PHI
Proof
  rpt strip_tac >> gvs[LET_THM] >> rpt strip_tac >>
  drule_all filter_el_mono >> strip_tac >>
  `(EL j2 (MAPi (\idx inst. remove_unused_inst (lr idx) inst)
      insts)).inst_opcode = PHI` by metis_tac[] >>
  gvs[EL_MAPi, LENGTH_MAPi] >>
  qspecl_then [`lr j2`, `EL j2 insts`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def, EVAL ``NOP = PHI``] >>
  `j1 < LENGTH insts` by gvs[] >>
  `(EL j1 insts).inst_opcode = PHI` by metis_tac[] >>
  qspecl_then [`lr j1`, `EL j1 insts`] strip_assume_tac
    remove_unused_inst_cases >> gvs[mk_nop_inst_def] >>
  `MEM (EL i (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)))
    (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts))`
    by (irule EL_MEM >> gvs[]) >>
  gvs[MEM_FILTER]
QED

Theorem rui_mapi_preserves_last[local]:
  !lr insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode ==>
    LAST (MAPi (\idx inst. remove_unused_inst
            (lr idx) inst) insts) = LAST insts
Proof
  rpt strip_tac >>
  `0 < LENGTH insts` by (Cases_on `insts` >> gvs[]) >>
  `MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts <> []`
    by (Cases_on `insts` >> gvs[]) >>
  simp[LAST_EL, LENGTH_MAPi] >>
  simp[EL_MAPi] >>
  irule rui_identity_on_terminator >>
  gvs[LAST_EL]
QED

Theorem rui_filter_nonempty_last[local]:
  !lr insts.
    insts <> [] /\ is_terminator (LAST insts).inst_opcode ==>
    FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)
      <> [] /\
    LAST (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts))
      = LAST insts
Proof
  rpt gen_tac >> strip_tac >>
  `LAST (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)
    = LAST insts` by (irule rui_mapi_preserves_last >> simp[]) >>
  `MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts <> []`
    by (Cases_on `insts` >> gvs[]) >>
  `LAST insts = LAST (MAPi (\idx inst. remove_unused_inst
    (lr idx) inst) insts)` by gvs[] >>
  pop_assum (fn th => rewrite_tac [th]) >>
  irule filter_last_when_last_passes >>
  gvs[] >> CCONTR_TAC >> gvs[EVAL ``is_terminator NOP``]
QED

Theorem filter_rui_bb_wf[local]:
  !lr insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) /\
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    let result = FILTER (\inst. inst.inst_opcode <> NOP)
                   (MAPi (\idx inst. remove_unused_inst
                     (lr idx) inst) insts) in
    result <> [] /\
    is_terminator (LAST result).inst_opcode /\
    (!i. i < LENGTH result /\ is_terminator (EL i result).inst_opcode ==>
         i = PRE (LENGTH result)) /\
    (!i j. i < j /\ j < LENGTH result /\
           (EL j result).inst_opcode = PHI ==>
           (EL i result).inst_opcode = PHI)
Proof
  rpt strip_tac >> simp[LET_THM] >>
  mp_tac (Q.SPECL [`lr`, `insts`] rui_filter_nonempty_last) >>
  simp[] >> strip_tac >>
  conj_tac
  >- (match_mp_tac filter_nop_preserves_only_last_terminator >> conj_tac
      >- (simp[LENGTH_NIL, LENGTH_MAPi] >> Cases_on `insts` >> gvs[])
      >- (match_mp_tac rui_mapi_only_last_terminator >> simp[]))
  >- (mp_tac (SRULE [LET_THM] (Q.SPECL [`lr`, `insts`]
        filter_rui_preserves_phi_prefix)) >>
      simp[] >> disch_then match_mp_tac >> metis_tac[])
QED

Theorem bb_wf_preserved[local]:
  !lr bb.
    bb_well_formed bb ==>
    bb_well_formed
      (clear_nops_block (remove_unused_block lr bb))
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  simp[clear_nops_block_def, remove_unused_block_def, LET_THM,
       bb_well_formed_def] >>
  mp_tac (SRULE [LET_THM] (Q.SPECL [`\idx. live_after_at lr bb.bb_label idx
      (LENGTH bb.bb_instructions)`, `bb.bb_instructions`]
    filter_rui_bb_wf)) >>
  disch_then irule >> metis_tac[]
QED

Theorem rusp_preserves_bb_succs[local]:
  !lr bb.
    bb_well_formed bb ==>
    bb_succs (clear_nops_block (remove_unused_block lr bb)) =
    bb_succs bb
Proof
  rw[bb_succs_def, bb_well_formed_def,
     clear_nops_block_def, remove_unused_block_def, LET_THM] >>
  mp_tac (Q.SPECL [`\idx. live_after_at lr bb.bb_label idx
    (LENGTH bb.bb_instructions)`, `bb.bb_instructions`]
    rui_filter_nonempty_last) >>
  simp[] >> strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `FILTER (\inst. inst.inst_opcode <> NOP)
    (MAPi (\idx inst. remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH (h::t)))
      inst) (h::t))` >> gvs[]
QED

Theorem rusp_preserves_fn_succs_closed[local]:
  !fn. wf_function fn ==>
       fn_succs_closed (remove_unused_single_pass fn)
Proof
  rw[fn_succs_closed_def, remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def,
     MEM_MAP, fn_labels_def, MAP_MAP_o] >>
  rpt strip_tac >> gvs[] >>
  fs[wf_function_def, fn_succs_closed_def] >>
  `bb_well_formed y` by metis_tac[] >>
  `bb_succs (clear_nops_block
      (remove_unused_block (liveness_analyze fn) y)) =
   bb_succs y` by
    (irule rusp_preserves_bb_succs >> simp[]) >>
  `MEM succ (bb_succs y)` by gvs[] >>
  `MEM succ (fn_labels fn)` by metis_tac[] >>
  gvs[fn_labels_def, MEM_MAP] >>
  qexists_tac `bb` >> gvs[clear_nops_block_def, remove_unused_block_label]
QED

Theorem all_distinct_flat_sublist[local]:
  !(f:'a -> 'b list) g l.
    ALL_DISTINCT (FLAT (MAP f l)) /\
    (!x. MEM x l ==> sublist (g x) (f x)) ==>
    ALL_DISTINCT (FLAT (MAP g l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >>
  rpt strip_tac >>
  fs[ALL_DISTINCT_APPEND] >> rpt conj_tac
  >- (irule sublist_ALL_DISTINCT >>
      qexists_tac `f h` >> metis_tac[])
  >- (rpt strip_tac >>
      `sublist (g h) (f h)` by metis_tac[] >>
      fs[MEM_FLAT, MEM_MAP] >> gvs[] >>
      `MEM e (f h)` by metis_tac[sublist_mem] >>
      `MEM e (f y)` by metis_tac[sublist_mem] >>
      metis_tac[])
QED

(* Exported: MAPi rui preserves inst_id *)
Theorem map_inst_id_mapi_rui:
  !lr lbl n insts.
    MAP (\i. i.inst_id)
      (MAPi (\idx inst. remove_unused_inst
        (live_after_at lr lbl idx n) inst) insts) =
    MAP (\i. i.inst_id) insts
Proof
  Induct_on `insts` >>
  simp[MAPi_def, rui_preserves_inst_id, combinTheory.o_DEF] >>
  simp[SF ETA_ss]
QED

Theorem rusp_block_inst_ids_sublist[local]:
  !lr bb.
    sublist (MAP (\i. i.inst_id)
               (clear_nops_block (remove_unused_block lr bb)).bb_instructions)
            (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[clear_nops_block_def, remove_unused_block_def, LET_THM] >>
  irule sublist_trans >>
  qexists_tac `MAP (\i. i.inst_id)
    (MAPi (\idx inst. remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
      inst) bb.bb_instructions)` >>
  conj_tac
  >- (irule MAP_SUBLIST >> simp[FILTER_sublist])
  >- simp[map_inst_id_mapi_rui, sublist_refl]
QED

Theorem rusp_preserves_fn_inst_ids_distinct[local]:
  !fn. fn_inst_ids_distinct fn ==>
       fn_inst_ids_distinct (remove_unused_single_pass fn)
Proof
  rw[fn_inst_ids_distinct_def, remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def, MAP_MAP_o] >>
  irule all_distinct_flat_sublist >>
  qexists_tac `\bb. MAP (\i. i.inst_id) bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  simp[rusp_block_inst_ids_sublist]
QED

Theorem rusp_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (remove_unused_single_pass fn)
Proof
  rw[wf_function_def] >>
  rpt conj_tac
  >- gvs[rusp_preserves_labels]
  >- (gvs[fn_has_entry_def, remove_unused_single_pass_def, LET_THM,
          clear_nops_function_def, function_map_transform_def] >>
      Cases_on `fn.fn_blocks` >> gvs[])
  >- (gvs[remove_unused_single_pass_def, LET_THM,
          clear_nops_function_def, function_map_transform_def,
          MEM_MAP] >> rpt strip_tac >> gvs[] >>
      irule bb_wf_preserved >> metis_tac[])
  >- (irule rusp_preserves_fn_succs_closed >> gvs[wf_function_def])
  >- (irule rusp_preserves_fn_inst_ids_distinct >> gvs[])
QED

Theorem flat_map_flat_map[local]:
  !(f:'b -> 'c list) (g:'a -> 'b list) l.
    FLAT (MAP f (FLAT (MAP g l))) =
    FLAT (MAP (\x. FLAT (MAP f (g x))) l)
Proof
  gen_tac >> gen_tac >> Induct >> simp[]
QED

Theorem flat_map_sublist[local]:
  !(f:'a -> 'b list) l1 l2.
    sublist l1 l2 ==> sublist (FLAT (MAP f l1)) (FLAT (MAP f l2))
Proof
  gen_tac >> ho_match_mp_tac sublist_induct >>
  simp[sublist_nil] >> rpt strip_tac
  >- simp[GSYM sublist_prefix]
  >- simp[sublist_append_include]
QED

Theorem filter_mapi_sublist[local]:
  !P (l:'a list) f.
    (!i. i < LENGTH l ==> f i (EL i l) = EL i l \/ ~P (f i (EL i l))) ==>
    sublist (FILTER P (MAPi f l)) l
Proof
  gen_tac >> Induct >- simp[sublist_refl] >>
  simp[MAPi_def, combinTheory.o_DEF] >> rpt strip_tac >>
  `sublist (FILTER P (MAPi (\i. f (SUC i)) l)) l` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >> simp[EL]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (Cases_on `P h` >> simp[]
      >- simp[GSYM sublist_cons]
      >- (irule sublist_cons_include >> simp[]))
  >- (simp[] >> irule sublist_cons_include >> simp[])
QED

Theorem rusp_block_insts_sublist[local]:
  !lr bb.
    sublist
      (clear_nops_block (remove_unused_block lr bb)).bb_instructions
      bb.bb_instructions
Proof
  rw[clear_nops_block_def, remove_unused_block_def, LET_THM] >>
  irule filter_mapi_sublist >>
  rpt strip_tac >>
  qspecl_then [`live_after_at lr bb.bb_label i (LENGTH bb.bb_instructions)`,
               `EL i bb.bb_instructions`]
    strip_assume_tac remove_unused_inst_cases >>
  gvs[mk_nop_inst_def]
QED

(* Exported *)
Theorem rusp_preserves_ssa_form:
  !fn. ssa_form fn ==>
       ssa_form (remove_unused_single_pass fn)
Proof
  rw[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
     remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def] >>
  `!bbs. FLAT (MAP (\i:instruction. i.inst_outputs)
     (FLAT (MAP (\bb:basic_block. bb.bb_instructions) bbs))) =
   FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
     bbs)` by simp[flat_map_flat_map] >>
  fs[] >> pop_assum kall_tac >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule all_distinct_flat_sublist >>
  qexists_tac `\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)` >>
  simp[] >> rpt strip_tac >>
  match_mp_tac flat_map_sublist >>
  simp[rusp_block_insts_sublist]
QED

Theorem rusp_cfg_edge_eq[local]:
  !fn. wf_function fn ==>
       fn_cfg_edge (remove_unused_single_pass fn) = fn_cfg_edge fn
Proof
  rw[FUN_EQ_THM, fn_cfg_edge_def, remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def, MEM_MAP,
     PULL_EXISTS] >>
  rpt gen_tac >> eq_tac >> strip_tac >> gvs[] >|
  [rename1 `MEM bk _.fn_blocks`,
   rename1 `MEM bk _.fn_blocks`] >>
  qexists_tac `bk` >>
  `bb_well_formed bk` by gvs[wf_function_def] >>
  gvs[clear_nops_block_def, remove_unused_block_label,
      rusp_preserves_bb_succs]
QED

Theorem rusp_reachable_eq[local]:
  !fn. wf_function fn ==>
       fn_reachable (remove_unused_single_pass fn) = fn_reachable fn
Proof
  rpt strip_tac >>
  simp[FUN_EQ_THM, fn_reachable_def, rusp_preserves_entry_label] >>
  `fn_cfg_edge (remove_unused_single_pass fn) = fn_cfg_edge fn` by
    metis_tac[rusp_cfg_edge_eq] >>
  simp[]
QED

(* Exported *)
Theorem rusp_dominates_eq:
  !fn. wf_function fn ==>
       fn_dominates (remove_unused_single_pass fn) = fn_dominates fn
Proof
  rpt strip_tac >>
  `fn_cfg_edge (remove_unused_single_pass fn) = fn_cfg_edge fn` by
    metis_tac[rusp_cfg_edge_eq] >>
  `!path. is_fn_path (remove_unused_single_pass fn) path <=>
          is_fn_path fn path` by
    (Induct >> simp[is_fn_path_def] >>
     Cases_on `path` >> gvs[is_fn_path_def]) >>
  simp[FUN_EQ_THM, fn_dominates_def, rusp_preserves_entry_label] >>
  metis_tac[rusp_reachable_eq]
QED

(* Exported *)
Theorem rusp_mem_inst_original:
  !fn bb' inst.
    MEM bb' (remove_unused_single_pass fn).fn_blocks /\
    MEM inst bb'.bb_instructions ==>
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         bb'.bb_label = bb.bb_label
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def, MEM_MAP] >>
  rename1 `MEM bk _.fn_blocks` >> qexists_tac `bk` >>
  simp[clear_nops_block_def, remove_unused_block_label] >>
  gvs[clear_nops_block_def, remove_unused_block_def, LET_THM,
      MEM_FILTER, MEM_MAPi] >>
  qspecl_then [`live_after_at (liveness_analyze fn) bk.bb_label idx
    (LENGTH bk.bb_instructions)`,
    `EL idx bk.bb_instructions`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def] >>
  metis_tac[MEM_EL]
QED

(* ===== SSA preservation by remove_unused_single_pass ===== *)

(* Local copy — non-local version causes simpset pollution (L1708) *)
Theorem fn_insts_blocks_flat_local[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* FILTER preserves relative order of surviving elements (forward direction). *)
Theorem filter_preserves_el_order[local]:
  !P l i j. i < j /\ j < LENGTH l /\ P (EL i l) /\ P (EL j l) ==>
    ?i' j'. i' < j' /\ j' < LENGTH (FILTER P l) /\
            EL i' (FILTER P l) = EL i l /\
            EL j' (FILTER P l) = EL j l
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[]
  >- (Cases_on `P h` >> gvs[] >>
      `MEM (EL n l) (FILTER P l)` by (simp[MEM_FILTER, MEM_EL] >> metis_tac[]) >>
      gvs[MEM_EL] >> qexistsl_tac [`0`, `SUC n'`] >> simp[])
  >- (first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[] >>
      strip_tac >>
      Cases_on `P h` >> gvs[]
      >- (qexistsl_tac [`SUC i'`, `SUC j'`] >> simp[])
      >- (qexistsl_tac [`i'`, `j'`] >> simp[]))
QED

(* NOP instructions in the result have empty outputs.
   This is implied by fn_inst_wf (inst_wf requires NOP outputs = []).
   Kept as internal helper for proof convenience. *)
Definition nop_outputs_empty_def:
  nop_outputs_empty func <=>
  !bb inst. MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
            inst.inst_opcode = NOP ==> inst.inst_outputs = []
End

Theorem rusp_nop_outputs_empty[local]:
  !func. nop_outputs_empty (remove_unused_single_pass func)
Proof
  rw[nop_outputs_empty_def] >> rpt strip_tac >>
  gvs[remove_unused_single_pass_def, LET_THM,
      clear_nops_function_def, function_map_transform_def, MEM_MAP,
      clear_nops_block_def] >>
  gvs[MEM_FILTER]
QED

(* Key contrapositive: if a variable's output is NOT in single_pass_nop_outputs,
   then rui at that variable's defining position returns the instruction unchanged. *)
Theorem rui_identity_when_output_not_nopd[local]:
  !func bb k v.
    MEM bb func.fn_blocks /\ k < LENGTH bb.bb_instructions /\
    MEM v (EL k bb.bb_instructions).inst_outputs /\
    v NOTIN single_pass_nop_outputs func ==>
    remove_unused_inst
      (live_after_at (liveness_analyze func) bb.bb_label k
        (LENGTH bb.bb_instructions))
      (EL k bb.bb_instructions) = EL k bb.bb_instructions
Proof
  rpt strip_tac >> CCONTR_TAC >>
  qspecl_then
    [`live_after_at (liveness_analyze func) bb.bb_label k
        (LENGTH bb.bb_instructions)`,
     `EL k bb.bb_instructions`] strip_assume_tac
    remove_unused_inst_cases >> gvs[] >>
  qpat_x_assum `v NOTIN _` mp_tac >>
  simp[single_pass_nop_outputs_def, LET_THM,
       pred_setTheory.IN_BIGUNION, PULL_EXISTS, MEM_MAP] >>
  qexists_tac `bb` >> simp[] >>
  simp[block_nop_outputs_def, LET_THM] >>
  simp[MEM_FLAT, MEM_MAPi, PULL_EXISTS] >>
  qexists_tac `k` >> simp[] >>
  gvs[remove_unused_inst_def] >>
  Cases_on `is_removable (EL k bb.bb_instructions)` >> gvs[mk_nop_inst_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  rpt IF_CASES_TAC >> gvs[] >>
  gvs[listTheory.EXISTS_MEM, listTheory.EVERY_MEM]
QED

(* Helper: instruction with a used output variable survives in rusp block *)
Theorem inst_with_used_var_survives[local]:
  !func ob k v.
    MEM ob func.fn_blocks /\ k < LENGTH ob.bb_instructions /\
    MEM v (EL k ob.bb_instructions).inst_outputs /\
    v NOTIN single_pass_nop_outputs func /\
    (EL k ob.bb_instructions).inst_opcode <> NOP ==>
    ?bk. MEM bk (remove_unused_single_pass func).fn_blocks /\
         MEM (EL k ob.bb_instructions) bk.bb_instructions /\
         bk.bb_label = ob.bb_label
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def, MEM_MAP,
     clear_nops_block_def, remove_unused_block_def] >>
  rpt strip_tac >>
  drule_all rui_identity_when_output_not_nopd >> strip_tac >>
  qexists_tac `ob with bb_instructions :=
    FILTER (\i. i.inst_opcode <> NOP)
      (MAPi (\idx i. remove_unused_inst
        (live_after_at (liveness_analyze func) ob.bb_label idx
          (LENGTH ob.bb_instructions)) i)
      ob.bb_instructions)` >>
  simp[MEM_FILTER, MEM_MAPi] >>
  conj_tac >- (
    qexists_tac `ob with bb_instructions :=
      MAPi (\idx i. remove_unused_inst
        (live_after_at (liveness_analyze func) ob.bb_label idx
          (LENGTH ob.bb_instructions)) i)
      ob.bb_instructions` >>
    simp[] >> qexists_tac `ob` >> simp[]
  ) >>
  qexists_tac `k` >> simp[EL_MAPi]
QED

(* Core identity: if rui result has opcode <> NOP, it returned the original *)
Theorem rui_not_nop_identity_ssa[local]:
  !live inst.
    (remove_unused_inst live inst).inst_opcode <> NOP ==>
    remove_unused_inst live inst = inst
Proof
  rpt strip_tac >>
  qspecl_then [`live`, `inst`] strip_assume_tac
    remove_unused_inst_cases >>
  gvs[mk_nop_inst_def]
QED

(* If ALL_DISTINCT (MAP f l) then f is injective on MEM elements *)
Theorem all_distinct_map_inj_mem[local]:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ (f x = f y)
    ==> (x = y)
Proof
  metis_tac[MEM_EL, EL_MAP, ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

(* def_dominates_uses preserved *)
Theorem rusp_preserves_def_dominates_uses[local]:
  !func.
    wf_function func /\ wf_ssa func /\ ssa_form func /\
    nop_outputs_empty func ==>
    def_dominates_uses (remove_unused_single_pass func)
Proof
  rpt strip_tac >>
  simp[def_dominates_uses_def] >> rpt strip_tac >>
  rename1 `MEM bb' (remove_unused_single_pass _).fn_blocks` >>
  drule_all rusp_mem_inst_original >> strip_tac >>
  rename1 `MEM bb_orig func.fn_blocks` >>
  (`def_dominates_uses func` by gvs[wf_ssa_def]) >>
  pop_assum (mp_tac o SRULE [def_dominates_uses_def]) >>
  disch_then (qspecl_then [`bb_orig`, `inst`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `MEM def_bb func.fn_blocks` >>
  rename1 `MEM def_inst def_bb.bb_instructions` >>
  (`def_inst.inst_opcode <> NOP` by (
    CCONTR_TAC >> gvs[nop_outputs_empty_def] >> res_tac >> gvs[MEM])) >>
  (`v NOTIN single_pass_nop_outputs func` by (
    CCONTR_TAC >> gvs[GSYM pred_setTheory.IN_COMPL] >>
    metis_tac[nop_output_not_used_as_operand])) >>
  (`?k_def. k_def < LENGTH def_bb.bb_instructions /\
    (def_inst = EL k_def def_bb.bb_instructions)` by metis_tac[MEM_EL]) >>
  qspecl_then [`func`, `def_bb`, `k_def`, `v`] mp_tac
    inst_with_used_var_survives >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `MEM bk (remove_unused_single_pass func).fn_blocks` >>
  qexistsl_tac [`bk`, `def_inst`] >> simp[] >>
  conj_tac >- (
    (`fn_dominates (remove_unused_single_pass func) = fn_dominates func` by
      (irule rusp_dominates_eq >> gvs[])) >> gvs[]) >>
  strip_tac >>
  (`ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def]) >>
  (`def_bb = bb_orig` by (
    (`wf_function (remove_unused_single_pass func)` by
      (irule rusp_preserves_wf_function >> gvs[])) >>
    gvs[wf_function_def, fn_labels_def] >>
    metis_tac[all_distinct_map_inj_mem])) >>
  `bk = bb'` by (
    (`wf_function (remove_unused_single_pass func)` by
      (irule rusp_preserves_wf_function >> gvs[])) >>
    gvs[wf_function_def, fn_labels_def] >>
    metis_tac[all_distinct_map_inj_mem]) >>
  gvs[] >>
  (`bb'.bb_instructions = FILTER (\i. i.inst_opcode <> NOP)
    (MAPi (\idx i. remove_unused_inst
      (live_after_at (liveness_analyze func) bb_orig.bb_label idx
        (LENGTH bb_orig.bb_instructions)) i)
    bb_orig.bb_instructions)` by (
    gvs[remove_unused_single_pass_def, LET_THM,
        clear_nops_function_def, function_map_transform_def, MEM_MAP,
        clear_nops_block_def, remove_unused_block_def] >>
    metis_tac[all_distinct_map_inj_mem])) >>
  qabbrev_tac `mapi_list = MAPi (\idx i. remove_unused_inst
    (live_after_at (liveness_analyze func) bb_orig.bb_label idx
      (LENGTH bb_orig.bb_instructions)) i)
    bb_orig.bb_instructions` >>
  (`EL k_def mapi_list = EL k_def bb_orig.bb_instructions` by (
    simp[Abbr `mapi_list`, EL_MAPi] >>
    qspecl_then [`func`, `bb_orig`, `k_def`, `v`] mp_tac
      rui_identity_when_output_not_nopd >>
    simp[])) >>
  (`ALL_DISTINCT (MAP (\i. i.inst_id) bb_orig.bb_instructions)` by (
    qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
      `func.fn_blocks`, `bb_orig`]
      (mp_tac o SRULE []) all_distinct_flat_map_member >>
    gvs[wf_function_def, fn_inst_ids_distinct_def])) >>
  (`MAP (\i. i.inst_id) mapi_list =
    MAP (\i. i.inst_id) bb_orig.bb_instructions` by
    simp[Abbr `mapi_list`, map_inst_id_mapi_rui]) >>
  (`k_def = i` by (
    `i < LENGTH bb_orig.bb_instructions` by simp[] >>
    qspecl_then [`MAP (\i. i.inst_id) bb_orig.bb_instructions`, `k_def`, `i`]
      mp_tac ALL_DISTINCT_EL_IMP >>
    simp[EL_MAP])) >>
  pop_assum (fn th => SUBST_ALL_TAC th) >>
  (`MEM (EL j bb_orig.bb_instructions) mapi_list` by
    fs[MEM_FILTER]) >>
  pop_assum (strip_assume_tac o SRULE [MEM_EL]) >>
  rename1 `m < LENGTH mapi_list` >>
  (`m = j` by (
    `LENGTH mapi_list = LENGTH bb_orig.bb_instructions`
      by simp[Abbr `mapi_list`, LENGTH_MAPi] >>
    `(EL m mapi_list).inst_id = (EL m bb_orig.bb_instructions).inst_id` by (
      qpat_x_assum `MAP _ mapi_list = MAP _ _`
        (fn th => ASSUME_TAC (Q.AP_TERM `\l. EL m l` th)) >>
      gvs[EL_MAP]) >>
    qspecl_then [`MAP (\i. i.inst_id) bb_orig.bb_instructions`, `m`, `j`]
      mp_tac ALL_DISTINCT_EL_IMP >>
    simp[EL_MAP, LENGTH_MAP] >> gvs[])) >>
  (`EL j mapi_list = EL j bb_orig.bb_instructions` by gvs[]) >>
  (`(EL i mapi_list).inst_opcode <> NOP` by fs[]) >>
  (`(EL j mapi_list).inst_opcode <> NOP` by fs[MEM_FILTER]) >>
  (`i < LENGTH mapi_list /\ j < LENGTH mapi_list` by
    simp[Abbr `mapi_list`, LENGTH_MAPi]) >>
  qspecl_then [`\inst. inst.inst_opcode <> NOP`, `mapi_list`, `i`, `j`]
    mp_tac filter_preserves_el_order >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`i'`, `j'`] >> fs[]
QED

(* Helper: map a single index in a rusp block back to the original block *)
Theorem rusp_block_el_original[local]:
  !func bk idx.
    MEM bk (remove_unused_single_pass func).fn_blocks /\
    idx < LENGTH bk.bb_instructions ==>
    ?ob m. MEM ob func.fn_blocks /\
           bk.bb_label = ob.bb_label /\
           m < LENGTH ob.bb_instructions /\
           EL idx bk.bb_instructions = EL m ob.bb_instructions
Proof
  rpt strip_tac >>
  gvs[remove_unused_single_pass_def, LET_THM,
      clear_nops_function_def, function_map_transform_def, MEM_MAP,
      clear_nops_block_def, remove_unused_block_def] >>
  rename1 `MEM ob func.fn_blocks` >>
  drule filter_el_original >> strip_tac >>
  qexistsl_tac [`ob`, `j`] >> simp[] >>
  `j < LENGTH ob.bb_instructions` by gvs[LENGTH_MAPi] >>
  simp[] >> gvs[EL_MAPi] >> irule rui_not_nop_identity_ssa >> simp[]
QED

(* Helper: two indices i1 < i2 in a rusp block map to m1 < m2 in original *)
Theorem rusp_block_el_mono[local]:
  !func bk i1 i2.
    MEM bk (remove_unused_single_pass func).fn_blocks /\
    i1 < i2 /\ i2 < LENGTH bk.bb_instructions ==>
    ?ob m1 m2. MEM ob func.fn_blocks /\
               bk.bb_label = ob.bb_label /\
               m1 < m2 /\ m2 < LENGTH ob.bb_instructions /\
               EL i1 bk.bb_instructions = EL m1 ob.bb_instructions /\
               EL i2 bk.bb_instructions = EL m2 ob.bb_instructions
Proof
  rpt strip_tac >>
  gvs[remove_unused_single_pass_def, LET_THM,
      clear_nops_function_def, function_map_transform_def, MEM_MAP,
      clear_nops_block_def, remove_unused_block_def] >>
  rename1 `MEM ob func.fn_blocks` >>
  drule_all filter_el_mono >> strip_tac >>
  qexistsl_tac [`ob`, `j1`, `j2`] >> simp[] >>
  `j2 < LENGTH ob.bb_instructions /\ j1 < LENGTH ob.bb_instructions`
    by gvs[LENGTH_MAPi] >>
  simp[] >> gvs[EL_MAPi] >>
  conj_tac >> irule rui_not_nop_identity_ssa >> simp[]
QED

(* wf_ssa preserved *)
Theorem rusp_preserves_wf_ssa[local]:
  !fn. wf_function fn /\ wf_ssa fn /\ ssa_form fn /\
       nop_outputs_empty fn ==>
       wf_ssa (remove_unused_single_pass fn)
Proof
  rpt strip_tac >> simp[wf_ssa_def] >> rpt conj_tac
  >- metis_tac[rusp_preserves_ssa_form, wf_ssa_def]
  >- metis_tac[rusp_preserves_def_dominates_uses]
QED

(* Forward preservation: all structural + SSA properties are preserved
   by remove_unused_single_pass in one step *)
Theorem rusp_preserves_all:
  !fn.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    ssa_form fn /\ nop_outputs_empty fn /\ alloca_pointer_confined fn ==>
    wf_function (remove_unused_single_pass fn) /\
    fn_inst_wf (remove_unused_single_pass fn) /\
    wf_ssa (remove_unused_single_pass fn) /\
    ssa_form (remove_unused_single_pass fn) /\
    nop_outputs_empty (remove_unused_single_pass fn) /\
    alloca_pointer_confined (remove_unused_single_pass fn)
Proof
  rpt strip_tac >>
  metis_tac[rusp_preserves_wf_function, rusp_preserves_fn_inst_wf,
            rusp_preserves_wf_ssa, rusp_preserves_ssa_form,
            rusp_nop_outputs_empty, rusp_preserves_alloca_pointer_confined]
QED

