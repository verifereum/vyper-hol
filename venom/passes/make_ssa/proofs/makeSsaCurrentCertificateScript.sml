Theory makeSsaCurrentCertificate
Ancestors
  makeSsaCurrentRenameTrace makeSsaCurrentPlacementCut makeSsaCurrentTokens
  makeSsaDefs makeSsaCurrentPlacement makeSsaCurrentProps
  venomInst list rich_list combin

(* Original indices are counted in the source suffix, never in the inserted
   prefix. Owners are kept independently of concrete output spellings. *)
Definition current_original_outputs_def:
  (current_original_outputs l i j [] = []) /\
  (current_original_outputs l i j (v::vs) =
    (CurrentOriginal l i j,v)::current_original_outputs l i (SUC j) vs)
End

Definition current_original_annotations_def:
  (current_original_annotations l i [] = []) /\
  (current_original_annotations l i (inst::insts) =
    current_original_outputs l i 0 inst.inst_outputs ::
      current_original_annotations l (SUC i) insts)
End

Definition current_inserted_annotations_def:
  current_inserted_annotations l pre =
    MAP (\inst. MAP (\v. (CurrentInserted v l,v)) inst.inst_outputs) pre
End

Definition current_block_annotations_def:
  current_block_annotations old pre =
    current_inserted_annotations old.bb_label pre ++
    current_original_annotations old.bb_label 0 old.bb_instructions
End

Theorem current_original_outputs_owners[simp]:
  !vs j. MAP SND (current_original_outputs l i j vs) = vs
Proof
  Induct >> simp[current_original_outputs_def]
QED

Theorem current_original_annotations_owners:
  !insts i. LIST_REL (\inst anns. MAP SND anns = inst.inst_outputs)
    insts (current_original_annotations l i insts)
Proof
  Induct >> simp[current_original_annotations_def]
QED

Theorem current_inserted_annotations_owners:
  LIST_REL (\inst anns. MAP SND anns = inst.inst_outputs)
    pre (current_inserted_annotations l pre)
Proof
  simp[current_inserted_annotations_def] >>
  Induct_on `pre` >> simp[MAP_MAP_o, o_DEF]
QED

Theorem current_block_annotations_owners:
  new = old with bb_instructions := pre ++ old.bb_instructions ==>
  LIST_REL (\inst anns. MAP SND anns = inst.inst_outputs)
    new.bb_instructions (current_block_annotations old pre)
Proof
  strip_tac >> simp[current_block_annotations_def, LIST_REL_APPEND_suff,
    current_original_annotations_owners, current_inserted_annotations_owners]
QED

Theorem current_original_outputs_scan:
  !vs j E. FOLDL (\env (t,w). (w =+ t) env) E
    (current_original_outputs l i j vs) v =
    current_output_token v l i j vs (E v)
Proof
  Induct >> simp[current_original_outputs_def, current_output_token_def] >>
  rpt gen_tac >> simp[APPLY_UPDATE_THM] >> Cases_on `h = v` >> simp[]
QED

Theorem current_original_annotations_scan:
  !insts i E. FOLDL (\env (t,w). (w =+ t) env) E
    (FLAT (current_original_annotations l i insts)) v =
    current_original_scan v l i insts (E v)
Proof
  Induct >> simp[current_original_annotations_def, current_original_scan_def,
    rich_listTheory.FOLDL_APPEND, current_original_outputs_scan]
QED

Theorem current_inserted_outputs_scan:
  !vs E. FOLDL (\env (t,w). (w =+ t) env) E
    (MAP (\w. (CurrentInserted w l,w)) vs) v =
    if MEM v vs then CurrentInserted v l else E v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `MEM v vs` >> simp[APPLY_UPDATE_THM] >>
  Cases_on `h = v` >> simp[]
QED

Theorem current_inserted_annotations_scan:
  !pre E. FOLDL (\env (t,w). (w =+ t) env) E
    (FLAT (current_inserted_annotations l pre)) v =
    if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
      then CurrentInserted v l else E v
Proof
  simp[current_inserted_annotations_def] >> Induct >>
  simp[rich_listTheory.FOLDL_APPEND, current_inserted_outputs_scan] >>
  rpt gen_tac >> Cases_on `?inst. MEM inst pre /\ MEM v inst.inst_outputs` >>
  simp[] >> metis_tac[]
QED

Theorem current_block_annotations_scan:
  (!v. inserted v old.bb_label <=>
    ?inst. MEM inst pre /\ MEM v inst.inst_outputs) ==>
  FOLDL (\env (t,w). (w =+ t) env) E
    (FLAT (current_block_annotations old pre)) v =
  current_original_scan v old.bb_label 0 old.bb_instructions
    (if inserted v old.bb_label then CurrentInserted v old.bb_label else E v)
Proof
  strip_tac >> simp[current_block_annotations_def, FLAT_APPEND,
    rich_listTheory.FOLDL_APPEND, current_original_annotations_scan,
    current_inserted_annotations_scan]
QED

Theorem current_actual_annotation_erasure:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    = (bbs',s') ==>
  LIST_REL (\old new. ?pre.
    new.bb_instructions = pre ++ old.bb_instructions /\
    new.bb_label = old.bb_label /\
    LIST_REL (\inst anns. MAP SND anns = inst.inst_outputs)
      new.bb_instructions (current_block_annotations old pre) /\
    (!E v. FOLDL (\env (t,w). (w =+ t) env) E
      (FLAT (current_block_annotations old pre)) v =
      current_original_scan v old.bb_label 0 old.bb_instructions
        (if current_actual_inserted fn v old.bb_label
         then CurrentInserted v old.bb_label else E v))) fn.fn_blocks bbs'
Proof
  strip_tac >> drule current_actual_insertion_prefix >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `n < LENGTH fn.fn_blocks` by metis_tac[] >>
  first_x_assum drule >> strip_tac >> qexists_tac `pre` >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (drule current_block_annotations_owners >> simp[LIST_REL_EL_EQN]) >>
  irule current_block_annotations_scan >> simp[]
QED

(* A strict insertion boundary: one output per inserted variable and block. *)
Definition current_unique_prefix_def:
  current_unique_prefix pm vars old new <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      EVERY (\i. ?id v. MEM v vars /\ i = build_phi_inst_supply id v
        (case ALOOKUP pm old.bb_label of SOME ps => ps | NONE => [])) pre /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre))
End

Theorem current_unique_prefix_nil:
  current_unique_prefix pm [] b b
Proof
  simp[current_unique_prefix_def] >> qexists_tac `[]` >> simp[]
QED

Theorem current_unique_prefix_cons:
  ~MEM v vars /\ current_var_prefix pm li v [] a b /\
  current_unique_prefix pm vars b c ==>
  current_unique_prefix pm (v::vars) a c
Proof
  simp[current_unique_prefix_def, current_var_prefix_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `pre' ++ pre` >>
  simp[EVERY_APPEND, MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  `!i. MEM i pre ==> i.inst_outputs = [v]` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[build_phi_inst_supply_def]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre))` by
    (Cases_on `pre` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, EVERY_MEM] >>
  qpat_x_assum `!i. MEM i pre' ==> _` drule >>
  strip_tac >> gvs[build_phi_inst_supply_def]
QED

Theorem current_defs_placement_unique_prefix:
  !defs bbs bbs'. ALL_DISTINCT (MAP FST defs) /\
    current_defs_placement df pm li defs bbs bbs' ==>
    LIST_REL (current_unique_prefix pm (MAP FST defs)) bbs bbs'
Proof
  Induct >- simp[current_defs_placement_def, LIST_REL_EL_EQN,
                 current_unique_prefix_nil] >>
  Cases_on `h` >> simp[current_defs_placement_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule current_unique_prefix_cons >> goal_assum $ drule_at Any >>
  metis_tac[]
QED

Theorem current_add_phi_nodes_unique_prefix:
  add_phi_nodes_supply s df pm li bbs (compute_defs ordered) = (bbs',s') ==>
  LIST_REL (current_unique_prefix pm (MAP FST (compute_defs ordered))) bbs bbs'
Proof
  strip_tac >> irule current_defs_placement_unique_prefix >>
  simp[compute_defs_all_distinct] >>
  metis_tac[current_add_phi_nodes_placement]
QED

Theorem current_original_outputs_key:
  !vs j t. MEM t (MAP FST (current_original_outputs l i j vs)) ==>
    ?k. t = CurrentOriginal l i k /\ j <= k
Proof
  Induct >> simp[current_original_outputs_def] >> rpt strip_tac
  >- (qexists_tac `j` >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexists_tac `k` >> simp[]
QED

Theorem current_original_outputs_distinct:
  !vs j. ALL_DISTINCT (MAP FST (current_original_outputs l i j vs))
Proof
  Induct >> simp[current_original_outputs_def] >> rpt strip_tac >>
  drule current_original_outputs_key >> simp[]
QED

Theorem current_original_annotations_key:
  !insts i t. MEM t (MAP FST (FLAT (current_original_annotations l i insts))) ==>
    ?k j. t = CurrentOriginal l k j /\ i <= k
Proof
  Induct >> simp[current_original_annotations_def, MAP_APPEND] >>
  rpt strip_tac
  >- (drule current_original_outputs_key >> strip_tac >>
      qexistsl_tac [`i`, `k`] >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexistsl_tac [`k`, `j`] >> simp[]
QED

Theorem current_original_annotations_distinct:
  !insts i. ALL_DISTINCT
    (MAP FST (FLAT (current_original_annotations l i insts)))
Proof
  Induct >> simp[current_original_annotations_def, MAP_APPEND,
    ALL_DISTINCT_APPEND, current_original_outputs_distinct] >>
  rpt strip_tac >> drule current_original_outputs_key >> strip_tac >>
  drule current_original_annotations_key >> simp[]
QED

Theorem current_inserted_annotations_keys:
  MAP FST (FLAT (current_inserted_annotations l pre)) =
    MAP (\v. CurrentInserted v l) (FLAT (MAP (\i. i.inst_outputs) pre))
Proof
  simp[current_inserted_annotations_def] >> Induct_on `pre` >>
  simp[MAP_APPEND, MAP_MAP_o, o_DEF]
QED

Theorem current_block_annotations_distinct:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre)) ==>
  ALL_DISTINCT (MAP FST (FLAT (current_block_annotations old pre)))
Proof
  simp[current_block_annotations_def, FLAT_APPEND, MAP_APPEND,
    ALL_DISTINCT_APPEND, current_original_annotations_distinct,
    current_inserted_annotations_keys, ALL_DISTINCT_MAP] >>
  strip_tac >> conj_tac >- (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  `MEM (FST y) (MAP FST
    (FLAT (current_original_annotations old.bb_label 0 old.bb_instructions)))`
    by (simp[MEM_MAP] >> metis_tac[]) >>
  drule current_original_annotations_key >>
  qpat_x_assum `CurrentInserted _ _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem current_prefix_unique_instructions:
  current_unique_prefix pm vars old new /\
  new.bb_instructions = pre ++ old.bb_instructions ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre))
Proof
  simp[current_unique_prefix_def] >> rpt strip_tac >> gvs[] >>
  `pre' = pre` by metis_tac[APPEND_11] >> gvs[]
QED

Definition current_block_provenance_def:
  current_block_provenance fn old new anns <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      anns = current_block_annotations old pre /\
      ALL_DISTINCT (MAP FST (FLAT anns)) /\
      LIST_REL (\inst ann. MAP SND ann = inst.inst_outputs)
        new.bb_instructions anns /\
      (!E v. FOLDL (\env (t,w). (w =+ t) env) E (FLAT anns) v =
        current_original_scan v old.bb_label 0 old.bb_instructions
          (if current_actual_inserted fn v old.bb_label
           then CurrentInserted v old.bb_label else E v))
End

Theorem current_actual_block_provenance:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    = (bbs',s') ==>
  LIST_REL (\old new. ?anns. current_block_provenance fn old new anns)
    fn.fn_blocks bbs'
Proof
  strip_tac >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  drule current_actual_insertion_prefix >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `n < LENGTH fn.fn_blocks` by metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!n. _ ==> current_unique_prefix _ _ _ _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `current_block_annotations (EL n fn.fn_blocks) pre` >>
  simp[current_block_provenance_def] >> qexists_tac `pre` >> simp[] >>
  conj_tac
  >- (irule current_block_annotations_distinct >>
      irule current_prefix_unique_instructions >> goal_assum $ drule_at Any >> simp[]) >>
  conj_tac >- simp[current_block_annotations_def, LIST_REL_APPEND_suff,
    current_original_annotations_owners, current_inserted_annotations_owners] >>
  simp[current_block_annotations_def, FLAT_APPEND, rich_listTheory.FOLDL_APPEND,
    current_original_annotations_scan, current_inserted_annotations_scan]
QED

Theorem current_block_provenance_scan:
  current_block_provenance fn old new anns /\
  lookup_block old.bb_label fn.fn_blocks = SOME old ==>
  FOLDL (\env (t,w). (w =+ t) env) E (FLAT anns) v =
    current_block_token fn (current_actual_inserted fn) v old.bb_label (E v)
Proof
  simp[current_block_provenance_def, current_block_token_def] >>
  rpt strip_tac >> simp[]
QED

Definition current_token_label_def:
  (current_token_label (CurrentDefault v) = NONE) /\
  (current_token_label (CurrentOriginal l i j) = SOME l) /\
  (current_token_label (CurrentInserted v l) = SOME l)
End

Theorem current_block_annotations_label:
  MEM t (MAP FST (FLAT (current_block_annotations old pre))) ==>
  current_token_label t = SOME old.bb_label
Proof
  simp[current_block_annotations_def, FLAT_APPEND, MAP_APPEND,
    current_inserted_annotations_keys] >> strip_tac
  >- (gvs[MEM_MAP, current_token_label_def]) >>
  drule current_original_annotations_key >>
  strip_tac >> simp[current_token_label_def]
QED

Theorem current_block_provenance_label:
  current_block_provenance fn old new anns /\ MEM t (MAP FST (FLAT anns)) ==>
  current_token_label t = SOME old.bb_label
Proof
  simp[current_block_provenance_def] >> rpt strip_tac >> gvs[] >>
  irule current_block_annotations_label >> goal_assum $ drule_at Any
QED

Theorem current_provenance_list_label:
  !olds annsss. LIST_REL
    (\old anns. ?new. current_block_provenance fn old new anns) olds annsss ==>
  !t. MEM t (MAP FST (FLAT (FLAT annsss))) ==>
    ?old. MEM old olds /\ current_token_label t = SOME old.bb_label
Proof
  Induct >> Cases_on `annsss` >> simp[] >> rpt strip_tac >>
  gvs[MAP_APPEND] >- metis_tac[current_block_provenance_label] >>
  first_x_assum drule >> disch_then drule >> strip_tac >> metis_tac[]
QED

Theorem current_provenance_global_distinct:
  !olds annsss.
  ALL_DISTINCT (MAP (\bb. bb.bb_label) olds) /\
  LIST_REL (\old anns. ?new. current_block_provenance fn old new anns)
    olds annsss ==>
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss)))
Proof
  Induct >> Cases_on `annsss` >> simp[] >> rpt strip_tac >>
  `ALL_DISTINCT (MAP FST (FLAT (FLAT t)))` by
    (first_x_assum irule >> simp[]) >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> conj_tac
  >- gvs[current_block_provenance_def] >> simp[] >>
  rpt strip_tac >>
  drule_all current_block_provenance_label >> strip_tac >>
  drule current_provenance_list_label >> disch_then drule >> strip_tac >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem current_provenance_collect:
  !olds news.
  LIST_REL (\old new. ?anns. current_block_provenance fn old new anns) olds news ==>
  ?annsss.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (olds,news)) annsss /\
    LIST_REL (\old anns. ?new. current_block_provenance fn old new anns) olds annsss
Proof
  Induct >> Cases_on `news` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `anns::annsss` >> simp[] >> metis_tac[]
QED

Theorem current_actual_provenance:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    = (bbs',s') ==>
  ?annsss.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs')) annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss)))
Proof
  strip_tac >> drule current_actual_block_provenance >>
  disch_then (mp_tac o MATCH_MP current_provenance_collect) >> strip_tac >>
  qexists_tac `annsss` >> simp[] >>
  irule current_provenance_global_distinct >> goal_assum $ drule_at Any >> simp[]
QED

Theorem current_block_provenance_nondefault:
  current_block_provenance fn old new anns /\ MEM t (MAP FST (FLAT anns)) ==>
  !v. t <> CurrentDefault v
Proof
  strip_tac >> drule_all current_block_provenance_label >>
  Cases_on `t` >> simp[current_token_label_def]
QED

Theorem current_provenance_trace_exit:
  current_block_provenance fn old new anns /\
  lookup_block old.bb_label fn.fn_blocks = SOME old /\
  current_local_trace anns new.bb_instructions s rs H E
    insts' s' rs' H' E' ==>
  E' v = current_block_token fn (current_actual_inserted fn) v old.bb_label (E v)
Proof
  strip_tac >> drule current_local_trace_exit_env >> strip_tac >>
  gvs[] >> irule current_block_provenance_scan >> metis_tac[]
QED
