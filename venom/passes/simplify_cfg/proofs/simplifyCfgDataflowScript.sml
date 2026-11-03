Theory simplifyCfgDataflow
Ancestors
  simplifyCfgStruct simplifyCfgLabelProps simplifyCfgDefs cfgTransform
  venomWf venomInst venomExecProofs cfgWf list rich_list relation

Theorem is_fn_path_edge_mono:
  (!a b. fn_cfg_edge fn a b ==> fn_cfg_edge fn' a b) ==>
  !path. is_fn_path fn path ==> is_fn_path fn' path
Proof
  strip_tac >> Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_edge_input:
  fn_cfg_edge (remove_unreachable_blocks fn) a b ==> fn_cfg_edge fn a b
Proof
  Cases_on `fn_entry_label fn` >>
  simp[fn_cfg_edge_def, remove_unreachable_blocks_def, MEM_FILTER] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_path_input:
  is_fn_path (remove_unreachable_blocks fn) path ==> is_fn_path fn path
Proof
  match_mp_tac (GEN_ALL is_fn_path_edge_mono) >>
  metis_tac[remove_unreachable_blocks_edge_input]
QED

Theorem remove_unreachable_blocks_dominates:
  wf_function fn /\ MEM bb (remove_unreachable_blocks fn).fn_blocks /\
  fn_dominates fn d bb.bb_label ==>
  fn_dominates (remove_unreachable_blocks fn) d bb.bb_label
Proof
  strip_tac >> simp[fn_dominates_def] >> conj_tac
  >- metis_tac[remove_unreachable_blocks_reachable, all_reachable_def] >>
  rpt strip_tac >>
  `is_fn_path fn path` by metis_tac[remove_unreachable_blocks_path_input] >>
  fs[remove_unreachable_blocks_entry, fn_dominates_def] >> metis_tac[]
QED

Theorem fix_all_phis_path_iff:
  wf_function fn ==> (is_fn_path (fix_all_phis fn) path <=> is_fn_path fn path)
Proof
  strip_tac >> eq_tac >>
  match_mp_tac (GEN_ALL is_fn_path_edge_mono) >>
  metis_tac[fix_all_phis_edge, wf_function_def]
QED

Theorem fix_all_phis_dominates:
  wf_function fn ==> (fn_dominates (fix_all_phis fn) d n <=> fn_dominates fn d n)
Proof
  strip_tac >>
  `fn_reachable (fix_all_phis fn) n = fn_reachable fn n` by
    metis_tac[fix_all_phis_reachable, wf_function_def] >>
  simp[fn_dominates_def, fix_all_phis_entry, fix_all_phis_path_iff]
QED

Theorem entry_path_member_reachable:
  is_fn_path fn path /\ MEM lbl path /\
  fn_entry_label fn = SOME entry /\ HD path = entry ==>
  fn_reachable fn lbl
Proof
  strip_tac >> drule_all is_fn_path_prefix >> strip_tac >>
  simp[fn_reachable_def] >>
  qspec_then `pre ++ [lbl]` mp_tac (Q.SPEC `fn` is_fn_path_rtc) >>
  simp[]
QED

Theorem is_fn_path_restrict_edges:
  !path. is_fn_path fn path /\
    (!a b. MEM a path /\ fn_cfg_edge fn a b ==> fn_cfg_edge fn' a b) ==>
    is_fn_path fn' path
Proof
  Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_entry_path:
  wf_function fn /\ is_fn_path fn path /\
  fn_entry_label fn = SOME entry /\ HD path = entry ==>
  is_fn_path (remove_unreachable_blocks fn) path
Proof
  strip_tac >> irule is_fn_path_restrict_edges >>
  qexists `fn` >> simp[] >> rpt strip_tac >>
  irule remove_unreachable_blocks_edge >>
  gvs[wf_function_def] >>
  metis_tac[entry_path_member_reachable]
QED

Definition chain_chunk_def:
  chain_chunk a b x = if x = a then [a;b] else [x]
End

Definition chain_prefix_def:
  chain_prefix a b p = FLAT (MAP (chain_chunk a b) (FRONT p))
End

Theorem chain_chunk_mem:
  MEM d (chain_chunk a b x) <=> d = x \/ (d = b /\ x = a)
Proof
  Cases_on `x = a` >> simp[chain_chunk_def] >> metis_tac[]
QED

Theorem chain_prefix_mem:
  MEM d (chain_prefix a b p) <=>
  MEM d (FRONT p) \/ (d = b /\ MEM a (FRONT p))
Proof
  simp[chain_prefix_def, MEM_FLAT, MEM_MAP] >> metis_tac[chain_chunk_mem]
QED

Theorem chain_prefix_singleton[simp]:
  chain_prefix a b [x] = []
Proof
  simp[chain_prefix_def]
QED

Theorem chain_prefix_loop[simp]:
  chain_prefix a b [a;a] = [a;b]
Proof
  simp[chain_prefix_def, chain_chunk_def]
QED

Theorem chain_prefix_last[simp]:
  LAST (chain_prefix a b p ++ [z]) = z
Proof
  simp[]
QED

Theorem chain_prefix_front[simp]:
  FRONT (chain_prefix a b p ++ [z]) = chain_prefix a b p
Proof
  simp[FRONT_APPEND]
QED

Theorem chain_prefix_front_pair[simp]:
  FRONT (chain_prefix a b p ++ [a;b]) = chain_prefix a b p ++ [a]
Proof
  simp[FRONT_APPEND]
QED

Theorem chain_prefix_head:
  p <> [] ==> HD (chain_prefix a b p ++ [LAST p]) = HD p
Proof
  Cases_on `p` >> simp[] >> Cases_on `t` >>
  simp[chain_prefix_def, chain_chunk_def, FRONT_DEF] >>
  Cases_on `h = a` >> simp[chain_chunk_def]
QED

Theorem mem_front_index:
  p <> [] ==>
  (MEM d (FRONT p) <=> ?k. k < LENGTH p - 1 /\ EL k p = d)
Proof
  strip_tac >>
  `PRE (LENGTH p) = LENGTH p - 1` by decide_tac >>
  simp[MEM_EL, LENGTH_FRONT, SF CONJ_ss, EL_FRONT, NULL_EQ] >>
  metis_tac[]
QED

Theorem replace_block_cfg_edges:
  lookup_block lbl bbs = SOME bb /\
  bb'.bb_label = bb.bb_label /\ bb_succs bb' = bb_succs bb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
  ((?b. MEM b (replace_block lbl bb' bbs) /\ b.bb_label = src /\
        MEM dst (bb_succs b)) <=>
   (?b. MEM b bbs /\ b.bb_label = src /\ MEM dst (bb_succs b)))
Proof
  strip_tac >>
  `MEM bb bbs /\ bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  simp[replace_block_def, MEM_MAP] >> eq_tac >> rpt strip_tac
  >- (Cases_on `b'.bb_label = lbl` >> gvs[] >> metis_tac[])
  >- (qexists `if b.bb_label = lbl then bb' else b` >>
      conj_tac >- (qexists `b` >> simp[]) >>
      Cases_on `b.bb_label = lbl` >> gvs[] >>
      `lookup_block b.bb_label bbs = SOME b` by
        (irule MEM_lookup_block >> simp[]) >> gvs[])
QED

Theorem update_succ_phi_labels_cfg_edges:
  !succs bbs. EVERY bb_well_formed bbs /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  ((?bb. MEM bb (update_succ_phi_labels old new bbs succs) /\
         bb.bb_label = src /\ MEM dst (bb_succs bb)) <=>
   (?bb. MEM bb bbs /\ bb.bb_label = src /\ MEM dst (bb_succs bb)))
Proof
  Induct_on `succs` >> simp[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[]
  >- (first_x_assum (qspec_then `bbs` mp_tac) >>
      simp[update_succ_phi_labels_def]) >>
  rename1 `lookup_block h bbs = SOME bb` >>
  `MEM bb bbs /\ bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  `bb_well_formed bb` by fs[EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `FOLDL stepfn bs succs` >>
  `EVERY bb_well_formed bs` by
    (simp[Abbr `bs`] >> irule EVERY_replace_block >>
     simp[bb_well_formed_subst_phi_labels]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bs)` by
    simp[Abbr `bs`, cfgTransformPropsTheory.fn_labels_replace_block] >>
  first_x_assum (qspec_then `bs` mp_tac) >>
  simp[update_succ_phi_labels_def, Abbr `stepfn`] >>
  disch_then (fn th => rewrite_tac[th]) >>
  unabbrev_all_tac >> irule replace_block_cfg_edges >>
  simp[bb_succs_subst_phi_labels] >> metis_tac[]
QED

Theorem chain_merge_base_edge:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ src <> b.bb_label ==>
  (fn_cfg_edge (fn with fn_blocks :=
      replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) src dst <=>
   if src = a.bb_label then fn_cfg_edge fn b.bb_label dst
   else fn_cfg_edge fn src dst)
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by fs[can_merge_blocks_def] >>
  `b.bb_instructions <> []` by
    metis_tac[wf_function_bb_well_formed, bb_well_formed_def] >>
  `!bb. MEM bb fn.fn_blocks /\ bb.bb_label = a.bb_label ==> bb = a` by
    metis_tac[same_label_same_block] >>
  `!bb. MEM bb fn.fn_blocks /\ bb.bb_label = b.bb_label ==> bb = b` by
    metis_tac[same_label_same_block] >>
  `bb_succs (merge_blocks a b) = bb_succs b` by simp[bb_succs_merge_blocks] >>
  ` (merge_blocks a b).bb_label = a.bb_label` by simp[merge_blocks_def] >>
  simp[fn_cfg_edge_def, replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  Cases_on `src = a.bb_label` >> gvs[] >> eq_tac >> rpt strip_tac
  >- (Cases_on `bb'.bb_label = a.bb_label` >> gvs[] >> metis_tac[])
  >- (`bb = b` by metis_tac[] >> gvs[] >>
      qexists `merge_blocks a b` >> simp[] >> qexists `a` >> simp[])
  >- (Cases_on `bb'.bb_label = a.bb_label` >> gvs[] >> metis_tac[])
  >- (qexists `bb` >> simp[] >> qexists `bb` >> simp[])
QED

Theorem chain_merge_edge:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ src <> b.bb_label ==>
  (fn_cfg_edge (fn with fn_blocks :=
     update_succ_phi_labels b.bb_label a.bb_label
       (replace_block a.bb_label (merge_blocks a b)
         (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
     src dst <=>
   if src = a.bb_label then fn_cfg_edge fn b.bb_label dst
   else fn_cfg_edge fn src dst)
Proof
  strip_tac >>
  `EVERY bb_well_formed (replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks))` by
    (irule chain_merge_base_bb_wf >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)))` by
    (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  drule_all chain_merge_base_edge >>
  simp[fn_cfg_edge_def, update_succ_phi_labels_cfg_edges]
QED

Theorem chain_prefix_path:
  fn_cfg_edge fn a b /\
  (!x y. fn_cfg_edge fn' x y ==>
     if x = a then fn_cfg_edge fn b y else fn_cfg_edge fn x y) ==>
  !p. p <> [] /\ is_fn_path fn' p ==>
    is_fn_path fn (chain_prefix a b p ++ [LAST p])
Proof
  strip_tac >> Induct >> simp[] >>
  qx_gen_tac `x` >>
  Cases_on `p` >> simp[chain_prefix_def, is_fn_path_def] >>
  rpt strip_tac >>
  rename1 `fn_cfg_edge fn' x y` >>
  `HD (chain_prefix a b (y::t) ++ [LAST (y::t)]) = y` by
    simp[chain_prefix_head] >>
  `is_fn_path fn (chain_prefix a b (y::t) ++ [LAST (y::t)])` by fs[] >>
  qpat_x_assum `is_fn_path fn (chain_prefix _ _ _ ++ _)` mp_tac >>
  simp[chain_prefix_def] >>
  Cases_on `x = a` >> simp[chain_chunk_def] >>
  Cases_on `FLAT (MAP (chain_chunk a b) (FRONT (y::t))) ++ [LAST (y::t)]` >>
  gvs[is_fn_path_def, chain_prefix_def] >> metis_tac[]
QED

Theorem is_fn_path_member_labels:
  !p. is_fn_path fn p /\ MEM (LAST p) (fn_labels fn) ==>
    EVERY (\x. MEM x (fn_labels fn)) p
Proof
  Induct >> simp[] >> Cases_on `p` >> simp[is_fn_path_def] >>
  rpt strip_tac >>
  fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem chain_prefix_path_last_pair:
  fn_cfg_edge fn a b /\ p <> [] /\ LAST p = a /\
  is_fn_path fn (chain_prefix a b p ++ [LAST p]) ==>
  is_fn_path fn (chain_prefix a b p ++ [a;b])
Proof
  strip_tac >>
  drule is_fn_path_snoc >> simp[] >>
  disch_then (qspec_then `b` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem chain_merge_path_input:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
     update_succ_phi_labels b.bb_label a.bb_label
       (replace_block a.bb_label (merge_blocks a b)
         (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) /\
  p <> [] /\ is_fn_path fn' p /\ MEM (LAST p) (fn_labels fn') ==>
  ~MEM b.bb_label p /\
  is_fn_path fn (chain_prefix a.bb_label b.bb_label p ++ [LAST p])
Proof
  strip_tac >>
  `EVERY (\x. MEM x (fn_labels fn')) p` by
    metis_tac[is_fn_path_member_labels] >>
  `fn_labels fn' = FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)` by
    (qpat_x_assum `fn' = _` SUBST1_TAC >> simp[chain_merge_fn_labels]) >>
  `~MEM b.bb_label p` by
    (fs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  simp[] >>
  `fn_cfg_edge fn a.bb_label b.bb_label` by
    (simp[fn_cfg_edge_def] >> qexists `a` >> fs[can_merge_blocks_def]) >>
  irule chain_prefix_path >> simp[] >> qexists `fn'` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> rename1 `fn_cfg_edge fn' src dst` >>
  `MEM src (fn_labels fn')` by
    (qpat_assum `fn_cfg_edge fn' src dst` mp_tac >>
     pure_rewrite_tac[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >>
     metis_tac[]) >>
  `src <> b.bb_label` by
    (qpat_x_assum `MEM src (fn_labels fn')` mp_tac >> simp[MEM_FILTER]) >>
  qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
  drule_all chain_merge_edge >>
  disch_then (qspec_then `dst` mp_tac) >> simp[]
QED

Theorem chain_prefix_head_pair:
  p <> [] /\ LAST p = a ==>
  HD (chain_prefix a b p ++ [a;b]) = HD p
Proof
  strip_tac >>
  `HD (chain_prefix a b p ++ [LAST p]) = HD p` by simp[chain_prefix_head] >>
  Cases_on `chain_prefix a b p` >> gvs[]
QED

Theorem chain_merge_path_input_pair:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
     update_succ_phi_labels b.bb_label a.bb_label
       (replace_block a.bb_label (merge_blocks a b)
         (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) /\
  p <> [] /\ is_fn_path fn' p /\ MEM (LAST p) (fn_labels fn') /\
  LAST p = a.bb_label ==>
  is_fn_path fn (chain_prefix a.bb_label b.bb_label p ++ [a.bb_label;b.bb_label])
Proof
  strip_tac >>
  `fn_cfg_edge fn a.bb_label b.bb_label` by
    (simp[fn_cfg_edge_def] >> qexists `a` >> fs[can_merge_blocks_def]) >>
  irule chain_prefix_path_last_pair >> simp[] >>
  drule_all chain_merge_path_input >> simp[]
QED

Theorem chain_prefix_earlier:
  MEM d (FRONT (chain_prefix a b p ++ [z])) <=>
  MEM d (FRONT p) \/ (d = b /\ MEM a (FRONT p))
Proof
  simp[chain_prefix_mem]
QED

Theorem chain_prefix_earlier_pair:
  MEM d (FRONT (chain_prefix a b p ++ [a;b])) <=>
  MEM d (FRONT p) \/ (d = b /\ MEM a (FRONT p)) \/ d = a
Proof
  simp[chain_prefix_mem] >> metis_tac[]
QED
