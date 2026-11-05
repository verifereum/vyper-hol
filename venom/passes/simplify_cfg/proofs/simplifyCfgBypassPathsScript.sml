(* Path transport across deletion of a unique-predecessor singleton jump. *)
Theory simplifyCfgBypassPaths
Ancestors
  simplifyCfgShapeCore
  simplifyCfgBypassStatic simplifyCfgMergePaths simplifyCfgFixupStatic
  venomWf list rich_list
  simplifyCfgDataflow

Theorem scfg_bypass_incoming:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_bypass_jump fn a b /\
  venomWf$fn_cfg_edge fn x b.bb_label ==> x = a.bb_label
Proof
  strip_tac >> drule_all scfg_bypass_preds >> strip_tac >>
  fs[venomWfTheory.fn_cfg_edge_def] >>
  `MEM bb (block_preds fn b.bb_label)` by
    (pure_rewrite_tac[cfgTransformTheory.block_preds_def, MEM_FILTER] >> simp[]) >>
  `bb = a` by metis_tac[MEM] >> gvs[]
QED

Theorem scfg_bypass_outgoing:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ bb_succs b = [target] ==>
  (venomWf$fn_cfg_edge fn b.bb_label y <=> y = target)
Proof
  strip_tac >> simp[scfg_lookup_edge] >> metis_tac[MEM, optionTheory.SOME_11]
QED

Theorem scfg_bypass_filter_path:
  !p. (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
    (!x. venomWf$fn_cfg_edge fn x B ==> x = A) /\
    (!y. venomWf$fn_cfg_edge fn B y ==> y = target) /\ target <> B /\
    is_fn_path fn p ==>
  is_fn_path fn' (FILTER (\l. l <> B) p)
Proof
  Induct >- simp[is_fn_path_def] >> rpt strip_tac >>
  `is_fn_path fn' (FILTER (\l. l <> B) p)` by
    (first_x_assum irule >> Cases_on `p` >> gvs[is_fn_path_def]) >>
  Cases_on `h = B` >- gvs[] >>
  Cases_on `p` >- simp[is_fn_path_def] >>
  rename1 `is_fn_path fn (h::k::rest)` >>
  Cases_on `k = B`
  >- (gvs[] >> Cases_on `rest` >- simp[is_fn_path_def] >>
      rename1 `is_fn_path fn (h::B::z::zs)` >>
      `h = A /\ z = target` by (gvs[is_fn_path_def] >> metis_tac[]) >>
      gvs[FILTER, is_fn_path_def] >> simp[is_fn_path_prepend] >> metis_tac[]) >>
  gvs[FILTER] >> simp[is_fn_path_prepend] >>
  `venomWf$fn_cfg_edge fn h k` by gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem scfg_bypass_expand_path:
  !p. (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
    venomWf$fn_cfg_edge fn A B /\ venomWf$fn_cfg_edge fn B target /\
    is_fn_path fn' p /\ p <> [] /\ EVERY (\l. l <> B) p ==>
  ?q. is_fn_path fn q /\ q <> [] /\ HD q = HD p /\ LAST q = LAST p /\
      FILTER (\l. l <> B) q = p
Proof
  Induct >- simp[] >> rpt strip_tac >> Cases_on `p`
  >- (qexists `[h]` >> gvs[is_fn_path_def]) >>
  rename1 `is_fn_path fn' (h::k::rest)` >> gvs[] >>
  `?q. is_fn_path fn q /\ q <> [] /\ HD q = k /\
    LAST q = LAST (k::rest) /\ FILTER (\l. l <> B) q = k::rest` by
    (first_x_assum irule >> gvs[is_fn_path_def]) >>
  `h <> B /\ k <> B` by gvs[] >>
  `venomWf$fn_cfg_edge fn' h k` by gvs[is_fn_path_def] >>
  Cases_on `venomWf$fn_cfg_edge fn h k`
  >- (qexists `h::q` >> simp[is_fn_path_prepend, LAST_CONS_cond]) >>
  `h = A /\ k = target` by metis_tac[] >>
  qexists `h::B::q` >> simp[is_fn_path_prepend, LAST_CONS_cond, FILTER]
QED

Theorem scfg_bypass_edge:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\ bb_succs b = [target] /\
  lookup_block target fn.fn_blocks = SOME t /\
  EVERY simplifyCfgShapeCore$scfg_label_positions a.bb_instructions /\
  do_merge_jump fn a b lm = SOME (fn', lm') ==>
  (venomWf$fn_cfg_edge fn' x y <=> x <> b.bb_label /\ y <> b.bb_label /\
    (venomWf$fn_cfg_edge fn x y \/ x = a.bb_label /\ y = target))
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label /\ target <> b.bb_label` by
    metis_tac[can_bypass_jump_labels_distinct, scfg_bypass_target_distinct] >>
  `venomWf$fn_cfg_edge fn a.bb_label b.bb_label` by
    (simp[scfg_lookup_edge] >> fs[simplifyCfgDefsTheory.can_bypass_jump_def]) >>
  drule_all scfg_bypass_edge_redirect >>
  disch_then (qspecl_then [`y`, `x`] assume_tac) >>
  Cases_on `x = a.bb_label` >> simp[]
  >- (eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[scfg_bypass_incoming]
QED

Theorem scfg_bypass_path_no_removed:
  !p. (!x y. venomWf$fn_cfg_edge fn' x y ==> x <> B /\ y <> B) /\
    is_fn_path fn' p /\ p <> [] /\ HD p <> B ==>
    EVERY (\l. l <> B) p
Proof
  Induct >- simp[] >> rpt strip_tac >> Cases_on `p` >> gvs[is_fn_path_def] >>
  metis_tac[]
QED

Theorem scfg_bypass_filter_entry_path:
  (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
  (!x. venomWf$fn_cfg_edge fn x B ==> x = A) /\
  (!y. venomWf$fn_cfg_edge fn B y ==> y = target) /\ target <> B /\
  fn_entry_label fn' = fn_entry_label fn /\ fn_entry_label fn <> SOME B /\
  scfg_entry_path fn p t /\ t <> B ==>
  scfg_entry_path fn' (FILTER (\l. l <> B) p) t
Proof
  strip_tac >>
  `is_fn_path fn p /\ p <> [] /\ LAST p = t /\ HD p <> B` by
    (fs[scfg_entry_path_def] >> metis_tac[]) >>
  `is_fn_path fn' (FILTER (\l. l <> B) p)` by
    (irule scfg_bypass_filter_path >> metis_tac[]) >>
  `FILTER (\l. l <> B) p <> [] /\
    HD (FILTER (\l. l <> B) p) = HD p /\
    LAST (FILTER (\l. l <> B) p) = LAST p` by
    (irule scfg_filter_endpoints >> simp[]) >>
  fs[scfg_entry_path_def] >> metis_tac[]
QED

Theorem scfg_bypass_expand_entry_path:
  (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
  venomWf$fn_cfg_edge fn A B /\ venomWf$fn_cfg_edge fn B target /\
  fn_entry_label fn' = fn_entry_label fn /\ fn_entry_label fn <> SOME B /\
  scfg_entry_path fn' p t ==>
  ?q. scfg_entry_path fn q t /\ FILTER (\l. l <> B) q = p
Proof
  strip_tac >>
  `is_fn_path fn' p /\ p <> [] /\ HD p <> B` by
    (fs[scfg_entry_path_def] >> metis_tac[]) >>
  `EVERY (\l. l <> B) p` by
    (irule scfg_bypass_path_no_removed >> metis_tac[]) >>
  drule_all scfg_bypass_expand_path >> strip_tac >>
  qexists `q` >> fs[scfg_entry_path_def] >> metis_tac[]
QED

(* Surviving-label avoidance is exact; no injectivity of contraction is needed. *)
Theorem scfg_bypass_filter_entry_avoiding:
  (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
  (!x. venomWf$fn_cfg_edge fn x B ==> x = A) /\
  (!y. venomWf$fn_cfg_edge fn B y ==> y = target) /\ target <> B /\
  fn_entry_label fn' = fn_entry_label fn /\ fn_entry_label fn <> SOME B /\
  scfg_entry_path fn p t /\ t <> B /\ d <> B /\ ~MEM d p ==>
  scfg_entry_path fn' (FILTER (\l. l <> B) p) t /\
  ~MEM d (FILTER (\l. l <> B) p)
Proof
  strip_tac >> conj_tac
  >- (irule scfg_bypass_filter_entry_path >> metis_tac[]) >>
  simp[MEM_FILTER]
QED

Theorem scfg_bypass_expand_entry_avoiding:
  (!x y. venomWf$fn_cfg_edge fn' x y <=>
       x <> B /\ y <> B /\ (venomWf$fn_cfg_edge fn x y \/ x = A /\ y = target)) /\
  venomWf$fn_cfg_edge fn A B /\ venomWf$fn_cfg_edge fn B target /\
  fn_entry_label fn' = fn_entry_label fn /\ fn_entry_label fn <> SOME B /\
  scfg_entry_path fn' p t /\ d <> B /\ ~MEM d p ==>
  ?q. scfg_entry_path fn q t /\ FILTER (\l. l <> B) q = p /\ ~MEM d q
Proof
  strip_tac >> drule_all scfg_bypass_expand_entry_path >> strip_tac >>
  qexists `q` >> simp[] >>
  `~MEM d (FILTER (\l. l <> B) q)` by metis_tac[] >>
  gvs[MEM_FILTER]
QED

(* A path to the deleted block stops immediately after its unique predecessor. *)
Theorem scfg_bypass_removed_endpoint:
  (!x. venomWf$fn_cfg_edge fn x B ==> x = A) /\
  fn_entry_label fn <> SOME B /\ scfg_entry_path fn p B ==>
  scfg_entry_path fn (FRONT p) A /\ p = FRONT p ++ [B]
Proof
  strip_tac >>
  `is_fn_path fn p /\ p <> [] /\ HD p <> B /\ LAST p = B` by
    (fs[scfg_entry_path_def] >> metis_tac[]) >>
  drule_all scfg_path_last_split >> strip_tac >>
  `LAST route = A` by metis_tac[] >>
  `FRONT p = route` by simp[FRONT_APPEND] >>
  fs[scfg_entry_path_def] >> metis_tac[]
QED
