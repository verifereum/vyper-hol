Theory makeSsaCurrentSingleSiteSegment
Ancestors
  makeSsaCurrentPlacementCut makeSsaCurrentOccurrence makeSsaCurrentLastSite
  makeSsaCurrentRestrictedSegment list rich_list arithmetic

Theorem current_single_definition_changing_site_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME entry /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  blocks_have_leading_phi fn.fn_blocks /\
  current_changing_site fn (current_actual_inserted fn) v l ==>
  l = db.bb_label
Proof
  simp[current_changing_site_def] >> rpt strip_tac
  >- (drule_all current_actual_inserted_single_local >> simp[]) >>
  metis_tac[current_single_def_occurrence]
QED

Theorem current_single_site_restricted_path:
  labels <> [] /\
  (!k. SUC k < LENGTH labels ==>
    fn_cfg_edge fn (EL k labels) (EL (SUC k) labels)) /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) labels /\
  ~MEM d labels /\
  (!l. current_changing_site fn (current_actual_inserted fn) v l ==> l = d) ==>
  current_restricted_path fn v labels
Proof
  simp[current_restricted_path_def, EVERY_MEM] >> metis_tac[]
QED

Theorem current_cfg_suffix_edges[local]:
  !pre post.
  (!k. SUC k < LENGTH (pre ++ post) ==>
    fn_cfg_edge fn (EL k (pre ++ post)) (EL (SUC k) (pre ++ post))) ==>
  !k. SUC k < LENGTH post ==>
    fn_cfg_edge fn (EL k post) (EL (SUC k) post)
Proof
  rpt strip_tac >>
  `SUC (k + LENGTH pre) - LENGTH pre = SUC k` by decide_tac >>
  first_x_assum (qspec_then `LENGTH pre + k` mp_tac) >>
  simp[EL_APPEND, ADD_CLAUSES]
QED

Theorem current_single_site_last_visit:
  labels <> [] /\
  (!k. SUC k < LENGTH labels ==>
    fn_cfg_edge fn (EL k labels) (EL (SUC k) labels)) /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) labels /\
  (!l. current_changing_site fn (current_actual_inserted fn) v l ==> l = d) ==>
  (~MEM d labels /\ current_restricted_path fn v labels) \/
  ?pre post. labels = pre ++ d::post /\ ~MEM d post /\
    (post = [] \/ current_restricted_path fn v post)
Proof
  strip_tac >>
  qspec_then `labels` mp_tac (Q.INST [`P` |-> `\l. l = d`] current_list_last_site) >>
  simp[EVERY_MEM] >> strip_tac
  >- (disj1_tac >> conj_tac >- metis_tac[] >>
      irule current_single_site_restricted_path >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`pre`, `post`] >> gvs[] >>
  Cases_on `post = []` >- simp[] >> simp[] >>
  irule current_single_site_restricted_path >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >> irule current_cfg_suffix_edges >>
  simp[] >> qexists_tac `pre ++ [d]` >>
  gvs[APPEND_ASSOC]
QED
