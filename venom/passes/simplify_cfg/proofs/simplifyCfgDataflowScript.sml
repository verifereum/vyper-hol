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
