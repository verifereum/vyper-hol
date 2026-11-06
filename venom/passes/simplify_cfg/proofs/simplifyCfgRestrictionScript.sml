(* Entry and lookup interfaces for unreachable-block restriction. *)
Theory simplifyCfgRestriction
Ancestors
  simplifyCfgShapeCore
  simplifyCfgLabelProps o1PassLift simplifyCfgDefs venomInst cfgTransform
  venomWf venomExecProps list relation simplifyCfgPhiSemantics
  simplifyCfgAvailability simplifyCfgPhiConsumer unitShapeDefs unitLabelMapIdentity
  simplifyCfgStruct
  simplifyCfgDataflow

Theorem scfg_restriction_mem:
  fn_entry_label fn = SOME e ==>
  (MEM bb (remove_unreachable_blocks fn).fn_blocks <=>
   MEM bb fn.fn_blocks /\ reachable fn bb.bb_label)
Proof
  simp[remove_unreachable_blocks_def, MEM_FILTER, CONJ_COMM]
QED

Theorem scfg_restriction_lookup_back:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block l (remove_unreachable_blocks fn).fn_blocks = SOME bb ==>
  lookup_block l fn.fn_blocks = SOME bb
Proof
  strip_tac >>
  `MEM bb (remove_unreachable_blocks fn).fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM bb fn.fn_blocks` by
    (Cases_on `fn_entry_label fn` >>
     gvs[remove_unreachable_blocks_def, MEM_FILTER]) >>
  irule MEM_lookup_block >> gvs[fn_labels_def]
QED

Theorem scfg_restriction_lookup_reachable:
  ALL_DISTINCT (fn_labels fn) /\ fn_reachable fn l ==>
  lookup_block l (remove_unreachable_blocks fn).fn_blocks =
  lookup_block l fn.fn_blocks
Proof
  strip_tac >>
  Cases_on `lookup_block l fn.fn_blocks`
  >- (Cases_on `lookup_block l (remove_unreachable_blocks fn).fn_blocks` >>
      simp[] >> drule_all scfg_restriction_lookup_back >> simp[]) >>
  rename1 `lookup_block l fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `reachable fn l` by metis_tac[fn_reachable_iff_reachable] >>
  `MEM bb (remove_unreachable_blocks fn).fn_blocks` by
    (Cases_on `fn_entry_label fn` >>
     gvs[reachable_def, scfg_restriction_mem]) >>
  irule MEM_lookup_block >> simp[] >>
  metis_tac[fn_labels_remove_unreachable_all_distinct, fn_labels_def]
QED

Theorem scfg_restriction_entry_state:
  fn_entry_state (remove_unreachable_blocks fn) s <=> fn_entry_state fn s
Proof
  simp[fn_entry_state_def, remove_unreachable_blocks_entry]
QED

Theorem scfg_reachable_step:
  fn_reachable fn a /\ fn_cfg_edge fn a b ==> fn_reachable fn b
Proof
  rw[fn_reachable_def] >> qexists_tac `entry` >> simp[] >>
  metis_tac[RTC_SINGLE, RTC_TRANSITIVE, transitive_def]
QED

Theorem scfg_restriction_rtc:
  ALL_DISTINCT (fn_labels fn) ==>
  !a b. RTC (fn_cfg_edge fn) a b /\ fn_reachable fn a ==>
        RTC (fn_cfg_edge (remove_unreachable_blocks fn)) a b
Proof
  strip_tac >> simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  metis_tac[scfg_reachable_step, remove_unreachable_blocks_edge, RTC_RULES]
QED

Theorem scfg_restriction_reachable:
  ALL_DISTINCT (fn_labels fn) ==>
  (fn_reachable (remove_unreachable_blocks fn) l <=> fn_reachable fn l)
Proof
  strip_tac >> simp[fn_reachable_def, remove_unreachable_blocks_entry] >>
  eq_tac >> strip_tac >> qexists_tac `entry` >> simp[]
  >- (qpat_x_assum `RTC _ _ _` mp_tac >>
      match_mp_tac RTC_MONOTONE >> metis_tac[remove_unreachable_blocks_edge_input]) >>
  irule scfg_restriction_rtc >> simp[fn_reachable_def] >>
  qexists_tac `entry` >> simp[]
QED

Theorem scfg_restriction_blocks_reachable:
  ALL_DISTINCT (fn_labels fn) /\ fn_entry_label fn = SOME e /\
  MEM bb (remove_unreachable_blocks fn).fn_blocks ==>
  fn_reachable (remove_unreachable_blocks fn) bb.bb_label
Proof
  strip_tac >> drule_all scfg_restriction_mem >> strip_tac >>
  metis_tac[scfg_restriction_reachable, fn_reachable_iff_reachable]
QED

Theorem scfg_restriction_path_forward:
  ALL_DISTINCT (fn_labels fn) ==>
  !path. is_fn_path fn path /\ (path <> [] ==> fn_reachable fn (HD path)) ==>
    is_fn_path (remove_unreachable_blocks fn) path
Proof
  strip_tac >> Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def] >> gen_tac >> strip_tac >>
  conj_tac >- (irule remove_unreachable_blocks_edge >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[scfg_reachable_step]
QED

Theorem scfg_restriction_rooted_path:
  ALL_DISTINCT (fn_labels fn) /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) ==>
  (is_fn_path (remove_unreachable_blocks fn) path <=> is_fn_path fn path)
Proof
  strip_tac >> eq_tac >- metis_tac[remove_unreachable_blocks_path_input] >>
  strip_tac >> irule scfg_restriction_path_forward >>
  simp[fn_reachable_def] >> qexists_tac `HD path` >> simp[]
QED

Theorem scfg_restriction_defined_path:
  ALL_DISTINCT (fn_labels fn) /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ is_fn_path fn path ==>
  (scfg_path_defined fn path bb n s <=>
   scfg_path_defined (remove_unreachable_blocks fn) path bb n s)
Proof
  strip_tac >>
  `is_fn_path (remove_unreachable_blocks fn) path` by
    metis_tac[scfg_restriction_rooted_path] >>
  `!k. k < LENGTH path ==>
       lookup_block (EL k path) (remove_unreachable_blocks fn).fn_blocks =
       lookup_block (EL k path) fn.fn_blocks` by
    (rpt strip_tac >> irule scfg_restriction_lookup_reachable >> simp[] >>
     irule scfg_path_member_reachable >> metis_tac[EL_MEM]) >>
  simp[scfg_path_defined_def, remove_unreachable_blocks_entry] >>
  eq_tac >> strip_tac >> simp[] >>
  (conj_tac >- (rpt strip_tac >>
    `k < LENGTH path` by decide_tac >> metis_tac[])) >>
  metis_tac[]
QED

Theorem scfg_restriction_def_on_paths:
  ALL_DISTINCT (fn_labels fn) /\ def_on_all_paths fn bb use_inst_opt v ==>
  def_on_all_paths (remove_unreachable_blocks fn) bb use_inst_opt v
Proof
  strip_tac >> simp[def_on_all_paths_def] >> rpt strip_tac >>
  `is_fn_path fn path` by metis_tac[remove_unreachable_blocks_path_input] >>
  `fn_entry_label fn = SOME (HD path)` by metis_tac[remove_unreachable_blocks_entry] >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`k`, `def_bb`, `def_inst`] >> simp[] >>
      `k < LENGTH path` by decide_tac >>
      `fn_reachable fn def_bb.bb_label` by
        (irule scfg_path_member_reachable >> metis_tac[EL_MEM]) >>
      `reachable fn def_bb.bb_label` by metis_tac[fn_reachable_iff_reachable] >>
      metis_tac[scfg_restriction_mem]) >>
  disj2_tac >> metis_tac[]
QED

Theorem scfg_restriction_defs_reach_uses:
  ALL_DISTINCT (fn_labels fn) /\ fn_defs_reach_uses fn ==>
  fn_defs_reach_uses (remove_unreachable_blocks fn)
Proof
  strip_tac >>
  `!bb. MEM bb (remove_unreachable_blocks fn).fn_blocks ==>
         MEM bb fn.fn_blocks` by
    (Cases_on `fn_entry_label fn` >>
     simp[remove_unreachable_blocks_def, MEM_FILTER]) >>
  simp[fn_defs_reach_uses_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >> rpt strip_tac >>
  irule scfg_restriction_def_on_paths >> simp[] >>
  fs[fn_defs_reach_uses_def] >>
  metis_tac[remove_unreachable_blocks_edge_input]
QED

Theorem scfg_restriction_ok:
  wf_function fn /\ simplify_cfg_fn_ok fn ==>
  simplify_cfg_fn_ok (remove_unreachable_blocks fn)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `HD (remove_unreachable_blocks fn).fn_blocks = HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks`
     >- simp[remove_unreachable_blocks_def, fn_entry_label_def, entry_block_def] >>
     `fn_entry_label fn = SOME h.bb_label` by
       simp[fn_entry_label_def, entry_block_def] >>
     `reachable fn h.bb_label` by simp[reachable_def] >>
     simp[remove_unreachable_blocks_def]) >>
  `!bb. MEM bb (remove_unreachable_blocks fn).fn_blocks ==>
         MEM bb fn.fn_blocks` by
    (Cases_on `fn_entry_label fn` >>
     simp[remove_unreachable_blocks_def, MEM_FILTER]) >>
  `fn_defs_reach_uses (remove_unreachable_blocks fn)` by
    (irule scfg_restriction_defs_reach_uses >> fs[simplify_cfg_fn_ok_def]) >>
  simp[simplify_cfg_fn_ok_def] >>
  conj_tac >- fs[simplify_cfg_fn_ok_def] >>
  conj_tac
  >- (rpt strip_tac >> fs[simplify_cfg_fn_ok_def] >>
      metis_tac[scfg_restriction_reachable]) >>
  rpt strip_tac >> fs[simplify_cfg_fn_ok_def] >>
  metis_tac[scfg_restriction_reachable]
QED

Theorem scfg_restriction_fix_phis_block:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb (remove_unreachable_blocks fn).fn_blocks /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  bb.bb_instructions = ps ++ tail /\ EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst (pred_labels (remove_unreachable_blocks fn) bb.bb_label) i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst (pred_labels (remove_unreachable_blocks fn) bb.bb_label) i).inst_opcode <> PHI) ps /\
  MEM pb (remove_unreachable_blocks fn).fn_blocks /\
  fn_cfg_edge (remove_unreachable_blocks fn) pb.bb_label bb.bb_label /\
  s.vs_prev_bb = SOME pb.bb_label /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s ==>
  ?snap.
    EVERY (\i. eval_one_phi s i = SOME (snap i)) ps /\
    eval_phis s ps = OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap ps)) /\
    eval_phis s (MAP (fix_phi_inst (pred_labels (remove_unreachable_blocks fn) bb.bb_label)) rs) =
      OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap rs)) /\
    scfg_iprefix C (fix_phis_in_block (pred_labels (remove_unreachable_blocks fn) bb.bb_label) bb)
      ((FOLDL (\t (x,w). update_var x w t) s (MAP snap rs))
        with vs_inst_idx := LENGTH rs)
      ((FOLDL (\t (x,w). update_var x w t) s (MAP snap ps))
        with vs_inst_idx := LENGTH rs + LENGTH cs)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `path <> [] /\ is_fn_path fn path /\
   fn_entry_label fn = SOME (HD path)` by fs[scfg_path_defined_def] >>
  `scfg_path_defined (remove_unreachable_blocks fn) path pb
     (LENGTH pb.bb_instructions) s` by
    metis_tac[scfg_restriction_defined_path] >>
  `wf_function (remove_unreachable_blocks fn) /\
   fn_inst_wf (remove_unreachable_blocks fn) /\
   simplify_cfg_fn_ok (remove_unreachable_blocks fn)` by
    metis_tac[remove_unreachable_blocks_wf, simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf, scfg_restriction_ok] >>
  `!qb. MEM qb (remove_unreachable_blocks fn).fn_blocks ==>
     fn_reachable (remove_unreachable_blocks fn) qb.bb_label` by
    metis_tac[scfg_restriction_blocks_reachable] >>
  irule scfg_fn_fix_phis_block >> metis_tac[]
QED

Theorem scfg_opaque_use_subset:
  (!i. MEM i (fn_insts f) ==> MEM i (fn_insts g)) /\
  opaque_use_ok g ==> opaque_use_ok f
Proof
  rw[opaque_use_ok_def, gas_var_def, retpc_var_def] >>
  metis_tac[copy_phi_var_mono, gas_var_def, retpc_var_def]
QED

Theorem scfg_restriction_insts_subset:
  MEM i (fn_insts (remove_unreachable_blocks fn)) ==> MEM i (fn_insts fn)
Proof
  Cases_on `fn_entry_label fn` >>
  simp[remove_unreachable_blocks_def, fn_insts_def, fn_insts_blocks_mem, MEM_FILTER] >>
  metis_tac[]
QED

Theorem scfg_restriction_shape:
  scfg_shape fn ==> scfg_shape (remove_unreachable_blocks fn)
Proof
  strip_tac >>
  `opaque_use_ok (remove_unreachable_blocks fn)` by
    (irule scfg_opaque_use_subset >> qexists_tac `fn` >>
     fs[scfg_shape_def] >> metis_tac[scfg_restriction_insts_subset]) >>
  `fn_entry_label (remove_unreachable_blocks fn) = SOME fn.fn_name` by
    fs[scfg_shape_def, remove_unreachable_blocks_entry] >>
  `!bb. MEM bb (remove_unreachable_blocks fn).fn_blocks ==> MEM bb fn.fn_blocks` by
    (Cases_on `fn_entry_label fn` >> simp[remove_unreachable_blocks_def, MEM_FILTER]) >>
  ` (remove_unreachable_blocks fn).fn_name = fn.fn_name` by
    (Cases_on `fn_entry_label fn` >> simp[remove_unreachable_blocks_def]) >>
  fs[scfg_shape_def, EVERY_MEM] >>
  metis_tac[scfg_restriction_insts_subset]
QED

