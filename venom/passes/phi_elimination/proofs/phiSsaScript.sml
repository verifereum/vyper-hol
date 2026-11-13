(* SSA and the pipeline's entry invariants survive PHI elimination. *)
Theory phiSsa
Ancestors
  phiTransform phiOrigins phiCopyRegion phiDefs venomWf o1PassContract unitShapeDefs
  sorting list

Theorem phi_transform_cfg_edge:
  !fn a b. wf_function fn ==>
    (fn_cfg_edge (transform_function fn) a b <=> fn_cfg_edge fn a b)
Proof
  rpt strip_tac >>
  simp[fn_cfg_edge_def, transform_function_def, MEM_MAP,
       transform_block_label] >>
  metis_tac[transform_block_succs, transform_block_label,
            venomExecProofsTheory.wf_function_bb_well_formed]
QED

Theorem phi_transform_entry_label:
  !fn. fn_entry_label (transform_function fn) = fn_entry_label fn
Proof
  simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
       transform_function_def] >>
  gen_tac >> Cases_on `fn.fn_blocks` >> simp[transform_block_label]
QED

Theorem phi_transform_reachable:
  !fn lbl. wf_function fn ==>
    (fn_reachable (transform_function fn) lbl <=> fn_reachable fn lbl)
Proof
  rpt strip_tac >>
  `fn_cfg_edge (transform_function fn) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, phi_transform_cfg_edge] >>
  simp[fn_reachable_def, phi_transform_entry_label]
QED

Theorem phi_transform_path:
  !fn path. wf_function fn ==>
    (is_fn_path (transform_function fn) path <=> is_fn_path fn path)
Proof
  gen_tac >> Induct_on `path` >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def, phi_transform_cfg_edge]
QED

Theorem phi_transform_dominates:
  !fn a b. wf_function fn ==>
    (fn_dominates (transform_function fn) a b <=> fn_dominates fn a b)
Proof
  rpt strip_tac >>
  simp[fn_dominates_def, phi_transform_reachable,
       phi_transform_entry_label, phi_transform_path]
QED

Theorem phi_transform_first_no_preds:
  !fn. wf_function fn /\ first_block_no_preds fn ==>
    first_block_no_preds (transform_function fn)
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  Cases_on `fn.fn_blocks` >> gvs[] >>
  gvs[first_block_no_preds_def, transform_function_def, EVERY_MAP,
      transform_block_label, EVERY_MEM, MEM_MAP] >>
  metis_tac[transform_block_succs,
            venomExecProofsTheory.wf_function_bb_well_formed, MEM]
QED

Theorem phi_transform_first_no_phi:
  !fn. wf_function fn /\ first_block_no_phi fn ==>
    first_block_no_phi (transform_function fn)
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  Cases_on `fn.fn_blocks` >> gvs[] >>
  gvs[first_block_no_phi_def, transform_function_def, transform_block_def,
      EVERY_MEM, transform_insts_def, MEM_APPEND, MEM_FILTER, MEM_MAP] >>
  metis_tac[transform_inst_phi_iff]
QED

Theorem phi_transform_available_end:
  !fn bb v. wf_function fn /\ def_available_at fn bb NONE v ==>
    def_available_at (transform_function fn)
      (transform_block (dfg_build_function fn) bb) NONE v
Proof
  rpt strip_tac >>
  gvs[def_available_at_def] >>
  qexistsl [`transform_block (dfg_build_function fn) def_bb`,
            `transform_inst (dfg_build_function fn) def_inst`] >>
  simp[transform_function_def, MEM_MAP, transform_inst_preserves_outputs,
       MEM_transform_inst_transform_block, transform_block_label,
       phi_transform_dominates] >>
  metis_tac[MEM_transform_inst_transform_block, phi_transform_dominates,
            transform_block_label, transform_function_def]
QED

Theorem phi_transform_phi_edges:
  !fn bb inst.
    wf_function fn /\ phi_edge_uses_wf fn bb inst ==>
    phi_edge_uses_wf (transform_function fn)
      (transform_block (dfg_build_function fn) bb) inst
Proof
  rpt strip_tac >>
  gvs[phi_edge_uses_wf_def] >>
  simp[phi_transform_cfg_edge, transform_block_label] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists `transform_block (dfg_build_function fn) pred_bb` >>
  simp[transform_function_def, MEM_MAP, transform_block_label,
       phi_transform_cfg_edge, phi_transform_available_end] >>
  metis_tac[]
QED

Theorem phi_transform_available_ordinary:
  !fn bb inst v.
    wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands /\
    def_available_at fn bb (SOME inst) v ==>
    def_available_at (transform_function fn)
      (transform_block (dfg_build_function fn) bb)
      (SOME (transform_inst (dfg_build_function fn) inst)) v
Proof
  rpt strip_tac >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `~is_pseudo inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >>
     gvs[venomInstTheory.is_pseudo_def, inst_wf_def]) >>
  gvs[def_available_at_def] >>
  qexistsl [`transform_block (dfg_build_function fn) def_bb`,
            `transform_inst (dfg_build_function fn) def_inst`] >>
  simp[transform_function_def, MEM_MAP, transform_inst_preserves_outputs,
       MEM_transform_inst_transform_block, transform_block_label,
       phi_transform_dominates] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  `def_bb.bb_label = bb.bb_label` by metis_tac[transform_block_label] >>
  `def_bb = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >>
  `bb_well_formed bb` by
    metis_tac[venomExecProofsTheory.wf_function_bb_well_formed] >>
  drule_all transform_block_nonpseudo_order >>
  metis_tac[]
QED

Theorem phi_transform_replacement_available:
  !fn bb inst r.
    wf_function fn /\ wf_ssa fn /\ first_block_no_phi fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    phi_single_origin (dfg_build_function fn) inst = SOME r ==>
    def_available_at (transform_function fn)
      (transform_block (dfg_build_function fn) bb)
      (SOME (transform_inst (dfg_build_function fn) inst)) r
Proof
  rpt strip_tac >>
  `inst.inst_opcode = PHI` by
    metis_tac[phi_single_origin_is_phi, is_phi_inst_def] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_single_origin_reachable] >>
  `EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions` by
    fs[first_block_no_phi_def] >>
  drule_all phi_single_origin_strict_dominance >> strip_tac >>
  simp[def_available_at_def] >>
  qexistsl [`transform_block (dfg_build_function fn) db`,
            `transform_inst (dfg_build_function fn) di`] >>
  simp[transform_function_def, MEM_MAP, transform_inst_preserves_outputs,
       MEM_transform_inst_transform_block, transform_block_label,
       phi_transform_dominates] >>
  metis_tac[transform_block_label]
QED

Theorem phi_elim_preserves_wf_ssa:
  !func.
    wf_function func /\
    fn_inst_wf func /\
    wf_ssa func /\
    fn_pseudos_prefix func /\
    first_block_no_preds func /\
    first_block_no_phi func
  ==>
    wf_ssa (transform_function func) /\
    first_block_no_preds (transform_function func) /\
    first_block_no_phi (transform_function func)
Proof
  gen_tac >> strip_tac >>
  reverse conj_tac
  >- metis_tac[phi_transform_first_no_preds, phi_transform_first_no_phi] >>
  simp[wf_ssa_def] >>
  conj_tac >- metis_tac[wf_ssa_def, phi_elim_preserves_ssa_form] >>
  simp[def_dominates_uses_def, transform_function_def, MEM_MAP] >>
  rpt strip_tac >>
  gvs[transform_block_def] >>
  rename1 `MEM bb func.fn_blocks` >>
  `MEM inst (MAP (transform_inst (dfg_build_function func))
      bb.bb_instructions)` by
    metis_tac[transform_insts_perm, sortingTheory.PERM_MEM_EQ] >>
  gvs[MEM_MAP] >>
  rename1 `MEM src bb.bb_instructions` >>
  once_rewrite_tac[GSYM transform_block_def] >>
  `if src.inst_opcode = PHI then phi_edge_uses_wf func bb src
   else !v. MEM (Var v) src.inst_operands ==>
     def_available_at func bb (SOME src) v` by
    metis_tac[wf_ssa_def, def_dominates_uses_def] >>
  Cases_on `phi_single_origin (dfg_build_function func) src`
  >- (simp[transform_inst_identity] >>
      Cases_on `src.inst_opcode = PHI` >> gvs[]
      >- metis_tac[phi_transform_phi_edges, transform_function_def] >>
      rpt strip_tac >>
      `def_available_at func bb (SOME src) v` by metis_tac[] >>
      drule_all phi_transform_available_ordinary >>
      simp[transform_inst_identity, transform_function_def]) >>
  drule transform_inst_phi_to_assign >> strip_tac >>
  simp[] >>
  drule_all phi_transform_replacement_available >>
  simp[transform_function_def]
QED
