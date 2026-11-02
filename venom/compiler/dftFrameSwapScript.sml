(* Local structural interface for directed DFT crossings. *)
Theory dftFrameSwap
Ancestors
  dftFrameOrder dftFramePerm dftCorrectnessFinal dftDefs unitShapeDefs venomWf venomInst venomEffects
  venomState finite_map sorting list relation

Definition dft_cross_def:
  dft_cross a b <=>
    a.inst_id <> b.inst_id /\
    ~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    DISJOINT (write_effects a.inst_opcode)
      (read_effects b.inst_opcode UNION write_effects b.inst_opcode) /\
    DISJOINT (read_effects a.inst_opcode) (write_effects b.inst_opcode) /\
    (~(is_fallible a /\ is_fallible b) \/
     (a.inst_opcode = RETURNDATACOPY /\ b.inst_opcode = ASSERT_UNREACHABLE))
End

Definition dft_swap_list_def:
  dft_swap_list = adjacent_swap dft_cross
End

Definition dft_swap_fn_def:
  dft_swap_fn f g <=>
    ?p bb q insts.
      f.fn_blocks = p ++ [bb] ++ q /\
      dft_swap_list bb.bb_instructions insts /\
      g = f with fn_blocks := p ++ [bb with bb_instructions := insts] ++ q
End

Definition dft_labels_bound_def:
  dft_labels_bound f L <=>
    !inst l. MEM inst (fn_insts f) /\
      MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
      l IN FDOM L
End

Definition dft_swap_invariant_def:
  dft_swap_invariant L f <=>
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ fn_pseudos_prefix f /\
    fn_shape_ok f /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f) /\
    dft_labels_bound f L
End

Theorem dft_swap_list_perm:
  dft_swap_list l r ==> PERM l r
Proof
  rw[dft_swap_list_def, adjacent_swap_def] >>
  simp[PERM_APPEND_IFF, PERM_SWAP_AT_FRONT]
QED

Theorem dft_swap_list_last:
  dft_swap_list l r /\ is_terminator (LAST l).inst_opcode ==>
  LAST l = LAST r
Proof
  rw[dft_swap_list_def, adjacent_swap_def] >>
  Cases_on `q` >> gvs[LAST_APPEND_CONS, dft_cross_def]
QED

Theorem dft_swap_list_pseudos:
  dft_swap_list l r ==>
  FILTER (\i. is_pseudo i.inst_opcode) l =
  FILTER (\i. is_pseudo i.inst_opcode) r
Proof
  rw[dft_swap_list_def, adjacent_swap_def] >>
  gvs[dft_cross_def, FILTER_APPEND_DISTRIB]
QED

Theorem dft_swap_fn_name_entry:
  dft_swap_fn f g ==>
  fn_entry_label g = fn_entry_label f /\ g.fn_name = f.fn_name
Proof
  rw[dft_swap_fn_def, fn_entry_label_def] >>
  Cases_on `p` >> gvs[entry_block_def]
QED

Theorem dft_swap_fn_labels:
  dft_swap_fn f g ==> fn_labels g = fn_labels f
Proof
  rw[dft_swap_fn_def, fn_labels_def] >> simp[MAP_APPEND]
QED

Theorem dft_swap_fn_insts_perm:
  dft_swap_fn f g ==> PERM (fn_insts f) (fn_insts g)
Proof
  `!p q. fn_insts_blocks (p ++ q) = fn_insts_blocks p ++ fn_insts_blocks q`
    by (Induct >> simp[fn_insts_blocks_def, APPEND_ASSOC]) >>
  rw[dft_swap_fn_def, fn_insts_def] >>
  simp[fn_insts_blocks_def, PERM_APPEND_IFF] >>
  metis_tac[dft_swap_list_perm]
QED

Theorem dft_swap_fn_insts_every:
  dft_swap_fn f g ==> (EVERY P (fn_insts g) <=> EVERY P (fn_insts f))
Proof
  strip_tac >> drule dft_swap_fn_insts_perm >>
  metis_tac[PERM_MEM_EQ, EVERY_MEM]
QED

Theorem dft_swap_fn_labels_bound:
  dft_swap_fn f g ==> (dft_labels_bound g L <=> dft_labels_bound f L)
Proof
  strip_tac >> drule dft_swap_fn_insts_perm >>
  simp[dft_labels_bound_def] >> metis_tac[PERM_MEM_EQ]
QED

Theorem dft_swap_fn_inst_wf:
  dft_swap_fn f g ==> (fn_inst_wf g <=> fn_inst_wf f)
Proof
  rw[dft_swap_fn_def] >>
  simp[fn_inst_wf_def, MEM_APPEND] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[] >> drule dft_swap_list_perm >>
  disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >> simp[] >> metis_tac[]
QED

Theorem dft_swap_fn_ssa_form:
  dft_swap_fn f g ==> (ssa_form g <=> ssa_form f)
Proof
  strip_tac >> drule dft_swap_fn_insts_perm >>
  disch_then (mp_tac o MATCH_MP PERM_FLAT o
    MATCH_MP (Q.ISPEC `\i:instruction. i.inst_outputs` PERM_MAP)) >>
  metis_tac[ssa_form_def, ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem dft_swap_block_succs:
  bb_well_formed bb /\ dft_swap_list bb.bb_instructions insts ==>
  bb_succs (bb with bb_instructions := insts) = bb_succs bb
Proof
  strip_tac >>
  `insts <> []` by
    (drule dft_swap_list_perm >>
     gvs[bb_well_formed_def] >> metis_tac[PERM_NIL]) >>
  `LAST bb.bb_instructions = LAST insts` by
    (irule dft_swap_list_last >> gvs[bb_well_formed_def]) >>
  simp[bb_succs_def] >> Cases_on `insts` >> gvs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem dft_swap_fn_cfg:
  wf_function f /\ dft_swap_fn f g ==> fn_cfg_edge g = fn_cfg_edge f
Proof
  rw[dft_swap_fn_def] >>
  `bb_well_formed bb` by
    (gvs[wf_function_def, MEM_APPEND] >> metis_tac[]) >>
  drule_all dft_swap_block_succs >> strip_tac >>
  simp[FUN_EQ_THM, fn_cfg_edge_def, MEM_APPEND,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem dft_swap_fn_reachable:
  wf_function f /\ dft_swap_fn f g ==> fn_reachable g = fn_reachable f
Proof
  strip_tac >> drule_all dft_swap_fn_cfg >> strip_tac >>
  drule dft_swap_fn_name_entry >> strip_tac >>
  simp[FUN_EQ_THM, fn_reachable_def]
QED

Theorem cfg_equal_paths[local]:
  !path. fn_cfg_edge g = fn_cfg_edge f ==>
    (is_fn_path g path <=> is_fn_path f path)
Proof
  Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def]
QED

Theorem dft_swap_fn_dominates:
  wf_function f /\ dft_swap_fn f g ==> fn_dominates g = fn_dominates f
Proof
  strip_tac >> drule_all dft_swap_fn_cfg >> strip_tac >>
  drule_all dft_swap_fn_reachable >> strip_tac >>
  drule dft_swap_fn_name_entry >> strip_tac >>
  `!path. is_fn_path g path <=> is_fn_path f path` by
    metis_tac[cfg_equal_paths] >>
  simp[FUN_EQ_THM, fn_dominates_def]
QED

Theorem adjacent_swap_order:
  adjacent_swap R l r /\ id_before l x y ==>
    id_before r x y \/ R x y
Proof
  rw[adjacent_swap_def] >>
  gvs[dftSsaPreserveTheory.id_before_append, dftSsaPreserveTheory.id_before_cons] >>
  metis_tac[]
QED

Theorem dft_swap_list_order:
  dft_swap_list l r /\ id_before l x y /\
  ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) ==>
  id_before r x y
Proof
  simp[dft_swap_list_def] >> strip_tac >>
  drule_all adjacent_swap_order >> simp[dft_cross_def]
QED

Theorem dft_swap_list_reverse_order:
  dft_swap_list l r /\ id_before r x y ==>
    id_before l x y \/ dft_cross y x
Proof
  rw[dft_swap_list_def, adjacent_swap_def] >>
  gvs[dftSsaPreserveTheory.id_before_append, dftSsaPreserveTheory.id_before_cons] >>
  metis_tac[]
QED

Theorem prefix_order_iff[local]:
  (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) <=>
  (!a b. id_before l a b /\ P b ==> P a)
Proof
  simp[id_before_def] >> metis_tac[]
QED

Theorem last_only_order_iff[local]:
  (!i. i < LENGTH l /\ P (EL i l) ==> i = PRE (LENGTH l)) <=>
  (!a b. id_before l a b ==> ~P a)
Proof
  eq_tac
  >- (rw[id_before_def] >> strip_tac >>
      `i < LENGTH l` by decide_tac >>
      `i = PRE (LENGTH l)` by metis_tac[] >> decide_tac) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `SUC i < LENGTH l` by decide_tac >>
  `id_before l (EL i l) (EL (SUC i) l)` by
    (simp[id_before_def] >> qexistsl [`i`, `SUC i`] >> simp[]) >>
  metis_tac[]
QED

Theorem dft_swap_block_wf:
  bb_well_formed bb /\ dft_swap_list bb.bb_instructions insts ==>
  bb_well_formed (bb with bb_instructions := insts)
Proof
  strip_tac >>
  `insts <> []` by
    (drule dft_swap_list_perm >>
     gvs[bb_well_formed_def] >> metis_tac[PERM_NIL]) >>
  `LAST bb.bb_instructions = LAST insts` by
    (irule dft_swap_list_last >> gvs[bb_well_formed_def]) >>
  gvs[bb_well_formed_def, last_only_order_iff, prefix_order_iff] >>
  conj_tac
  >- (rpt strip_tac >> drule_all dft_swap_list_reverse_order >>
      gvs[dft_cross_def] >> metis_tac[]) >>
  rpt strip_tac >> drule_all dft_swap_list_reverse_order >>
  gvs[dft_cross_def, is_pseudo_def] >> metis_tac[]
QED

Theorem dft_swap_block_pseudos:
  pseudos_prefix bb /\ dft_swap_list bb.bb_instructions insts ==>
  pseudos_prefix (bb with bb_instructions := insts)
Proof
  simp[pseudos_prefix_def, prefix_order_iff] >> rpt strip_tac >>
  drule_all dft_swap_list_reverse_order >>
  gvs[dft_cross_def] >> metis_tac[]
QED

Theorem dft_swap_fn_pseudos:
  fn_pseudos_prefix f /\ dft_swap_fn f g ==> fn_pseudos_prefix g
Proof
  rw[dft_swap_fn_def] >>
  gvs[fn_pseudos_prefix_def, MEM_APPEND] >> rpt strip_tac >>
  gvs[] >> metis_tac[dft_swap_block_pseudos]
QED

Theorem fn_inst_ids_insts[local]:
  fn_inst_ids_distinct f <=> ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts f))
Proof
  `!bs. MAP (\i. i.inst_id) (fn_insts_blocks bs) =
     FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  simp[fn_inst_ids_distinct_def, fn_insts_def]
QED

Theorem dft_swap_fn_ids:
  dft_swap_fn f g ==> (fn_inst_ids_distinct g <=> fn_inst_ids_distinct f)
Proof
  strip_tac >> drule dft_swap_fn_insts_perm >> strip_tac >>
  `PERM (MAP (\i. i.inst_id) (fn_insts f))
        (MAP (\i. i.inst_id) (fn_insts g))` by metis_tac[PERM_MAP] >>
  metis_tac[fn_inst_ids_insts, ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem dft_swap_fn_succs_closed:
  wf_function f /\ dft_swap_fn f g ==> fn_succs_closed g
Proof
  strip_tac >> drule_all dft_swap_fn_cfg >> strip_tac >>
  drule dft_swap_fn_labels >> strip_tac >>
  gvs[fn_succs_closed_def, wf_function_def] >> rpt strip_tac >>
  `fn_cfg_edge g bb.bb_label succ` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `fn_cfg_edge f bb.bb_label succ` by metis_tac[] >>
  qpat_x_assum `fn_cfg_edge f _ _` mp_tac >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem dft_swap_fn_wf:
  wf_function f /\ dft_swap_fn f g ==> wf_function g
Proof
  strip_tac >>
  `fn_succs_closed g` by metis_tac[dft_swap_fn_succs_closed] >>
  `fn_inst_ids_distinct g` by
    metis_tac[dft_swap_fn_ids, wf_function_def] >>
  drule dft_swap_fn_labels >> strip_tac >>
  qpat_x_assum `dft_swap_fn _ _` mp_tac >>
  rw[dft_swap_fn_def] >>
  gvs[wf_function_def, fn_has_entry_def, MEM_APPEND] >>
  rpt strip_tac >> gvs[] >> metis_tac[dft_swap_block_wf]
QED

Theorem copy_phi_var_same_members[local]:
  !origin f x. copy_phi_var origin f x ==>
    !g. (!i. MEM i (fn_insts f) <=> MEM i (fn_insts g)) ==>
        copy_phi_var origin g x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >>
  metis_tac[copy_phi_var_rules]
QED

Theorem dft_swap_fn_copy_phi:
  dft_swap_fn f g ==> (copy_phi_var origin g x <=> copy_phi_var origin f x)
Proof
  strip_tac >> drule dft_swap_fn_insts_perm >> strip_tac >>
  `!i. MEM i (fn_insts f) <=> MEM i (fn_insts g)` by metis_tac[PERM_MEM_EQ] >>
  metis_tac[copy_phi_var_same_members]
QED

Theorem dft_swap_fn_opaque:
  dft_swap_fn f g ==> (opaque_use_ok g <=> opaque_use_ok f)
Proof
  strip_tac >>
  `!origin x. copy_phi_var origin g x <=> copy_phi_var origin f x` by
    metis_tac[dft_swap_fn_copy_phi] >>
  drule dft_swap_fn_insts_perm >>
  disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
  simp[opaque_use_ok_def, gas_var_def, retpc_var_def] >> metis_tac[]
QED

Theorem dft_swap_fn_shape:
  fn_shape_ok f /\ dft_swap_fn f g ==> fn_shape_ok g
Proof
  strip_tac >>
  `opaque_use_ok g` by metis_tac[dft_swap_fn_opaque, fn_shape_ok_def] >>
  `EVERY inst_shape_ok (fn_insts g)` by
    metis_tac[dft_swap_fn_insts_every, fn_shape_ok_def] >>
  drule dft_swap_fn_name_entry >> strip_tac >>
  drule dft_swap_fn_labels >> strip_tac >>
  `EVERY (\l. ~reserved_label l) (fn_labels f)` by
    gvs[fn_shape_ok_def, fn_labels_def, EVERY_MAP] >>
  `EVERY (\l. ~reserved_label l) (fn_labels g)` by metis_tac[] >>
  qpat_x_assum `EVERY _ (fn_labels g)` mp_tac >>
  pure_rewrite_tac[fn_labels_def, EVERY_MAP, combinTheory.o_DEF] >>
  strip_tac >> gvs[fn_shape_ok_def]
QED

Theorem dft_swap_fn_blocks:
  dft_swap_fn f g ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    RC dft_swap_list bb.bb_instructions bb'.bb_instructions)
    f.fn_blocks g.fn_blocks
Proof
  `!bs. LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
      RC dft_swap_list bb.bb_instructions bb'.bb_instructions) bs bs` by
    (Induct >> simp[RC_DEF]) >>
  rw[dft_swap_fn_def] >>
  gvs[LIST_REL_APPEND_EQ, RC_DEF]
QED

Theorem dft_swap_block_members:
  RC dft_swap_list l r ==> (!i. MEM i l <=> MEM i r)
Proof
  simp[RC_DEF] >> strip_tac >> gvs[] >>
  metis_tac[dft_swap_list_perm, PERM_MEM_EQ]
QED

Theorem dft_swap_block_order:
  RC dft_swap_list l r /\ id_before l x y /\
  ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) ==>
  id_before r x y
Proof
  simp[RC_DEF] >> metis_tac[dft_swap_list_order]
QED

Theorem dft_swap_fn_block_forward:
  dft_swap_fn f g /\ MEM bb f.fn_blocks ==>
  ?bb'. MEM bb' g.fn_blocks /\ bb'.bb_label = bb.bb_label /\
        RC dft_swap_list bb.bb_instructions bb'.bb_instructions
Proof
  rw[dft_swap_fn_def] >> gvs[MEM_APPEND]
  >- (qexists_tac `bb` >> simp[RC_DEF])
  >- (qexists_tac `bb with bb_instructions := insts` >> simp[RC_DEF]) >>
  qexists_tac `bb` >> simp[RC_DEF]
QED

Theorem dft_swap_fn_block_backward:
  dft_swap_fn f g /\ MEM bb' g.fn_blocks ==>
  ?bb. MEM bb f.fn_blocks /\ bb'.bb_label = bb.bb_label /\
        RC dft_swap_list bb.bb_instructions bb'.bb_instructions
Proof
  rw[dft_swap_fn_def] >> gvs[MEM_APPEND] >>
  metis_tac[RC_DEF, basic_block_accfupds, basic_block_fupdfupds]
QED

Theorem dft_swap_fn_available:
  wf_function f /\ dft_swap_fn f g /\
  MEM bb f.fn_blocks /\ MEM bb' g.fn_blocks /\
  bb'.bb_label = bb.bb_label /\
  RC dft_swap_list bb.bb_instructions bb'.bb_instructions /\
  def_available_at f bb use v /\
  (case use of NONE => T | SOME u => MEM v (inst_uses u)) ==>
  def_available_at g bb' use v
Proof
  strip_tac >>
  `wf_function g` by metis_tac[dft_swap_fn_wf] >>
  `fn_dominates g = fn_dominates f` by metis_tac[dft_swap_fn_dominates] >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  drule_all dft_swap_fn_block_forward >> strip_tac >>
  rename1 `RC dft_swap_list def_bb.bb_instructions db.bb_instructions` >>
  qexistsl [`db`, `def_inst`] >>
  `MEM def_inst db.bb_instructions` by metis_tac[dft_swap_block_members] >>
  simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[wf_fn_blocks_same_label_eq] >>
  qpat_x_assum `def_bb = bb` SUBST_ALL_TAC >>
  Cases_on `use` >> fs[] >>
  rename1 `MEM v (inst_uses u)` >>
  `~DISJOINT (set (inst_defs def_inst)) (set (inst_uses u))` by
    (simp[inst_defs_def, pred_setTheory.DISJOINT_DEF,
          pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `id_before bb.bb_instructions def_inst u` by
    (simp[id_before_def] >> metis_tac[]) >>
  `id_before bb'.bb_instructions def_inst u` by
    metis_tac[dft_swap_block_order] >>
  gvs[id_before_def] >> metis_tac[]
QED

Theorem dft_swap_fn_phi:
  wf_function f /\ dft_swap_fn f g /\ bb'.bb_label = bb.bb_label /\
  phi_edge_uses_wf f bb inst ==> phi_edge_uses_wf g bb' inst
Proof
  strip_tac >>
  `fn_cfg_edge g = fn_cfg_edge f` by metis_tac[dft_swap_fn_cfg] >>
  qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
  simp[phi_edge_uses_wf_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all dft_swap_fn_block_forward >> strip_tac >>
  rename1 `RC dft_swap_list pred_bb.bb_instructions pb.bb_instructions` >>
  qexists_tac `pb` >> simp[] >>
  conj_tac >- (qexists_tac `(pred,v)` >> simp[]) >>
  irule dft_swap_fn_available >> simp[] >>
  qexistsl [`pred_bb`, `f`] >> simp[]
QED

Theorem dft_swap_fn_def_dominates:
  wf_function f /\ dft_swap_fn f g /\ def_dominates_uses f ==>
  def_dominates_uses g
Proof
  strip_tac >> simp[def_dominates_uses_def] >> rpt strip_tac >>
  drule_all dft_swap_fn_block_backward >> strip_tac >>
  rename1 `RC dft_swap_list src.bb_instructions bb.bb_instructions` >>
  `MEM inst src.bb_instructions` by metis_tac[dft_swap_block_members] >>
  qpat_x_assum `def_dominates_uses f` mp_tac >>
  simp[def_dominates_uses_def] >>
  disch_then (qspecl_then [`src`, `inst`] mp_tac) >> simp[] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[] >> metis_tac[dft_swap_fn_phi]) >>
  simp[] >> strip_tac >> rpt strip_tac >>
  irule dft_swap_fn_available >> simp[inst_uses_def, dftCorrectnessTheory.MEM_operand_vars_iff] >>
  qexistsl [`src`, `f`] >> simp[]
QED

Theorem dft_swap_fn_ssa:
  wf_function f /\ wf_ssa f /\ dft_swap_fn f g ==> wf_ssa g
Proof
  strip_tac >>
  gvs[wf_ssa_def] >> conj_tac
  >- metis_tac[dft_swap_fn_ssa_form] >>
  metis_tac[dft_swap_fn_def_dominates]
QED

Theorem dft_swap_fn_invariant:
  dft_swap_invariant L f /\ dft_swap_fn f g ==> dft_swap_invariant L g
Proof
  simp[dft_swap_invariant_def] >> strip_tac >> rpt conj_tac
  >- metis_tac[dft_swap_fn_wf]
  >- metis_tac[dft_swap_fn_ssa]
  >- metis_tac[dft_swap_fn_inst_wf]
  >- metis_tac[dft_swap_fn_pseudos]
  >- metis_tac[dft_swap_fn_shape]
  >- metis_tac[dft_swap_fn_insts_every] >>
  metis_tac[dft_swap_fn_labels_bound]
QED
