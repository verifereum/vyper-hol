Theory concretizeStepRetpc
Ancestors
  concretizeStepStructure unitShapeDefs concretizeMemLocDefs
  passSharedDefs passSimulationDefs venomInst venomWf unitLabelMapIdentity list
  passTransform

Theorem concretize_positions_retained_member:
  MEM i (fn_insts fn) /\ i.inst_opcode <> ALLOCA /\ i.inst_opcode <> NOP ==>
  MEM i (fn_insts (concretize_function_with_positions p fn))
Proof
  simp[fn_insts_MEM, concretize_positions_blocks, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  qexists `bb` >> simp[] >>
  simp[clear_nops_block_def, block_map_transform_def, MEM_FILTER, MEM_MAP] >>
  qexists `i` >> simp[concretize_positions_unchanged]
QED

Theorem concretize_positions_seed:
  MEM origin [GAS; RETPC_PARAM] /\
  (concretize_inst_with_positions p i).inst_opcode = origin ==>
  concretize_inst_with_positions p i = i
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_copy_phi_forward:
  !origin fn x. copy_phi_var origin fn x ==>
  !p. MEM origin [GAS; RETPC_PARAM] ==>
    copy_phi_var origin (concretize_function_with_positions p fn) x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >>
  `MEM inst (fn_insts (concretize_function_with_positions p fn))` by
    (irule concretize_positions_retained_member >> simp[] >> gvs[]) >>
  metis_tac[copy_phi_var_rules]
QED

Theorem concretize_positions_copy_phi_backward:
  !origin g x. copy_phi_var origin g x ==>
  !fn p. g = concretize_function_with_positions p fn /\
    MEM origin [GAS; RETPC_PARAM] ==> copy_phi_var origin fn x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `MEM inst (fn_insts _)`
    (mp_tac o REWRITE_RULE [fn_insts_MEM]) >> strip_tac >>
  drule_all concretize_positions_inst_preimage >> strip_tac >> gvs[]
  >~ [`(concretize_inst_with_positions p oldi).inst_opcode = GAS`]
  >- (`concretize_inst_with_positions p oldi = oldi` by
         (irule concretize_positions_seed >> qexists `GAS` >> simp[]) >>
       gvs[] >> metis_tac[copy_phi_var_rules, fn_insts_MEM])
  >~ [`(concretize_inst_with_positions p oldi).inst_opcode = RETPC_PARAM`]
  >- (`concretize_inst_with_positions p oldi = oldi` by
         (irule concretize_positions_seed >> qexists `RETPC_PARAM` >> simp[]) >>
       gvs[] >> metis_tac[copy_phi_var_rules, fn_insts_MEM]) >>
  `?z. MEM (Var z) (concretize_inst_with_positions p oldi).inst_operands` by
    (simp[] >> metis_tac[]) >>
  drule concretize_positions_var_operand >> strip_tac >> gvs[] >>
  metis_tac[copy_phi_var_rules, fn_insts_MEM]
QED

Theorem concretize_positions_copy_phi:
  MEM origin [GAS; RETPC_PARAM] ==>
  (copy_phi_var origin (concretize_function_with_positions p fn) x <=>
   copy_phi_var origin fn x)
Proof
  metis_tac[concretize_positions_copy_phi_forward,
            concretize_positions_copy_phi_backward]
QED

Theorem concretize_positions_opaque_use:
  opaque_use_ok fn ==> opaque_use_ok (concretize_function_with_positions p fn)
Proof
  simp[opaque_use_ok_def] >> rpt strip_tac >>
  qpat_x_assum `MEM inst (fn_insts _)`
    (mp_tac o REWRITE_RULE [fn_insts_MEM]) >> strip_tac >>
  drule_all concretize_positions_inst_preimage >> strip_tac >> gvs[] >>
  drule concretize_positions_var_operand >> strip_tac >> gvs[] >>
  fs[retpc_var_def, concretize_positions_copy_phi] >>
  metis_tac[fn_insts_MEM]
QED

Theorem concretize_positions_reachable_preds:
  wf_function fn ==>
  reachable_preds (concretize_function_with_positions p fn) = reachable_preds fn
Proof
  strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `fn_cfg_edge (concretize_function_with_positions p fn) = fn_cfg_edge fn /\
   fn_reachable (concretize_function_with_positions p fn) = fn_reachable fn` by
    simp[FUN_EQ_THM, concretize_positions_cfg_edge,
         concretize_positions_reachable] >>
  simp[FUN_EQ_THM, reachable_preds_def, concretize_positions_blocks,
       MAP_MAP_o, combinTheory.o_DEF, concretize_positions_block_label]
QED

Theorem concretize_positions_reachable_inst:
  concretize_inst_with_positions p (reachable_inst fn lbl i) =
  reachable_inst fn lbl (concretize_inst_with_positions p i)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- simp[reachable_inst_def, concretize_positions_unchanged] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (simp[reachable_inst_def, concretize_inst_with_positions_def] >>
      rpt CASE_TAC >>
      gvs[mk_assign_inst_def, mk_nop_inst_def, reachable_inst_def]) >>
  simp[reachable_inst_def, concretize_positions_unchanged]
QED

Theorem concretize_positions_reachable_list[local]:
  !xs. MAP (reachable_inst fn lbl)
    (FILTER (\i. i.inst_opcode <> NOP) (MAP (concretize_inst_with_positions p) xs)) =
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) (MAP (reachable_inst fn lbl) xs))
Proof
  Induct >> simp[concretize_positions_reachable_inst, reachable_inst_fields] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem concretize_positions_reachable_fn:
  wf_function fn ==>
  reachable_fn (concretize_function_with_positions p fn) =
  concretize_function_with_positions p (reachable_fn fn)
Proof
  strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `fn_reachable (concretize_function_with_positions p fn) = fn_reachable fn` by
    simp[FUN_EQ_THM, concretize_positions_reachable] >>
  drule concretize_positions_reachable_preds >> strip_tac >>
  `reachable_inst (concretize_function_with_positions p fn) = reachable_inst fn` by
    simp[FUN_EQ_THM, reachable_inst_def] >>
  simp[reachable_fn_def, concretize_function_with_positions_def,
    clear_nops_function_def, function_map_transform_def,
    ir_function_component_equality, concretize_positions_blocks,
    rich_listTheory.FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF,
    concretize_positions_block_label] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  simp[clear_nops_block_def, block_map_transform_def,
       basic_block_component_equality, concretize_positions_reachable_list]
QED

Theorem concretize_positions_reachable_copy_phi:
  wf_function fn /\ MEM origin [GAS; RETPC_PARAM] ==>
  (copy_phi_var origin (reachable_fn (concretize_function_with_positions p fn)) x <=>
   copy_phi_var origin (reachable_fn fn) x)
Proof
  simp[concretize_positions_reachable_fn, concretize_positions_copy_phi]
QED

Theorem concretize_positions_fn_preimage:
  MEM i (fn_insts (concretize_function_with_positions p fn)) ==>
  ?oldi. MEM oldi (fn_insts fn) /\
    i = concretize_inst_with_positions p oldi
Proof
  simp[fn_insts_MEM] >> rpt strip_tac >>
  drule_all concretize_positions_inst_preimage >> strip_tac >>
  metis_tac[]
QED

Theorem concretize_positions_outputs:
  MEM x (concretize_inst_with_positions p i).inst_outputs ==>
  MEM x i.inst_outputs
Proof
  Cases_on `i.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_retpc_writer:
  retpc_shape_ok fn /\ MEM i (fn_insts (concretize_function_with_positions p fn)) /\
  MEM x i.inst_outputs /\ retpc_var fn x ==> MEM i (fn_insts fn)
Proof
  strip_tac >> drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  drule concretize_positions_outputs >> strip_tac >>
  `oldi.inst_opcode <> ALLOCA` by
    (fs[retpc_shape_ok_def] >> strip_tac >> res_tac >> gvs[]) >>
  gvs[concretize_positions_unchanged]
QED

Theorem concretize_positions_retpc_member:
  MEM i (fn_insts (concretize_function_with_positions p fn)) /\
  MEM i.inst_opcode [PHI; RET; RETFMP; DRET] ==> MEM i (fn_insts fn)
Proof
  strip_tac >> drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  `concretize_inst_with_positions p oldi = oldi` by
    (qpat_x_assum `(concretize_inst_with_positions p oldi).inst_opcode = _` mp_tac >>
     simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
     simp[mk_assign_inst_def, mk_nop_inst_def]) >>
  gvs[]
QED

Theorem concretize_positions_retpc_shape:
  wf_function fn /\ retpc_shape_ok fn ==>
  retpc_shape_ok (concretize_function_with_positions p fn)
Proof
  strip_tac >>
  `!x. retpc_var (concretize_function_with_positions p fn) x <=> retpc_var fn x` by
    simp[retpc_var_def, concretize_positions_copy_phi] >>
  `!x. retpc_var (reachable_fn (concretize_function_with_positions p fn)) x <=>
       retpc_var (reachable_fn fn) x` by
    simp[retpc_var_def, concretize_positions_reachable_copy_phi] >>
  simp[retpc_shape_ok_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `MEM inst (fn_insts (reachable_fn fn))` by
        (irule concretize_positions_retpc_member >> simp[] >> qexists `p` >>
         gvs[concretize_positions_reachable_fn]) >>
      fs[retpc_shape_ok_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `MEM inst (fn_insts (reachable_fn fn))` by
        (irule concretize_positions_retpc_member >> simp[] >> qexists `p` >>
         gvs[concretize_positions_reachable_fn]) >>
      fs[retpc_shape_ok_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[concretize_positions_retpc_writer] >>
      fs[retpc_shape_ok_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM i (fn_insts fn) /\ MEM j (fn_insts fn)` by
    metis_tac[concretize_positions_retpc_writer] >>
  fs[retpc_shape_ok_def] >> metis_tac[]
QED
