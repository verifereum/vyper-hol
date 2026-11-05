Theory concretizeStepRetpc
Ancestors
  concretizeStepStructure unitShapeDefs concretizeMemLocDefs
  passSharedDefs passSimulationDefs venomInst venomWf unitLabelMapIdentity list

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

Theorem concretize_positions_var_operand:
  MEM (Var x) (concretize_inst_with_positions p i).inst_operands ==>
  concretize_inst_with_positions p i = i
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
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
