(*
 * When a unit label map is the identity on code.
 *
 * apply_unit_label_map rewrites every Label operand of every function by
 * the resolved map.  If no Label operand of any function is a source of
 * the map, the context is unchanged (apply_unit_label_map_context); the
 * data section may still change.
 *)
Theory unitLabelMapIdentity
Ancestors
  unitLabelMap cfgTransform venomInst alist list

Theorem resolve_label_entries_sources:
  !entries resolved.
    resolve_label_entries label_map fuel entries = SOME resolved ==>
    MAP FST resolved = MAP FST entries
Proof
  Induct >> simp[resolve_label_entries_def] >>
  Cases >> simp[resolve_label_entries_def, AllCaseEqs()] >>
  rw[] >> simp[]
QED

Theorem resolve_label_map_sources:
  resolve_label_map label_map = SOME resolved ==>
  MAP FST resolved = MAP FST label_map
Proof
  simp[resolve_label_map_def, AllCaseEqs()] >>
  metis_tac[resolve_label_entries_sources]
QED

Theorem subst_label_map_op_id:
  ~MEM l (MAP FST label_map) ==>
  subst_label_map_op label_map (Label l) = Label l
Proof
  strip_tac >> `ALOOKUP label_map l = NONE` by simp[ALOOKUP_NONE] >>
  simp[subst_label_map_op_def]
QED

Theorem MAP_eq_self:
  !l. (!x. MEM x l ==> f x = x) ==> MAP f l = l
Proof
  Induct >> simp[]
QED

Theorem subst_label_map_inst_id:
  (!l. MEM (Label l) inst.inst_operands ==> ~MEM l (MAP FST label_map)) ==>
  subst_label_map_inst label_map inst = inst
Proof
  rw[subst_label_map_inst_def] >>
  simp[venomInstTheory.instruction_component_equality] >>
  irule MAP_eq_self >> Cases >> simp[subst_label_map_op_def] >> strip_tac >>
  rename1 `MEM (Label l) _` >>
  `ALOOKUP label_map l = NONE` by simp[ALOOKUP_NONE] >> simp[]
QED

Theorem MEM_fn_insts_blocks:
  !bbs. MEM inst (fn_insts_blocks bbs) <=>
        ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem MEM_fn_insts:
  MEM inst (fn_insts fn) <=>
  ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks]
QED

Theorem subst_label_map_fn_id:
  (!inst l. MEM inst (fn_insts fn) /\ MEM (Label l) inst.inst_operands ==>
            ~MEM l (MAP FST label_map)) ==>
  subst_label_map_fn label_map fn = fn
Proof
  rw[subst_label_map_fn_def] >>
  simp[venomInstTheory.ir_function_component_equality] >>
  irule MAP_eq_self >> rpt strip_tac >> rename1 `MEM bb fn.fn_blocks` >>
  simp[subst_label_map_block_def,
       venomInstTheory.basic_block_component_equality] >>
  irule MAP_eq_self >> rpt strip_tac >>
  irule subst_label_map_inst_id >> rpt strip_tac >>
  fs[MEM_fn_insts] >> metis_tac[]
QED

Theorem apply_unit_label_map_context:
  apply_unit_label_map label_map unit = SOME unit' /\
  (!fn inst l.
     MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
     MEM (Label l) inst.inst_operands ==>
     ~MEM l (MAP FST label_map)) ==>
  unit'.cu_context = unit.cu_context
Proof
  simp[apply_unit_label_map_def, AllCaseEqs()] >> strip_tac >>
  drule resolve_label_map_sources >> strip_tac >>
  gvs[apply_resolved_unit_label_map_def] >>
  simp[venomInstTheory.venom_context_component_equality] >>
  irule MAP_eq_self >> rpt strip_tac >> irule subst_label_map_fn_id >>
  metis_tac[]
QED
