(* Kind boundaries shared by symbolic instruction and control-flow proofs. *)
Theory symInstKinds
Ancestors
  codegenSymRel genFrameSim frameViewFacts unitShapeDefs
  contextCodegenRel frameRel asmSymSem list

Theorem op_kind_ok_word:
  ~retpc_var fn x /\ ~code_end_var fn x ==>
  op_kind_ok fn ret (Var x) (Val w)
Proof
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem ordinary_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode <> ASSIGN /\
  (~?op. inst.inst_opcode = ADD /\
         inst.inst_operands = [op; Label "code_end"]) ==>
  ~code_end_var fn x
Proof
  metis_tac[code_end_var_def_inst]
QED

Theorem ordinary_output_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode <> RETPC_PARAM /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  (~?op. inst.inst_opcode = ADD /\
         inst.inst_operands = [op; Label "code_end"]) ==>
  op_kind_ok fn ret (Var x) (Val w)
Proof
  metis_tac[op_kind_ok_word, noncopy_output_not_retpc,
            ordinary_output_not_code_end]
QED

Theorem spill_region_labels_outside_closure:
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP after b = FLOOKUP before b) ==>
  !b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP after b = FLOOKUP before b
Proof
  metis_tac[closure_spill_byte_own]
QED

Theorem spill_disjoint_range_not_context:
  (len = 0 \/ !r. MEM r cplan.cp_regions ==>
      off + len <= r.sr_spill_base \/ r.sr_spill_end <= off) /\
  in_mem_range off len b ==> ~context_spill_byte cplan b
Proof
  rw[in_mem_range_def, context_spill_byte_def] >> gvs[] >>
  spose_not_then strip_assume_tac >> first_x_assum drule >> decide_tac
QED

Theorem spill_disjoint_ranges_no_labels:
  EVERY (\(off,len). len = 0 \/
    !r. MEM r cplan.cp_regions ==>
        off + len <= r.sr_spill_base \/ r.sr_spill_end <= off) ranges /\
  (!b. b IN FDOM labs ==> context_spill_byte cplan b) /\
  MEM (off,len) ranges /\ in_mem_range off len b ==>
  b NOTIN FDOM labs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e ranges ==> _` drule >> simp[] >>
  metis_tac[spill_disjoint_range_not_context, arithmeticTheory.ADD_COMM]
QED

Theorem source_read_ranges_no_labels:
  source_memory_reads_disjoint cplan inst vs /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  MEM (off,len) (source_memory_read_ranges inst vs) /\
  in_mem_range off len b ==>
  b NOTIN FDOM ss.sym_mem_labels
Proof
  metis_tac[spill_disjoint_ranges_no_labels, sym_kinds_ok_def,
            source_memory_reads_disjoint_def]
QED

Theorem source_write_ranges_no_labels:
  context_source_memory_writes_disjoint cplan inst vs /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  MEM (off,len) (source_memory_write_ranges inst vs) /\
  in_mem_range off len b ==>
  b NOTIN FDOM ss.sym_mem_labels
Proof
  metis_tac[spill_disjoint_ranges_no_labels, sym_kinds_ok_def,
            context_source_memory_writes_disjoint_def]
QED

Theorem assign_output_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
  (code_end_var fn x <=> code_end_var fn y)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all code_end_var_def_inst >> simp[]) >>
  strip_tac >> irule code_end_var_assign >> metis_tac[]
QED

Theorem assign_var_output_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
  (op_kind_ok fn ret (Var x) sv <=> op_kind_ok fn ret (Var y) sv)
Proof
  strip_tac >> drule_all assign_output_retpc >>
  drule_all assign_output_code_end >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem assign_lit_output_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Lit v] ==>
  (op_kind_ok fn ret (Var x) sv <=> op_kind_ok fn ret (Lit v) sv)
Proof
  strip_tac >>
  `~retpc_var fn x /\ ~code_end_var fn x` by
    (conj_tac >> strip_tac
     >- (drule_all retpc_var_output_cases >> simp[]) >>
     drule_all code_end_var_def_inst >> simp[]) >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem ordinary_input_not_code_end:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ MEM (Var x) inst.inst_operands /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> CODECOPY ==>
  ~code_end_var fn x
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `label_flow_ok ctx`
    (mp_tac o REWRITE_RULE [label_flow_ok_def]) >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

Theorem phi_var_output_kind:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  MEM (Var y) inst.inst_operands ==>
  (op_kind_ok fn ret (Var x) sv <=> op_kind_ok fn ret (Var y) sv)
Proof
  strip_tac >>
  `~code_end_var fn x` by
    (drule_at (Pat `MEM inst (fn_insts fn)`) ordinary_output_not_code_end >>
     simp[] >> metis_tac[]) >>
  `~code_end_var fn y` by
    (drule_at (Pat `MEM inst (fn_insts fn)`) ordinary_input_not_code_end >>
     simp[] >> metis_tac[]) >>
  drule_all frameViewFactsTheory.phi_output_retpc >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem op_kind_ok_numeric:
  ~is_label_operand op /\
  (!x. op = Var x ==> ~retpc_var fn x /\ ~code_end_var fn x) ==>
  (op_kind_ok fn ret op sv <=> ?w. sv = Val w)
Proof
  Cases_on `op` >>
  simp[stackPlanTypesTheory.is_label_operand_def, op_kind_ok_def,
       stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem code_end_add_output_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"] /\
  MEM x inst.inst_outputs ==>
  (op_kind_ok fn ret (Var x) sv <=> ?d. sv = Lab "code_end" d)
Proof
  strip_tac >>
  `code_end_var fn x /\ ~retpc_var fn x` by
    (conj_asm1_tac
     >- (irule code_end_var_seed >> metis_tac[]) >>
     metis_tac[code_end_var_not_retpc_var]) >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem code_end_add_offset_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"] ==>
  eval_operand op (frame_view fn ra vs with vs_memory := m) =
  eval_operand op vs
Proof
  strip_tac >> irule eval_operand_frame_view >> gen_tac >> strip_tac >>
  irule ordinary_operand_not_retpc >> simp[] >> qexists `inst` >> simp[]
QED
