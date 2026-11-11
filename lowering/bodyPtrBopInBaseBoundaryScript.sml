Theory bodyPtrBopInBaseBoundary
Ancestors bodyPtrDefs bodyPtrBopInLoopContract bodyPtrBopInStackMemory
  exprLowering compileEnv context valueEncoding ptrDiscipline venomState finite_map
  valueEncodingProps loweringPosts vyperValue vyperAST
  stmtAppendStorageRunPtr ptrSafeRun venomExecSemantics venomInst codegenRel contextCodegenRel

(* A memory aggregate's arr_op is a register only when its footprint is
   positive. Do not infer register shape from cleanliness alone. *)
Theorem membership_memory_positive_base:
  ptr_mem_ok cx ty v arr_op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand arr_op s = SOME bw /\ val_footprint tv v <> 0 ==>
  ?x. arr_op = Var x /\ lookup_var x s = SOME bw
Proof
  simp[ptr_mem_ok_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[eval_operand_def]
QED

(* The default location in the actual compiler is precisely memory. *)
Theorem membership_stack_memory_compile:
  compile_var_array_membership cenv needle (StackValue ann arr_op) (ArrayT et bd) is_in =
  compile_var_array_membership cenv needle
    (LocatedValue (ArrayT et bd) (mk_ptr arr_op LocMemory)) (ArrayT et bd) is_in
Proof
  Cases_on `bd` >>
  simp[compile_var_array_membership_def, vv_location_def, vv_operand_def, mk_ptr_def]
QED

(* Labels can evaluate: the frame preserves them because label bindings are
   not mutable loop registers. This is not a non-Label side condition. *)
Theorem membership_base_label_evaluates[local]:
  eval_operand (Label lbl) (s with vs_labels := s.vs_labels |+ (lbl,bw)) = SOME bw
Proof
  simp[eval_operand_def, FLOOKUP_UPDATE]
QED

Theorem membership_base_literal_evaluates[local]:
  eval_operand (Lit bw) s = SOME bw /\ op_taint tn (Lit bw) = {} /\
  op_prov G (Lit bw) = NONE
Proof
  simp[eval_operand_def, op_taint_def, op_prov_def]
QED

Theorem membership_evaluated_array_footprint_positive:
  evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV tv bd) ==>
  0 < val_footprint (ArrayTV tv bd) (ArrayV av)
Proof
  strip_tac >> simp[val_footprint_def] >>
  irule (cj 1 type_memory_size_pos) >>
  Cases_on `bd` >>
  gvs[Once evaluate_type_def, AllCaseEqs(), type_slot_size_def, bound_length_def]
QED

Theorem membership_located_memory_base_var:
  ptr_vv_ok cx (ArrayT et bd) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  eval_operand p.ptr_operand s = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) ==>
  ?x. p.ptr_operand = Var x /\ lookup_var x s = SOME bw
Proof
  strip_tac >>
  `0 < val_footprint (ArrayTV tv bd) (ArrayV av)` by
    metis_tac[membership_evaluated_array_footprint_positive] >>
  irule membership_memory_positive_base >>
  fs[ptr_vv_ok_def] >> goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* These primitive header boundaries deliberately accept all constructors.
   Literals and labels are not converted to synthetic target registers. *)
Theorem membership_slot_header_operand_step:
  eval_operand arr_op s = SOME bw /\ op_taint tn arr_op = {} /\
  ~ctx_has_dalloca ctx ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s =
    OK (update_var out (if tr then tload bw s else sload bw s) s) /\
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s =
    OK (update_var out (if tr then tload bw s else sload bw s) s)` by
    (Cases_on `tr` >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >> simp[exec_read1_def]) >>
  simp[] >> irule append_scalar_inst_check >>
  simp[update_var_def] >> Cases_on `tr` >> simp[]
QED

Theorem membership_code_header_operand_step:
  eval_operand arr_op s = SOME bw /\ op_taint tn arr_op = {} /\
  ~ctx_has_dalloca ctx /\
  value = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n bw) s.vs_data_section ++ REPLICATE 32 0w)) ==>
  step_inst_base (mk_inst id DLOAD [arr_op] [out]) s = OK (update_var out value s) /\
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id DLOAD [arr_op] [out]) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id DLOAD [arr_op] [out]) s = OK (update_var out value s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >> simp[exec_read1_def]) >>
  simp[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]
QED
