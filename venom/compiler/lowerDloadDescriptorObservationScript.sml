(* Descriptor-level observations, independent of successful execution. *)
(* FIRST [gvs ...] after Cases_on on the opcode runs gvs as one timed step
   per opcode goal: over all ~200 goals at once it takes over 2 s. *)
Theory lowerDloadDescriptorObservation
Ancestors lowerDloadOracleCallAssembly memLocDefs list venomInst
          ptrDiscipline lowerDloadSafetyValues pred_set words pointerConfinedDefs

Theorem ld_descriptor_offset_operand:
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) ==>
  MEM ops.iao_ofst inst.inst_operands /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  metis_tac[MEM_REVERSE, MEM]
QED

Theorem ld_descriptor_size_operand:
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME szop ==>
  (?w. szop = Lit w) \/ MEM szop inst.inst_operands
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  metis_tac[MEM_REVERSE, MEM]
QED

Theorem ld_descriptor_size_clean:
  taint_ok fn tn inst s /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME szop ==> op_taint tn szop = {}
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  FIRST [rename1 `op_taint tn (Lit _) = {}` >> simp[op_taint_def],
         irule ld_numeric_operand_untainted >>
         qexistsl_tac [`fn`,`inst`,`s`] >> simp[] >>
         metis_tac[MEM, MEM_REVERSE]]
QED

Theorem ld_descriptor_offset_clean:
  taint_ok fn tn inst s /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) ==>
  op_taint tn ops.iao_ofst = {}
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  fs[taint_ok_def] >> metis_tac[MEM, MEM_REVERSE]
QED

Theorem ld_descriptor_size_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME (Var v) ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  qpat_x_assum `ptr_use_ok _ _ _`
    (mp_tac o REWRITE_RULE [ptr_use_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  (impl_tac >- (simp[is_pointer_preserving_op_def] >>
                 metis_tac[MEM_REVERSE, MEM])) >>
  strip_tac >>
  gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `FILTER _ _ = _`
    (mp_tac o AP_TERM ``REVERSE : operand list -> operand list``) >>
  pure_rewrite_tac[GSYM FILTER_REVERSE] >>
  asm_rewrite_tac[FILTER, REVERSE_DEF, CONS_11] >> simp[]
QED

Theorem ld_descriptor_size_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  tn.t_var = f.lf_tv /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME szop ==>
  eval_operand szop f.lf_src = eval_operand szop f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn szop = {}` by metis_tac[ld_descriptor_size_clean] >>
  `op_prov f.lf_H szop = NONE` by
    (irule ld_vars_nonpointer_provenance >>
     metis_tac[ld_descriptor_size_nonpointer]) >>
  `!v. szop = Var v ==> MEM v (fn_ir_vars f.lf_fn) /\
      ~retpc_var f.lf_fn v /\
      (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}` by
    (gen_tac >> disch_then SUBST_ALL_TAC >>
     `MEM (Var v) inst.inst_operands` by
       (`(?w. Var v = Lit w) \/ MEM (Var v) inst.inst_operands` by
          metis_tac[ld_descriptor_size_operand] >> gvs[]) >>
     conj_tac >- metis_tac[ld_inst_input_ir] >> conj_tac
     >- metis_tac[ld_numeric_operand_nonopaque, ld_descriptor_offset_operand] >>
     gvs[op_taint_def]) >>
  irule ld_vars_operand_equal >> metis_tac[]
QED

Theorem ld_descriptor_offset_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  eval_operand ops.iao_ofst f.lf_tgt = SOME y ==>
  ?x. eval_operand ops.iao_ofst f.lf_src = SOME x /\
    (op_prov f.lf_H ops.iao_ofst = NONE ==> x = y) /\
    (!a. op_prov f.lf_H ops.iao_ofst = SOME a ==>
         ld_wordrel A (SOME a) x y)
Proof
  strip_tac >> irule ld_numeric_operand_observation >>
  metis_tac[ld_descriptor_offset_operand, ld_descriptor_offset_clean]
QED
