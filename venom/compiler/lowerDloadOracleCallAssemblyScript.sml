Theory lowerDloadOracleCallAssembly
Ancestors
  lowerDloadExternalCallEffects lowerDloadSafetyWriteAssembly
  lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyUpdates
  lowerDloadSafetyRelation ptrDiscipline venomExecSemantics venomState
  memLocDefs pointerConfinedDefs venomInst finite_map pred_set list words arithmetic

(* A numeric use observes either a selected translated pointer or an
   untainted scalar.  Definedness is transported independently of value class. *)
Theorem ld_numeric_operand_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\ op_taint tn op = {} /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x /\
      (op_prov f.lf_H op = NONE ==> x = y) /\
      (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `?x. eval_operand op f.lf_src = SOME x` by
    (irule ld_write_operand_defined >> metis_tac[]) >>
  qexists_tac `x` >> simp[] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >> metis_tac[]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def] >>
  drule_all ld_vars_value >> Cases_on `FLOOKUP f.lf_H s` >>
  simp[ld_word_agree_empty]
QED


Theorem ld_filter_unique_index[local]:
  !xs x i j. FILTER ($= x) xs = [x] /\
    i < LENGTH xs /\ j < LENGTH xs /\ EL i xs = x /\ EL j xs = x ==>
    i = j
Proof
  Induct >- simp[] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `x = h`
  >- (`FILTER ($= h) xs = []` by
        (qpat_x_assum `FILTER _ (_::_) = _` mp_tac >>
         asm_rewrite_tac[FILTER, CONS_11]) >>
      `!k. k < LENGTH xs ==> EL k xs <> h` by
        (qpat_x_assum `FILTER _ _ = []` mp_tac >>
         simp[FILTER_EQ_NIL, EVERY_MEM, MEM_EL] >> metis_tac[]) >>
      Cases_on `i` >> Cases_on `j` >> gvs[EL]) >>
  `FILTER ($= x) xs = [x]` by
    (qpat_x_assum `FILTER _ (_::_) = _` mp_tac >> asm_rewrite_tac[FILTER]) >>
  Cases_on `i` >> Cases_on `j` >> gvs[EL] >>
  first_x_assum irule >> simp[]
QED

Theorem ld_ptr_use_scalar_index:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> INVOKE /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ] /\
  mem_read_ops inst = SOME rd /\ mem_write_ops inst = SOME wr /\
  rd.iao_ofst = EL ri inst.inst_operands /\
  wr.iao_ofst = EL wi inst.inst_operands /\
  i < LENGTH inst.inst_operands /\ ri < LENGTH inst.inst_operands /\
  wi < LENGTH inst.inst_operands /\ i <> ri /\ i <> wi /\
  EL i inst.inst_operands = Var v ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  qpat_x_assum `ptr_use_ok _ _ _`
    (mp_tac o REWRITE_RULE [ptr_use_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
    disj1_tac >> fs[])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  gvs[Excl "FILTER"]
  >- (`i = wi` by
        (irule (INST_TYPE [``:'a`` |-> ``:operand``] ld_filter_unique_index) >>
         qexistsl_tac [`Var v`,`inst.inst_operands`] >> simp[]) >> fs[]) >>
  `i = ri` by
    (irule (INST_TYPE [``:'a`` |-> ``:operand``] ld_filter_unique_index) >>
     qexistsl_tac [`Var v`,`inst.inst_operands`] >> simp[]) >> fs[]
QED

Theorem ld_oracle_call_scalar_index:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\ MEM i [0;1;2;4;6]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [g;a;ao;az;ro;rz] /\ MEM i [0;1;3;5])) /\
  EL i inst.inst_operands = Var x ==>
  x NOTIN fn_pv P fn
Proof
  strip_tac >> (irule ld_ptr_use_scalar_index >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`i`,`inst`] >>
  simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  qexistsl_tac [`if inst.inst_opcode = CALL then 3 else 2`,
                `if inst.inst_opcode = CALL then 5 else 4`] >>
  simp[EL] >> fs[] >> gvs[])
QED
