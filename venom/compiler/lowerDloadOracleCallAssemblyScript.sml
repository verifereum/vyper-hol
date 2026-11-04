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

