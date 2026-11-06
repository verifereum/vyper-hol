Theory o1MakeSsaPrefixNames
Ancestors
  o1MakeSsaVisitNames o1MakeSsaReaching o1MakeSsaFormats
  makeSsaCurrentDefs venomInst list pair o1MakeSsaCfg

Theorem current_operand_var_at:
  !ops j x. j < LENGTH ops /\ EL j ops = Var x ==>
    EL j (rename_current_operands rs ops) = Var (latest_current_name rs x)
Proof
  Induct >> simp[] >> Cases_on `h` >> Cases_on `j` >>
  simp[rename_current_operands_def] >> metis_tac[]
QED

Theorem current_inst_operand_var_at:
  rename_current_inst s rs inst = (rt,t,out) /\
  inst.inst_opcode <> PHI /\ j < LENGTH inst.inst_operands /\
  EL j inst.inst_operands = Var x ==>
    EL j out.inst_operands = Var (latest_current_name rs x)
Proof
  simp[rename_current_inst_def] >> strip_tac >>
  pairarg_tac >> gvs[] >> metis_tac[current_operand_var_at]
QED

Theorem block_operand_prefix_name:
  !insts s rs rt t outs i j x.
    rename_current_block_insts s rs insts = (rt,t,outs) /\
    i < LENGTH insts /\ (EL i insts).inst_opcode <> PHI /\
    j < LENGTH (EL i insts).inst_operands /\
    EL j (EL i insts).inst_operands = Var x ==>
    EL j (EL i outs).inst_operands =
      Var (last_name x (latest_current_name rs x)
        (block_output_pairs (TAKE i insts) (TAKE i outs)))
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `i`
  >- (gvs[block_output_pairs_def, last_name_def] >>
      metis_tac[current_inst_operand_var_at]) >>
  gvs[] >>
  `LENGTH rest' = LENGTH insts` by metis_tac[rename_current_block_insts_length] >>
  simp[block_output_pairs_def, ZIP, last_name_append] >>
  first_x_assum drule_all >>
  drule inst_last_name >> disch_then (qspec_then `x` assume_tac) >>
  simp[block_output_pairs_def]
QED
