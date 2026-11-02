(* Runtime guards used by DFT instruction swaps. *)
Theory dftGuards
Ancestors
  venomState venomExecSemantics venomWf finite_map list

Theorem dft_operand_defined:
  (!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) ops ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem dft_exec_pure1_total:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  gvs[exec_pure1_def]
QED

Theorem dft_exec_pure2_total:
  LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_pure2_def]
QED

Theorem dft_exec_pure3_total:
  LENGTH inst.inst_operands = 3 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure3 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2; op3]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  `?v3. eval_operand op3 s = SOME v3` by metis_tac[] >>
  simp[exec_pure3_def]
QED

Theorem dft_exec_read0_total:
  LENGTH inst.inst_outputs = 1 ==> ?t. exec_read0 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> simp[exec_read0_def]
QED

Theorem dft_exec_read1_total:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_read1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >>
  gvs[exec_read1_def]
QED

Theorem dft_exec_write2_total:
  LENGTH inst.inst_operands = 2 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_write2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_write2_def]
QED
