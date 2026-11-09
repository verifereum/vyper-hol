Theory makeSsaCurrentPrefixEndpoints
Ancestors
  makeSsaCurrentPrefixMaps list

Theorem current_prefix_back_endpoint_cases:
  !xs M z x. current_prefix_back xs M z x ==>
    (FLOOKUP M z = SOME x /\
      EVERY (\inst. ~MEM z inst.inst_outputs) xs) \/
    ?before inst after dst.
      xs = before ++ inst::after /\
      EVERY (\i. ~MEM z i.inst_outputs) before /\
      inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
      inst.inst_operands = [Var z] /\ current_prefix_back after M dst x
Proof
  Induct >> simp[current_prefix_back_def] >>
  rpt gen_tac >> simp[current_prefix_pull_def] >> strip_tac
  >- (disj2_tac >> qexistsl_tac [`[]`, `h`, `xs`, `d`] >> simp[]) >>
  first_x_assum drule >> strip_tac
  >- (disj1_tac >> simp[]) >>
  disj2_tac >> qexistsl_tac [`h::before`, `inst`, `after`, `dst`] >> simp[]
QED

Theorem current_prefix_back_range:
  !xs M z x. current_prefix_back xs M z x ==>
    ?n. FLOOKUP M n = SOME x
Proof
  Induct >> simp[current_prefix_back_def, current_prefix_pull_def] >>
  metis_tac[]
QED
