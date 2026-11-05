Theory algebraicOptCmpCoherenceProofs
Ancestors
  algebraicOptCmpPairProofs algebraicOptMainShapeProofs
  algebraicOptCmpScanProofs dfgAnalysisProps dfgDefs venomInst list pred_set
  allocaRemapSSA

(* Only producers actually selected by this scan contribute complemented names. *)
Definition ao_cmp_flipped_def:
  ao_cmp_flipped dfg xs flips =
    {v | ?inst action. MEM inst xs /\ MEM action flips /\
      ao_cmp_flip_cert dfg inst action /\ MEM v inst.inst_outputs}
End

Theorem ao_cmp_flipped_source:
  v IN ao_cmp_flipped dfg xs flips ==>
  ?inst op w after. MEM inst xs /\
    ao_cmp_source dfg inst op w v after
Proof
  simp[ao_cmp_flipped_def, ao_cmp_flip_cert_def] >>
  rpt strip_tac >>
  `v = v'` by (gvs[ao_cmp_source_def]) >> gvs[] >>
  metis_tac[]
QED

Theorem ao_cmp_flipped_read:
  v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips /\
  MEM user (fn_insts fn) /\ MEM v (operand_vars user.inst_operands) ==>
  ?inst op w. MEM inst (fn_insts fn) /\
    ao_cmp_source (dfg_build_function fn) inst op w v user
Proof
  strip_tac >> drule ao_cmp_flipped_source >> strip_tac >>
  drule_all dfg_build_function_uses_complete >>
  qpat_assum `ao_cmp_source _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_source_def]) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_cmp_flipped_read_opcode:
  v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips /\
  MEM user (fn_insts fn) /\ MEM v (operand_vars user.inst_operands) ==>
  user.inst_opcode = ISZERO \/ user.inst_opcode = ASSERT
Proof
  strip_tac >> drule_all ao_cmp_flipped_read >>
  simp[ao_cmp_source_def] >> metis_tac[]
QED

Theorem ao_cmp_flipped_writer:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  v IN ao_cmp_flipped dfg xs flips /\
  MEM writer xs /\ MEM v writer.inst_outputs ==>
  ?op w after. ao_cmp_source dfg writer op w v after
Proof
  strip_tac >> drule ao_cmp_flipped_source >> strip_tac >>
  `MEM v inst.inst_outputs` by (gvs[ao_cmp_source_def]) >>
  `writer = inst` by
    (irule (INST_TYPE [beta |-> ``:string``] all_distinct_flat_map_unique) >>
     qexistsl_tac [`\i. i.inst_outputs`, `xs`, `v`] >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem ao_cmp_flipped_writer_opcode:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  v IN ao_cmp_flipped dfg xs flips /\
  MEM writer xs /\ MEM v writer.inst_outputs ==>
  is_comparator writer.inst_opcode
Proof
  strip_tac >> drule_all ao_cmp_flipped_writer >>
  simp[ao_cmp_source_def] >> metis_tac[]
QED

Theorem ao_cmp_flipped_nonconsumer_reads:
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> ISZERO /\
  inst.inst_opcode <> ASSERT ==>
  DISJOINT (set (operand_vars inst.inst_operands))
    (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips)
Proof
  simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[ao_cmp_flipped_read_opcode]
QED

Theorem ao_cmp_flipped_noncomparator_writes:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  MEM inst xs /\ ~is_comparator inst.inst_opcode ==>
  DISJOINT (set inst.inst_outputs) (ao_cmp_flipped dfg xs flips)
Proof
  simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[ao_cmp_flipped_writer_opcode]
QED
