Theory o1SymStaticMakeSSA
Ancestors
  o1MakeSsaFormats o1PassContract makeSsaCurrentInduct
  dfAnalyzeProofs makeSsaCurrentCfg makeSsaDefs list
  simplifyCfgDefs simplifyCfgStruct o1MakeSsaFrontier o1MakeSsaCfg
  venomInst venomWf unitShapeDefs vyperCompiler o1LabelReadinessSsa

Theorem make_ssa_current_fn_runtime_reflect:
  o1_fn_shape C f /\ make_ssa_current_fn s f = (f',s') ==>
  ((?i. MEM i (fn_insts f') /\ MEM (Label "runtime_begin") i.inst_operands) ==>
   (?i. MEM i (fn_insts f) /\ MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >> spose_not_then strip_assume_tac >>
  `~MEM "runtime_begin" (fn_labels f)` by
    (gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
         fn_labels_def, MEM_MAP, EVERY_MEM, unitShapeDefsTheory.reserved_label_def] >>
     metis_tac[]) >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) (fn_insts f)` by
    simp[EVERY_MEM] >>
  `wf_function f` by fs[o1_fn_shape_def] >>
  `EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) (fn_insts f')` by
    (fs[EVERY_MEM] >>
     metis_tac[o1LabelReadinessSsaTheory.make_ssa_current_fn_label_absent]) >>
  gvs[EVERY_MEM]
QED
