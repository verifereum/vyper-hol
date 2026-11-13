Theory o1LabelFlowSourceCfgData
Ancestors
  o1ContractSimplifyCfgSrcStatic unitShapeDefs venomInst list pred_set

Theorem simplify_cfg_fn_nonphi_data_origin:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  MEM i (fn_insts (simplify_cfg_fn f)) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  MEM i (fn_insts f)
Proof
  strip_tac >>
  drule_all simplify_cfg_fn_data_insts >>
  simp[EXTENSION, MEM_FILTER] >> strip_tac >>
  irule reachable_fn_insts_nonphi >> simp[] >>
  metis_tac[]
QED

Theorem simplify_cfg_fn_no_codesize:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  (!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE) ==>
  !i. MEM i (fn_insts (simplify_cfg_fn f)) ==>
      i.inst_opcode <> CODESIZE
Proof
  rpt strip_tac >>
  `MEM i (fn_insts f)` by
    (irule simplify_cfg_fn_nonphi_data_origin >>
     simp[is_terminator_def]) >>
  metis_tac[]
QED

Theorem simplify_cfg_fn_codecopy_runtime_begin:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  (!i. MEM i (fn_insts f) /\ i.inst_opcode = CODECOPY ==>
       ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]) ==>
  !i. MEM i (fn_insts (simplify_cfg_fn f)) /\
      i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]
Proof
  rpt strip_tac >>
  `MEM i (fn_insts f)` by
    (irule simplify_cfg_fn_nonphi_data_origin >>
     simp[is_terminator_def]) >>
  metis_tac[]
QED
