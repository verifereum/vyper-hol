Theory internalReturnCopyFwdHaltStatic
Ancestors
  internalReturnCopyFwdHaltProbe o1PassContract venomWf
  invokeCopyFwdCommonDefs ptrDiscipline venomInst list

Theorem ircf_halt_static_reachable_opcodes:
  MEM i (fn_insts (unitShapeDefs$reachable_fn ircf_halt_probe_fn)) ==>
  MEM i.inst_opcode [ALLOCA; MLOAD; SSTORE; JMP]
Proof
  strip_tac >> dxrule unitShapeDefsTheory.reachable_fn_insts_mem >>
  strip_tac >> gvs[unitShapeDefsTheory.reachable_inst_fields] >>
  mp_tac ircf_halt_probe_instruction_opcodes >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem ircf_halt_static_no_retpc:
  ~unitShapeDefs$copy_phi_var RETPC_PARAM ircf_halt_probe_fn x
Proof
  strip_tac >> drule unitShapeDefsTheory.copy_phi_var_has_seed >>
  strip_tac >> assume_tac ircf_halt_probe_instruction_opcodes >>
  fs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem ircf_halt_static_retpc:
  unitShapeDefs$retpc_shape_ok ircf_halt_probe_fn
Proof
  rw[unitShapeDefsTheory.retpc_shape_ok_def,
     unitShapeDefsTheory.retpc_var_def, ircf_halt_static_no_retpc] >>
  drule ircf_halt_static_reachable_opcodes >> simp[] >> gvs[]
QED

Theorem ircf_halt_static_shape:
  o1_ctx_shape ircf_halt_probe_ctx
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, ircf_halt_probe_ctx_def,
       unitShapeDefsTheory.fn_shape_ok_def, ircf_halt_static_retpc,
       unitShapeDefsTheory.opaque_use_ok_def,
       unitShapeDefsTheory.retpc_var_def, ircf_halt_static_no_retpc] >>
  rpt conj_tac >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem ircf_halt_static_ssa:
  EVERY wf_ssa ircf_halt_probe_ctx.ctx_functions
Proof
  EVAL_TAC
QED

Theorem ircf_halt_static_noalias:
  EVERY ircf_no_dst_write_alias ircf_halt_probe_ctx.ctx_functions
Proof
  simp[ircf_halt_probe_ctx_def, ircf_no_dst_write_alias_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[ircf_halt_probe_fn_def, ircf_halt_probe_bb_def, mk_raw_function_def,
      mk_inst_def]
QED

Theorem ircf_halt_static_no_dalloca:
  ~ctx_has_dalloca ircf_halt_probe_ctx
Proof
  EVAL_TAC
QED

Theorem ircf_halt_static_dead_wf:
  dead_wf <| d_stor := (\a st. {}); d_trans := (\a st. {});
             d_imm := (\im. {}); d_ret := (\r. {}) |>
Proof
  simp[dead_wf_def]
QED
