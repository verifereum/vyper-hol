Theory bodyMemTbExtract32RecursiveOrigin
Ancestors
  bodyMemTbExtract32Emission exprLowering emitHelper freshWrites compileEnv venomInst

Theorem extract32_emit_op_excluded_register:
  not_fresh_at sa v /\ EVERY (\a. a <> Var v) args /\
  emit_op opc args sa = (r,sb) ==>
  r <> Var v /\
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM,
      not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem extract32_emit_void_excluded_register:
  EVERY (\a. a <> Var v) args /\ emit_void opc args sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM]
QED


Theorem extract32_emit_inst_excluded_register:
  EVERY (\a. a <> Var v) args /\ ~MEM v outs /\
  emit_inst opc args outs sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM]
QED

Theorem extract32_fresh_var_chronological:
  fresh_var sa = (r,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_fresh_var_excluded_register:
  fresh_var sa = (r,sb) /\ not_fresh_at sa v ==> r <> v
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem extract32_fresh_label_chronological:
  fresh_label prefix sa = (r,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts
Proof
  simp[fresh_label_def] >> rpt strip_tac >> gvs[]
QED
