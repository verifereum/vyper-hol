(* TOP-LEVEL: compiler instruction counters grow monotonically and emitted
   instructions stay below the next fresh ID. This concerns compiler code
   history, independently of which runtime allocation IDs are cached. *)
Theory compileIdFlow
Ancestors
  compileCodePreservation compileAllocaProvenance compileEnv emitHelper
  venomInst list pair arithmetic

Definition compiler_ids_mono_def:
  compiler_ids_mono action <=> !cs. cs.cs_next_id <= (SND (action cs)).cs_next_id
End

Definition compiler_id_history_def:
  compiler_id_history cs <=>
    EVERY (\inst. inst.inst_id < cs.cs_next_id) cs.cs_current_insts /\
    EVERY (\bb. EVERY (\inst. inst.inst_id < cs.cs_next_id) bb.bb_instructions) cs.cs_blocks
End

Definition compiler_id_flow_def:
  compiler_id_flow action <=>
    compiler_ids_mono action /\ compiler_preserves compiler_id_history action
End

Theorem compiler_ids_mono_return:
  !value. compiler_ids_mono (comp_return value)
Proof
  simp[compiler_ids_mono_def, comp_return_def]
QED

Theorem compiler_ids_mono_bind:
  !action cont. compiler_ids_mono action /\ (!value. compiler_ids_mono (cont value)) ==>
    compiler_ids_mono (comp_bind action cont)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_ids_mono_def] >> strip_tac >> qx_gen_tac `cs` >>
  Cases_on `action cs` >> rename1 `action cs = (value,mid)` >> simp[comp_bind_def] >>
  irule LESS_EQ_TRANS >> qexists_tac `mid.cs_next_id` >> conj_tac
  >- (qpat_x_assum `!cs. cs.cs_next_id <= (SND (action cs)).cs_next_id`
        (qspec_then `cs` mp_tac) >> simp[]) >>
  qpat_x_assum `!value cs. _` (qspecl_then [`value`, `mid`] mp_tac) >> simp[]
QED

Theorem compiler_ids_mono_ignore_bind:
  !action next. compiler_ids_mono action /\ compiler_ids_mono next ==>
    compiler_ids_mono (comp_ignore_bind action next)
Proof
  rpt gen_tac >> rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_ids_mono_bind >> simp[]
QED

Theorem compiler_ids_mono_prims:
  (!inst. compiler_ids_mono (emit inst)) /\
  (!label. compiler_ids_mono (new_block label)) /\
  compiler_ids_mono fresh_var /\ (!suffix. compiler_ids_mono (fresh_label suffix)) /\
  compiler_ids_mono fresh_id /\ compiler_ids_mono comp_get
Proof
  simp[compiler_ids_mono_def, emit_def, new_block_def, fresh_var_def,
    fresh_label_def, fresh_id_def, comp_get_def, LET_THM]
QED

Theorem compiler_ids_mono_emit_helpers:
  (!opc ops outs. compiler_ids_mono (emit_inst opc ops outs)) /\
  (!opc ops. compiler_ids_mono (emit_op opc ops)) /\
  (!opc ops. compiler_ids_mono (emit_void opc ops))
Proof
  rw[emit_inst_def, emit_op_def, emit_void_def] >>
  rpt (FIRST [irule compiler_ids_mono_bind, irule compiler_ids_mono_ignore_bind] >>
    rw[compiler_ids_mono_prims, compiler_ids_mono_return]) >>
  rw[compiler_ids_mono_prims, compiler_ids_mono_return]
QED

Theorem compiler_ids_mono_result:
  !action cs ret cs'. compiler_ids_mono action /\ action cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id
Proof
  simp_tac bool_ss [compiler_ids_mono_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `cs` mp_tac) >> simp[]
QED

Theorem compiler_id_history_member:
  !cs. compiler_id_history cs <=>
    !inst. compiler_instruction_member cs inst ==> inst.inst_id < cs.cs_next_id
Proof
  simp[compiler_id_history_def, compiler_instruction_member_def, EVERY_MEM] >> metis_tac[]
QED

Theorem compiler_id_history_empty:
  !cs. cs.cs_current_insts = [] /\ cs.cs_blocks = [] ==> compiler_id_history cs
Proof
  simp[compiler_id_history_def]
QED

Theorem compiler_id_history_fresh:
  !cs inst. compiler_id_history cs /\ cs.cs_next_id <= inst.inst_id ==>
    ~compiler_instruction_member cs inst
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_id_history_member] >> strip_tac >>
  DISCH_TAC >> first_x_assum drule >> decide_tac
QED

Theorem compiler_preserves_id_history_prims:
  (!label. compiler_preserves compiler_id_history (new_block label)) /\
  compiler_preserves compiler_id_history fresh_var /\
  (!suffix. compiler_preserves compiler_id_history (fresh_label suffix)) /\
  compiler_preserves compiler_id_history fresh_id /\
  compiler_preserves compiler_id_history comp_get
Proof
  rw[compiler_preserves_def, compiler_id_history_def, new_block_def,
    fresh_var_def, fresh_label_def, fresh_id_def, comp_get_def, LET_THM, EVERY_MEM] >>
  fs[] >> res_tac >> decide_tac
QED

Theorem compiler_preserves_id_history_emit_helpers:
  (!opc ops outs. compiler_preserves compiler_id_history (emit_inst opc ops outs)) /\
  (!opc ops. compiler_preserves compiler_id_history (emit_op opc ops)) /\
  (!opc ops. compiler_preserves compiler_id_history (emit_void opc ops))
Proof
  rw[compiler_preserves_def, compiler_id_history_def, emit_inst_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
    emit_def, mk_inst_def, LET_THM, EVERY_MEM] >> fs[] >> res_tac >> decide_tac
QED

Theorem compiler_id_flow_return:
  !value. compiler_id_flow (comp_return value)
Proof
  simp[compiler_id_flow_def, compiler_ids_mono_return, compiler_preserves_return]
QED

Theorem compiler_id_flow_bind:
  !action cont. compiler_id_flow action /\ (!value. compiler_id_flow (cont value)) ==>
    compiler_id_flow (comp_bind action cont)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_id_flow_def] >> strip_tac >> conj_tac
  >- (irule compiler_ids_mono_bind >> simp[]) >>
  irule compiler_preserves_bind >> simp[]
QED

Theorem compiler_id_flow_ignore_bind:
  !action next. compiler_id_flow action /\ compiler_id_flow next ==>
    compiler_id_flow (comp_ignore_bind action next)
Proof
  rpt gen_tac >> rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_id_flow_bind >> simp[]
QED

Theorem compiler_id_flow_prims:
  (!label. compiler_id_flow (new_block label)) /\ compiler_id_flow fresh_var /\
  (!suffix. compiler_id_flow (fresh_label suffix)) /\
  compiler_id_flow fresh_id /\ compiler_id_flow comp_get
Proof
  simp[compiler_id_flow_def, compiler_ids_mono_prims, compiler_preserves_id_history_prims]
QED

Theorem compiler_id_flow_emit_helpers:
  (!opc ops outs. compiler_id_flow (emit_inst opc ops outs)) /\
  (!opc ops. compiler_id_flow (emit_op opc ops)) /\
  (!opc ops. compiler_id_flow (emit_void opc ops))
Proof
  simp[compiler_id_flow_def, compiler_ids_mono_emit_helpers, compiler_preserves_id_history_emit_helpers]
QED

Theorem compiler_id_flow_result:
  !action cs ret cs'. compiler_id_flow action /\ action cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id /\ (compiler_id_history cs ==> compiler_id_history cs')
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_id_flow_def] >> strip_tac >> conj_tac
  >- (drule_all compiler_ids_mono_result >> simp[]) >>
  DISCH_TAC >> drule_all compiler_preserves_result >> simp[]
QED
