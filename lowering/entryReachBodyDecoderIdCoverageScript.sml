Theory entryReachBodyDecoderIdCoverage
Ancestors
  entryReachBodyCodeHistory abiDecoderCode compileEnv emitHelper abiEncoder
  loweringShapeDefs venomInst context list arithmetic

Definition entry_decoder_id_coverage_def:
  entry_decoder_id_coverage a b <=>
    a.cs_next_id <= b.cs_next_id /\
    (!i. MEM i (state_insts a) ==> MEM i (state_insts b)) /\
    (!k. a.cs_next_id <= k /\ k < b.cs_next_id ==>
      ?i. MEM i (state_insts b) /\ i.inst_id = k /\
          abi_decoder_alloc_shape i)
End

Theorem entry_decoder_id_coverage_refl[simp]:
  entry_decoder_id_coverage a a
Proof
  simp[entry_decoder_id_coverage_def]
QED

Theorem entry_decoder_id_coverage_trans:
  entry_decoder_id_coverage a b /\ entry_decoder_id_coverage b c ==>
  entry_decoder_id_coverage a c
Proof
  rw[entry_decoder_id_coverage_def] >>
  Cases_on `k < b.cs_next_id`
  >- metis_tac[] >>
  `b.cs_next_id <= k` by decide_tac >> metis_tac[]
QED

Theorem entry_decoder_id_coverage_return:
  entry_decoder_id_coverage st (SND (comp_return v st))
Proof
  simp[comp_return_def]
QED

Theorem entry_decoder_id_coverage_bind:
  (!st. entry_decoder_id_coverage st (SND (f st))) /\
  (!v st. entry_decoder_id_coverage st (SND (g v st))) ==>
  entry_decoder_id_coverage st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule entry_decoder_id_coverage_trans >> metis_tac[pairTheory.SND]
QED

Theorem entry_decoder_id_coverage_ignore_bind:
  (!st. entry_decoder_id_coverage st (SND (f st))) /\
  (!st. entry_decoder_id_coverage st (SND (g st))) ==>
  entry_decoder_id_coverage st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule entry_decoder_id_coverage_bind >> simp[]
QED

Theorem entry_decoder_id_coverage_emit_op:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  entry_decoder_id_coverage st (SND (emit_op opc ops st))
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_var_def, fresh_id_def, emit_def, entry_decoder_id_coverage_def,
     state_insts_def, all_blocks_def, MEM_MAP, MEM_FLAT,
     abi_decoder_alloc_shape_def, mk_inst_def] >>
  gvs[] >> `k = st.cs_next_id` by decide_tac >> gvs[] >>
  qexists_tac `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >> simp[mk_inst_def]
QED

Theorem entry_decoder_id_coverage_emit_void:
  opc <> ALLOCA ==>
  entry_decoder_id_coverage st (SND (emit_void opc ops st))
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_id_def, emit_def, entry_decoder_id_coverage_def,
     state_insts_def, all_blocks_def, MEM_MAP, MEM_FLAT,
     abi_decoder_alloc_shape_def, mk_inst_def] >>
  gvs[] >> `k = st.cs_next_id` by decide_tac >> gvs[] >>
  qexists_tac `mk_inst st.cs_next_id opc ops []` >> simp[mk_inst_def]
QED

Theorem entry_decoder_id_coverage_emit_inst:
  opc <> ALLOCA ==>
  entry_decoder_id_coverage st (SND (emit_inst opc ops outs st))
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_id_def, emit_def, entry_decoder_id_coverage_def,
     state_insts_def, all_blocks_def, MEM_MAP, MEM_FLAT,
     abi_decoder_alloc_shape_def, mk_inst_def] >>
  gvs[] >> `k = st.cs_next_id` by decide_tac >> gvs[] >>
  qexists_tac `mk_inst st.cs_next_id opc ops outs` >> simp[mk_inst_def]
QED

Theorem entry_decoder_id_coverage_fresh_label:
  entry_decoder_id_coverage st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, entry_decoder_id_coverage_def, state_insts_def,
       all_blocks_def]
QED

Theorem entry_decoder_id_coverage_new_block:
  entry_decoder_id_coverage st (SND (new_block name st))
Proof
  simp[new_block_def, entry_decoder_id_coverage_def, state_insts_def,
       all_blocks_def, FLAT_APPEND] >> metis_tac[]
QED

Theorem entry_decoder_id_coverage_alloc_buffer:
  entry_decoder_id_coverage st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >>
  irule entry_decoder_id_coverage_bind >>
  simp[entry_decoder_id_coverage_emit_op, entry_decoder_id_coverage_return]
QED
