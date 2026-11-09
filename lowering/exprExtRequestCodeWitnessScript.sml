(* Forward instruction witnesses in any containing function. *)
Theory exprExtRequestCodeWitness
Ancestors
  abiDecoderCode fragExec compileEnv emitHelper context venomInst
  exprLoweringProps rich_list

Definition extrequest_code_witness_def:
  extrequest_code_witness a b <=>
    cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\
    a.cs_next_var <= b.cs_next_var /\
    !fn id. fn_has_code a b fn /\ a.cs_next_id <= id /\ id < b.cs_next_id ==>
      ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\ abi_decoder_alloc_shape i /\
        (i.inst_opcode = ALLOCA ==>
          ?n. i.inst_outputs = [STRING #"%" (toString n)] /\ a.cs_next_var <= n)
End

Theorem extrequest_code_witness_refl:
  extrequest_code_witness st st
Proof
  simp[extrequest_code_witness_def, cs_extends_refl]
QED

Theorem extrequest_code_witness_trans:
  extrequest_code_witness a b /\ extrequest_code_witness b c ==>
  extrequest_code_witness a c
Proof
  rw[extrequest_code_witness_def]
  >- metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `id < b.cs_next_id` >- simp[] >>
  `b.cs_next_id <= id` by decide_tac >>
  qpat_x_assum `!fn id. fn_has_code b c fn /\ _ ==> _` drule_all >>
  strip_tac >> qexists `i` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> qexists `n` >> simp[]
QED

Theorem extrequest_code_witness_return:
  extrequest_code_witness st (SND (comp_return v st))
Proof
  simp[comp_return_def, extrequest_code_witness_refl]
QED

Theorem extrequest_code_witness_bind:
  (!st. extrequest_code_witness st (SND (f st))) /\
  (!v st. extrequest_code_witness st (SND (g v st))) ==>
  extrequest_code_witness st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule extrequest_code_witness_trans >> metis_tac[pairTheory.SND]
QED

Theorem extrequest_code_witness_ignore_bind:
  (!st. extrequest_code_witness st (SND (f st))) /\
  (!st. extrequest_code_witness st (SND (g st))) ==>
  extrequest_code_witness st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule extrequest_code_witness_bind >> simp[]
QED

Theorem extrequest_code_witness_emit_inst:
  opc <> ALLOCA \/ (ops = [Lit 32w] /\
    ?n. outs = [STRING #"%" (toString n)] /\ st.cs_next_var <= n) ==>
  extrequest_code_witness st (SND (emit_inst opc ops outs st))
Proof
  disch_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, extrequest_code_witness_def,
    cs_extends_def] >> rpt strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `id = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  conj_tac
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def, abi_decoder_alloc_shape_def] >> metis_tac[]
QED

Theorem extrequest_code_witness_emit_void:
  opc <> ALLOCA ==>
  extrequest_code_witness st (SND (emit_void opc ops st))
Proof
  simp[emit_void_def, GSYM emit_inst_def, extrequest_code_witness_emit_inst]
QED

Theorem extrequest_code_witness_emit_op:
  opc <> ALLOCA \/ ops = [Lit 32w] ==>
  extrequest_code_witness st (SND (emit_op opc ops st))
Proof
  disch_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, extrequest_code_witness_def,
    cs_extends_def] >> rpt strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `id = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)]` >>
  conj_tac
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def, abi_decoder_alloc_shape_def] >> metis_tac[]
QED

Theorem extrequest_code_witness_fresh_label:
  extrequest_code_witness st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, extrequest_code_witness_def, cs_extends_def]
QED

Theorem extrequest_code_witness_new_block:
  extrequest_code_witness st (SND (new_block name st))
Proof
  simp[extrequest_code_witness_def, new_block_def, cs_extends_def]
QED

Theorem extrequest_code_witness_alloc_buffer:
  extrequest_code_witness st (SND (compile_alloc_buffer 32 st))
Proof
  simp[compile_alloc_buffer_def] >>
  irule extrequest_code_witness_bind >>
  simp[extrequest_code_witness_emit_op, extrequest_code_witness_return]
QED
