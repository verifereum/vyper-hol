(* Static instruction coverage, with no allocation-size restriction. *)
Theory bodyIntCallFamCallIntEntryCodeWitness
Ancestors
  fragExec compileEnv emitHelper context venomInst exprLoweringProps rich_list
  localPtrsProps

Definition entry_code_witness_def:
  entry_code_witness a b <=>
    cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\
    a.cs_next_var <= b.cs_next_var /\
    !fn id. fn_has_code a b fn /\ a.cs_next_id <= id /\ id < b.cs_next_id ==>
      ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
        (i.inst_opcode = ALLOCA ==>
          ?n. i.inst_outputs = [STRING #"%" (toString n)] /\ a.cs_next_var <= n)
End

Theorem entry_code_witness_refl:
  entry_code_witness st st
Proof
  simp[entry_code_witness_def, cs_extends_refl]
QED

Theorem entry_code_witness_trans:
  entry_code_witness a b /\ entry_code_witness b c ==>
  entry_code_witness a c
Proof
  rw[entry_code_witness_def]
  >- metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `id < b.cs_next_id` >- simp[] >>
  `b.cs_next_id <= id` by decide_tac >>
  qpat_x_assum `!fn id. fn_has_code b c fn /\ _ ==> _` drule_all >>
  strip_tac >> qexists `i` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> qexists `n` >> simp[]
QED

Theorem entry_code_witness_return:
  entry_code_witness st (SND (comp_return v st))
Proof
  simp[comp_return_def, entry_code_witness_refl]
QED

Theorem entry_code_witness_bind:
  (!st. entry_code_witness st (SND (f st))) /\
  (!v st. entry_code_witness st (SND (g v st))) ==>
  entry_code_witness st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule entry_code_witness_trans >> metis_tac[pairTheory.SND]
QED

Theorem entry_code_witness_ignore_bind:
  (!st. entry_code_witness st (SND (f st))) /\
  (!st. entry_code_witness st (SND (g st))) ==>
  entry_code_witness st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule entry_code_witness_bind >> simp[]
QED

Theorem entry_code_witness_emit_inst:
  (opc = ALLOCA ==>
    ?n. outs = [STRING #"%" (toString n)] /\ st.cs_next_var <= n) ==>
  entry_code_witness st (SND (emit_inst opc ops outs st))
Proof
  disch_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, entry_code_witness_def,
    cs_extends_def] >> rpt strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `id = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  conj_tac
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def]
QED

Theorem entry_code_witness_emit_void:
  opc <> ALLOCA ==>
  entry_code_witness st (SND (emit_void opc ops st))
Proof
  simp[emit_void_def, GSYM emit_inst_def, entry_code_witness_emit_inst]
QED

Theorem entry_code_witness_emit_op:
  entry_code_witness st (SND (emit_op opc ops st))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, entry_code_witness_def,
    cs_extends_def] >> rpt strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `id = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)]` >>
  conj_tac
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def]
QED

Theorem entry_code_witness_fresh_var:
  entry_code_witness st (SND (fresh_var st))
Proof
  simp[fresh_var_def, entry_code_witness_def, cs_extends_def]
QED

Theorem entry_code_witness_fresh_label:
  entry_code_witness st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, entry_code_witness_def, cs_extends_def]
QED

Theorem entry_code_witness_new_block:
  entry_code_witness st (SND (new_block name st))
Proof
  simp[entry_code_witness_def, new_block_def, cs_extends_def]
QED

Theorem entry_code_witness_alloc_buffer:
  entry_code_witness st (SND (compile_alloc_buffer sz st))
Proof
  simp[compile_alloc_buffer_def] >>
  irule entry_code_witness_bind >>
  simp[entry_code_witness_emit_op, entry_code_witness_return]
QED

Theorem entry_code_witness_alloca_fresh:
  entry_code_witness a b /\ fn_has_code a b func /\
  fn_inst_ids_distinct func ==>
  !i p. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_outputs = [p] /\ a.cs_next_id <= i.inst_id /\
    i.inst_id < b.cs_next_id ==> ~not_fresh_at a p
Proof
  rw[entry_code_witness_def] >>
  qpat_x_assum `!fn id. _` drule_all >> strip_tac >>
  `i = i'` by metis_tac[fn_inst_ids_distinct_inj] >>
  qpat_x_assum `i = i'` SUBST_ALL_TAC >>
  qpat_x_assum `_ ==> ?n. _` drule >> strip_tac >>
  fs[not_fresh_at_def] >> metis_tac[]
QED

(* A block change does not lose coverage of either emitted instruction. *)
Theorem entry_code_witness_block_probe:
  entry_code_witness st
    (SND (comp_ignore_bind (emit_op ALLOCA [Lit (n2w sz)])
      (comp_ignore_bind (new_block label) (emit_op ALLOCA [Lit (n2w sz')])) st))
Proof
  irule entry_code_witness_ignore_bind >>
  simp[entry_code_witness_emit_op] >> gen_tac >>
  irule entry_code_witness_ignore_bind >>
  simp[entry_code_witness_new_block, entry_code_witness_emit_op]
QED
