Theory aggregateCodeTrace
Ancestors
  exprSimAbiGasBridge fragExec compileEnv emitHelper context list rich_list pair sum

Definition code_patch_def:
  code_patch B L insts (s:compile_state) =
    s with <|cs_blocks := B; cs_current_bb := L; cs_current_insts := insts|>
End

Definition code_event_def:
  (code_event (INL i) s = SND (emit i s)) /\
  (code_event (INR l) s = SND (new_block l s))
End

Definition code_replay_def:
  (code_replay [] s = s) /\
  (code_replay (ev::tr) s = code_replay tr (code_event ev s))
End

Definition code_trace_parametric_def:
  code_trace_parametric (m:compile_state -> 'a # compile_state) <=>
    !sa. ?x sb tr. !B L insts.
      m (code_patch B L insts sa) = (x, code_replay tr (code_patch B L insts sb))
End

Theorem code_patch_self[simp]:
  code_patch s.cs_blocks s.cs_current_bb s.cs_current_insts s = s
Proof
  simp[code_patch_def, compile_state_component_equality]
QED

Theorem code_patch_overwrite[simp]:
  code_patch B L insts (code_patch B' L' insts' s) = code_patch B L insts s
Proof
  simp[code_patch_def]
QED

Theorem code_replay_append:
  !xs ys s. code_replay (xs ++ ys) s = code_replay ys (code_replay xs s)
Proof
  Induct >> simp[code_replay_def]
QED

Theorem code_replay_patch:
  !tr s B L insts.
    code_patch B L insts (code_replay tr s) = code_patch B L insts s
Proof
  Induct >- simp[code_replay_def] >>
  Cases_on `h` >> simp[code_replay_def] >>
  simp[code_event_def, emit_def, new_block_def, code_patch_def]
QED

Theorem code_trace_return:
  code_trace_parametric (comp_return x)
Proof
  simp[code_trace_parametric_def, comp_return_def] >> gen_tac >>
  qexistsl_tac [`x`, `sa`, `[]`] >> simp[code_replay_def]
QED

Theorem code_event_context:
  !ev s t. code_event ev (code_patch t.cs_blocks t.cs_current_bb t.cs_current_insts s) =
    code_patch (code_event ev t).cs_blocks (code_event ev t).cs_current_bb
      (code_event ev t).cs_current_insts s
Proof
  Cases >> simp[code_event_def, emit_def, new_block_def, code_patch_def]
QED

Theorem code_replay_context:
  !tr s t. code_replay tr (code_patch t.cs_blocks t.cs_current_bb t.cs_current_insts s) =
    code_patch (code_replay tr t).cs_blocks (code_replay tr t).cs_current_bb
      (code_replay tr t).cs_current_insts s
Proof
  Induct >> simp[code_replay_def, code_event_context]
QED

Theorem code_replay_patch_context:
  code_replay tr (code_patch B L insts s) =
    code_patch (code_replay tr (code_patch B L insts t)).cs_blocks
      (code_replay tr (code_patch B L insts t)).cs_current_bb
      (code_replay tr (code_patch B L insts t)).cs_current_insts s
Proof
  qspec_then `tr` (qspecl_then [`s`, `code_patch B L insts t`] mp_tac)
    code_replay_context >> simp[code_patch_def]
QED

Theorem code_trace_bind:
  code_trace_parametric m /\ (!x. code_trace_parametric (k x)) ==>
  code_trace_parametric (comp_bind m k)
Proof
  simp[code_trace_parametric_def] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >>
  qpat_x_assum `!x sa. _` (qspecl_then [`x`, `sb`] strip_assume_tac) >>
  rename1 `!B L insts. k x (code_patch B L insts sb) = (y, code_replay tr' (code_patch B L insts sc))` >>
  qexistsl_tac [`y`, `sc`, `tr ++ tr'`] >>
  simp[comp_bind_def, code_replay_append] >>
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `k x middle` >>
  `middle = code_patch middle.cs_blocks middle.cs_current_bb middle.cs_current_insts sb` by
    (metis_tac[code_patch_self, code_replay_patch, code_patch_overwrite]) >>
  pop_assum SUBST1_TAC >> simp[] >>
  simp[code_replay_context, Abbr `middle`] >>
  rewrite_tac[GSYM code_replay_append] >>
  sym_tac >> irule code_replay_patch_context
QED

Theorem code_trace_ignore_bind:
  code_trace_parametric m /\ code_trace_parametric n ==>
  code_trace_parametric (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule code_trace_bind >> simp[]
QED

Theorem code_trace_fresh_var:
  code_trace_parametric fresh_var
Proof
  simp[code_trace_parametric_def] >> gen_tac >>
  qexistsl_tac [`"%" ++ toString sa.cs_next_var`,
    `sa with cs_next_var := sa.cs_next_var + 1`, `[]`] >>
  simp[code_replay_def, code_patch_def, fresh_var_def]
QED

Theorem code_trace_fresh_label:
  code_trace_parametric (fresh_label suffix)
Proof
  simp[code_trace_parametric_def] >> gen_tac >>
  qexistsl_tac [`fresh_label_output suffix sa.cs_next_label`,
    `sa with cs_next_label := sa.cs_next_label + 1`, `[]`] >>
  simp[code_replay_def, code_patch_def, fresh_label_def]
QED

Theorem code_trace_fresh_id:
  code_trace_parametric fresh_id
Proof
  simp[code_trace_parametric_def] >> gen_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa with cs_next_id := sa.cs_next_id + 1`, `[]`] >>
  simp[code_replay_def, code_patch_def, fresh_id_def]
QED

Theorem code_trace_emit:
  code_trace_parametric (emit i)
Proof
  simp[code_trace_parametric_def] >> gen_tac >>
  qexistsl_tac [`sa`, `[INL i]`] >>
  simp[code_replay_def, code_event_def, emit_def]
QED

Theorem code_trace_new_block_ignore:
  code_trace_parametric (comp_ignore_bind (new_block label) (comp_return ()))
Proof
  simp[code_trace_parametric_def] >> gen_tac >>
  qexistsl_tac [`sa`, `[INR label]`] >>
  simp[code_replay_def, code_event_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, new_block_def]
QED

Theorem code_trace_new_block_bind:
  code_trace_parametric m ==>
  code_trace_parametric (comp_ignore_bind (new_block label) m)
Proof
  strip_tac >>
  `comp_ignore_bind (new_block label) m =
     comp_ignore_bind (comp_ignore_bind (new_block label) (comp_return ())) m` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def, new_block_def] >>
  pop_assum SUBST1_TAC >>
  irule code_trace_ignore_bind >> simp[code_trace_new_block_ignore]
QED

Theorem code_trace_emit_inst:
  code_trace_parametric (emit_inst opc ops outs)
Proof
  simp[emit_inst_def] >> irule code_trace_bind >> simp[code_trace_fresh_id, code_trace_emit]
QED

Theorem code_trace_emit_void:
  code_trace_parametric (emit_void opc ops)
Proof
  simp[emit_void_def] >> irule code_trace_bind >> simp[code_trace_fresh_id, code_trace_emit]
QED

Theorem code_trace_emit_op:
  code_trace_parametric (emit_op opc ops)
Proof
  simp[emit_op_def] >> irule code_trace_bind >> simp[code_trace_fresh_id] >>
  gen_tac >> irule code_trace_bind >> simp[code_trace_fresh_var] >>
  gen_tac >> irule code_trace_ignore_bind >> simp[code_trace_emit, code_trace_return]
QED

Theorem code_trace_copy_memory:
  code_trace_parametric (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, code_trace_return, code_trace_emit_void]
QED

Theorem code_trace_with_byte_offset:
  code_trace_parametric (compile_with_byte_offset operand off)
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[code_trace_return, code_trace_emit_op]
QED

Theorem code_trace_store_bytestring:
  code_trace_parametric (compile_store_bytestring src dst)
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def, comp_bind_assoc] >>
  irule code_trace_bind >> simp[code_trace_emit_op] >> gen_tac >>
  irule code_trace_bind >> simp[code_trace_emit_op] >> gen_tac >>
  irule code_trace_bind >> simp[code_trace_emit_op] >> gen_tac >>
  irule code_trace_bind >> simp[code_trace_emit_op, code_trace_emit_void]
QED

val trace_primitives = [code_trace_emit_op, code_trace_emit_void, code_trace_emit_inst,
  code_trace_return, code_trace_fresh_var, code_trace_fresh_label, code_trace_fresh_id,
  code_trace_copy_memory, code_trace_with_byte_offset];

val trace_sequence = rpt (FIRST [irule code_trace_new_block_bind,
    irule (SRULE [comp_ignore_bind_def] code_trace_new_block_bind),
    irule code_trace_bind >> conj_tac,
    irule code_trace_ignore_bind >> conj_tac, gen_tac] >> simp trace_primitives);

Theorem code_trace_typed_copy_family:
  (!ce dst dt src st. code_trace_parametric (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dts sts doff soff.
     code_trace_parametric (compile_typed_copy_fields ce dst src dts sts doff soff)) /\
  (!ce dst dt src st n.
     code_trace_parametric (compile_copy_sarray_typed ce dst dt src st n)) /\
  (!ce dst dt cap src st.
     code_trace_parametric (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src dfs sfs doff soff.
     code_trace_parametric (compile_struct_typed_copy ce dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, code_trace_return]
  >- simp[Once compile_store_memory_typed_def, code_trace_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, code_trace_return]
  >> suspend "struct"
QED

Resume code_trace_typed_copy_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (irule code_trace_bind >> simp trace_primitives) >>
  IF_CASES_TAC >- simp[code_trace_store_bytestring] >>
  IF_CASES_TAC >- simp[code_trace_emit_void] >>
  Cases_on `dt` >> Cases_on `st` >> gvs trace_primitives >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs trace_primitives)
QED

Resume code_trace_typed_copy_family[fields]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_memory_typed_def] >>
  trace_sequence
QED

Resume code_trace_typed_copy_family[sarray]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- simp[code_trace_copy_memory] >> trace_sequence >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume code_trace_typed_copy_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >> trace_sequence >>
  IF_CASES_TAC >> simp[compile_copy_memory_dynamic_def] >> trace_sequence >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume code_trace_typed_copy_family[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name`
  >- (gvs[] >> trace_sequence) >>
  rename1 `SOME pair` >> PairCases_on `pair` >> gvs[] >> trace_sequence
QED

Finalise code_trace_typed_copy_family

Theorem code_replay_shape:
  !tr. (?suffix. !s B L insts.
      code_replay tr (code_patch B L insts s) =
        code_patch B L (insts ++ suffix) s) \/
    (?blocks lab ins suffix. !s B L insts.
      code_replay tr (code_patch B L insts s) =
        code_patch (blocks ++ [<|bb_label := L;
          bb_instructions := insts ++ suffix|>] ++ B) lab ins s)
Proof
  Induct using SNOC_INDUCT
  >- (disj1_tac >> qexists_tac `[]` >> simp[code_replay_def]) >>
  strip_tac >> Cases_on `x` >>
  gvs[SNOC_APPEND, code_replay_append, code_replay_def,
      code_event_def, emit_def, new_block_def, code_patch_def]
  >- (disj1_tac >> qexists_tac `suffix ++ [x']` >> simp[APPEND_ASSOC])
  >- (disj2_tac >> qexistsl_tac [`blocks`, `lab`, `ins ++ [x']`, `suffix`] >> simp[])
  >- (disj2_tac >> qexistsl_tac [`[]`, `y`, `[]`, `suffix`] >> simp[])
  >> disj2_tac >>
  qexistsl_tac [`<|bb_label := lab; bb_instructions := ins|> :: blocks`,
    `y`, `[]`, `suffix`] >> simp[]
QED

Theorem code_replay_start_swap:
  code_replay tr (code_patch sa.cs_blocks L
    (MAP (\id. mk_inst id NOP [] []) ids) sb) =
  start_swap sa L ids
    (code_replay tr (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb))
Proof
  qspec_then `tr` strip_assume_tac code_replay_shape >>
  simp[start_swap_def, emitted_blocks_def, code_patch_def,
    TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND, FRONT_APPEND, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[TAKE_APPEND, DROP_APPEND, FRONT_APPEND, LAST_APPEND,
    TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG]
QED

Theorem code_trace_start_oblivious:
  code_trace_parametric m ==> frag_start_oblivious m
Proof
  simp[code_trace_parametric_def, frag_start_oblivious_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >>
  `m sa = (x',code_replay tr
    (code_patch sa.cs_blocks sa.cs_current_bb sa.cs_current_insts sb'))` by
    metis_tac[code_patch_self] >>
  gvs[] >>
  `start_relabel L ids sa = code_patch sa.cs_blocks L
     (MAP (\id. mk_inst id NOP [] []) ids) sa` by
    simp[start_relabel_def, code_patch_def] >>
  simp[code_replay_start_swap]
QED

Theorem compile_typed_copy_start_oblivious_family:
  (!ce dst dt src st. frag_start_oblivious (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dts sts doff soff.
     frag_start_oblivious (compile_typed_copy_fields ce dst src dts sts doff soff)) /\
  (!ce dst dt src st n.
     frag_start_oblivious (compile_copy_sarray_typed ce dst dt src st n)) /\
  (!ce dst dt cap src st.
     frag_start_oblivious (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src dfs sfs doff soff.
     frag_start_oblivious (compile_struct_typed_copy ce dst src dfs sfs doff soff))
Proof
  rpt conj_tac >> rpt gen_tac >> irule code_trace_start_oblivious >>
  simp[code_trace_typed_copy_family]
QED
