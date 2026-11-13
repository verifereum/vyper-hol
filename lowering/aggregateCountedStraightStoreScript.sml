Theory aggregateCountedStraightStore
Ancestors
  aggregateTypedCopyRawShape aggregateCodeTrace exprSimAbiGasBridge
  context compileEnv emitHelper emitHelperProps fragExec list rich_list
  venomInst exprLoweringProps

(* A compositional compiler certificate, restricted to the no-new-block case. *)
Definition straight_copy_def:
  straight_copy (m:compile_state -> 'a # compile_state) <=>
    !sa x sb. m sa = (x,sb) ==>
      cs_extends sa sb /\
      (sa.cs_blocks = sb.cs_blocks ==>
       ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
              EVERY (\i. ~is_terminator i.inst_opcode) code)
End

Theorem extends_middle_blocks:
  cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_blocks = sb.cs_blocks ==>
  sa.cs_blocks = sm.cs_blocks /\ sm.cs_blocks = sb.cs_blocks
Proof
  simp[cs_extends_def] >> strip_tac >>
  `LENGTH new = 0 /\ LENGTH new' = 0` by
    (qpat_x_assum `sa.cs_blocks = _` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
     qpat_assum `sb.cs_blocks = _` (fn th => once_rewrite_tac [th]) >>
     qpat_assum `sm.cs_blocks = _` (fn th => once_rewrite_tac [th]) >>
     pure_rewrite_tac [LENGTH_APPEND] >> decide_tac) >> gvs[]
QED

Theorem straight_copy_bind:
  straight_copy m /\ (!x. straight_copy (k x)) ==>
  straight_copy (comp_bind m k)
Proof
  simp[straight_copy_def, comp_bind_def] >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  strip_tac >> drule_all extends_middle_blocks >> strip_tac >>
  gvs[] >> qexists_tac `code ++ code'` >> simp[APPEND_ASSOC]
QED

Theorem straight_copy_ignore_bind:
  straight_copy m /\ straight_copy n ==>
  straight_copy (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule straight_copy_bind >> simp[]
QED

Theorem straight_copy_return[simp]:
  straight_copy (comp_return x)
Proof
  simp[straight_copy_def, comp_return_def, cs_extends_refl]
QED

Theorem straight_copy_fresh_var[simp]:
  straight_copy fresh_var
Proof
  simp[straight_copy_def, fresh_var_def, cs_extends_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Theorem straight_copy_fresh_id[simp]:
  straight_copy fresh_id
Proof
  simp[straight_copy_def, fresh_id_def, cs_extends_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Theorem straight_copy_fresh_label[simp]:
  straight_copy (fresh_label pfx)
Proof
  simp[straight_copy_def, fresh_label_def, cs_extends_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]
QED

Theorem straight_copy_emit:
  ~is_terminator i.inst_opcode ==> straight_copy (emit i)
Proof
  simp[straight_copy_def, emit_def, cs_extends_def]
QED

Theorem straight_copy_emit_inst:
  ~is_terminator opc ==> straight_copy (emit_inst opc ops outs)
Proof
  strip_tac >> simp[emit_inst_def] >> irule straight_copy_bind >> simp[] >>
  gen_tac >> irule straight_copy_emit >> simp[mk_inst_def]
QED

Theorem straight_copy_emit_void:
  ~is_terminator opc ==> straight_copy (emit_void opc ops)
Proof
  strip_tac >> simp[emit_void_def] >> irule straight_copy_bind >> simp[] >>
  gen_tac >> irule straight_copy_emit >> simp[mk_inst_def]
QED

Theorem straight_copy_emit_op:
  ~is_terminator opc ==> straight_copy (emit_op opc ops)
Proof
  strip_tac >> simp[emit_op_def] >> irule straight_copy_bind >> simp[] >>
  gen_tac >> irule straight_copy_bind >> simp[] >> gen_tac >>
  irule straight_copy_ignore_bind >> simp[] >>
  irule straight_copy_emit >> simp[mk_inst_def]
QED

Theorem straight_copy_copy_memory:
  straight_copy (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, straight_copy_emit_void, is_terminator_def]
QED

Theorem straight_copy_copy_memory_dynamic:
  straight_copy (compile_copy_memory_dynamic dst src n)
Proof
  simp[compile_copy_memory_dynamic_def, straight_copy_emit_void, is_terminator_def]
QED

Theorem straight_copy_with_byte_offset:
  straight_copy (compile_with_byte_offset operand off)
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[straight_copy_emit_op, is_terminator_def]
QED

val straight_primitives = [straight_copy_emit_op, straight_copy_emit_void,
  straight_copy_emit_inst, straight_copy_copy_memory,
  straight_copy_copy_memory_dynamic, straight_copy_with_byte_offset, is_terminator_def];

val straight_sequence = rpt (FIRST [irule straight_copy_bind >> conj_tac,
    irule straight_copy_ignore_bind >> conj_tac, gen_tac] >> simp straight_primitives);

Theorem straight_copy_store_bytestring:
  straight_copy (compile_store_bytestring src dst)
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def, comp_bind_assoc] >>
  straight_sequence
QED

Theorem straight_copy_typed_family:
  (!ce dst dt src st. acyclic_struct_metadata ce.ce_struct_fields ==>
     straight_copy (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dts sts doff soff. acyclic_struct_metadata ce.ce_struct_fields ==>
     straight_copy (compile_typed_copy_fields ce dst src dts sts doff soff)) /\
  (!ce dst dt src st n. acyclic_struct_metadata ce.ce_struct_fields ==>
     straight_copy (compile_copy_sarray_typed ce dst dt src st n)) /\
  (!ce dst dt cap src st. acyclic_struct_metadata ce.ce_struct_fields ==>
     straight_copy (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src dfs sfs doff soff. acyclic_struct_metadata ce.ce_struct_fields ==>
     straight_copy (compile_struct_typed_copy ce dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def]
  >- simp[Once compile_store_memory_typed_def]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def] >> suspend "struct"
QED

Resume straight_copy_typed_family[dispatch]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (irule straight_copy_bind >> simp straight_primitives) >>
  IF_CASES_TAC >- simp[straight_copy_store_bytestring] >>
  Cases_on `dt` >> Cases_on `st` >> gvs straight_primitives >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs straight_primitives)
QED

Resume straight_copy_typed_family[fields]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >> straight_sequence
QED

Resume straight_copy_typed_family[struct]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name` >> gvs[]
  >- straight_sequence >>
  PairCases_on `x` >> gvs[] >> straight_sequence
QED

Resume straight_copy_typed_family[sarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[straight_copy_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (mp_tac (cj 3 ci_mono_typed_memory_family) >>
      disch_then (qspecl_then [`ce`, `dst`, `dt`, `src`, `st`, `n`, `sa`] mp_tac) >>
      simp[ci_mono_def]) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> IF_CASES_TAC
  >- (strip_tac >>
      mp_tac (GEN_ALL straight_copy_copy_memory) >> simp[straight_copy_def] >> metis_tac[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def, emit_inst_def,
       emit_op_def, emit_void_def, emit_def, new_block_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule aggregate_typed_store_extends >> simp[cs_extends_def] >>
  strip_tac >> strip_tac >>
  qpat_x_assum `sa.cs_blocks = _` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
  qpat_assum `cs'.cs_blocks = _` (fn th => once_rewrite_tac [th]) >>
  simp[LENGTH_APPEND]
QED

Resume straight_copy_typed_family[dynarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st`
  >- (simp[Once compile_store_memory_typed_def] >> straight_sequence) >>
  simp[straight_copy_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (mp_tac (cj 4 ci_mono_typed_memory_family) >>
      disch_then (qspecl_then [`ce`, `dst`, `dt`, `cap`, `src`, `st`, `sa`] mp_tac) >>
      simp[ci_mono_def]) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def, emit_inst_def,
       emit_op_def, emit_void_def, emit_def, new_block_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule aggregate_typed_store_extends >> simp[cs_extends_def] >>
  strip_tac >> strip_tac >>
  qpat_x_assum `sa.cs_blocks = _` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
  qpat_assum `cs'.cs_blocks = _` (fn th => once_rewrite_tac [th]) >>
  simp[LENGTH_APPEND]
QED

Finalise straight_copy_typed_family

Theorem compile_store_memory_typed_same_block_nonterminators:
  acyclic_struct_metadata ce.ce_struct_fields /\
  compile_store_memory_typed ce dst dt src st sa = ((),sb) /\
  sa.cs_blocks = sb.cs_blocks ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb)
Proof
  strip_tac >>
  mp_tac (cj 1 straight_copy_typed_family) >>
  simp[straight_copy_def] >>
  disch_then drule >> disch_then drule >> strip_tac >>
  gvs[frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]
QED
