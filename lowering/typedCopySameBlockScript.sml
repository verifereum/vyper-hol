(* Same-block operand boundary for layout-changing memory copies. *)
Theory typedCopySameBlock
Ancestors
  typedCopyGasControl typedCopyGasOps exprSimAbiEncodeObliviousOperands
  exprSimAbiEncodeObliviousLabels exprSimAbiGasBridge
  context compileEnv fragExec exprLoweringProps emitHelper list rich_list

Theorem typed_copy_operand_primitives[local]:
  (!dst src n. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_copy_memory dst src n)) /\
  (!dst src n. enc_nonlabel dst /\ enc_nonlabel src /\ enc_nonlabel n ==>
    enc_operand_action (\x. T) (compile_copy_memory_dynamic dst src n)) /\
  (!base off. enc_nonlabel base ==>
    enc_operand_action enc_nonlabel (compile_with_byte_offset base off)) /\
  (!src dst. enc_nonlabel src /\ enc_nonlabel dst ==>
    enc_operand_action (\x. T) (compile_store_bytestring src dst))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `n` >> simp[compile_copy_memory_def,
        enc_operand_action_return, enc_operand_emit_void])
  >- simp[compile_copy_memory_dynamic_def, enc_operand_emit_void]
  >- (simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
      simp[enc_operand_action_return, enc_operand_emit_op]) >>
  rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  irule enc_operand_bind_nonlabel >> conj_tac
  >- (rpt strip_tac >> simp[enc_operand_emit_void]) >>
  irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
  rpt strip_tac >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
  rpt strip_tac >> simp[] >>
  irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op]
QED

Theorem typed_copy_operand_family[local]:
  (!cenv dst dty src sty. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_store_memory_typed cenv dst dty src sty)) /\
  (!cenv dst src dtys stys doff soff. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_typed_copy_fields cenv dst src dtys stys doff soff)) /\
  (!cenv dst dty src sty n. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_copy_sarray_typed cenv dst dty src sty n)) /\
  (!cenv dst dty cap src sty. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_copy_dynarray_typed cenv dst dty cap src sty)) /\
  (!cenv dst src dfs sfs doff soff. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action (\x. T) (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  strip_assume_tac typed_copy_operand_primitives >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, enc_operand_action_return]
  >- simp[Once compile_store_memory_typed_def, enc_operand_action_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, enc_operand_action_return]
  >> suspend "struct"
QED

Resume typed_copy_operand_family[dispatch]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  rpt IF_CASES_TAC >> simp[enc_operand_emit_void]
  >- (irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> simp[enc_operand_emit_void]) >>
  Cases_on `dty` >> Cases_on `sty` >> gvs[] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[]
QED

Resume typed_copy_operand_family[fields]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
  irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
  simp[] >> irule enc_operand_action_ignore_bind >> simp[]
QED

Resume typed_copy_operand_family[struct]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name` >> gvs[]
  >- (irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
      irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
      irule enc_operand_action_ignore_bind >> simp[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >> gvs[] >>
  irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
  irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac >>
  irule enc_operand_action_ignore_bind >> simp[]
QED

Resume typed_copy_operand_family[sarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- simp[Once compile_store_memory_typed_def] >>
  rw[enc_operand_action_def] >>
  `entry_shape a b` by
    metis_tac[entry_action_run_shape, cj 3 typed_copy_entry_family] >>
  simp[enc_operand_step_def] >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_inst_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `_ _ = (_,_)`) entry_action_run_shape >>
  simp[typed_copy_entry_family] >>
  disch_then (mp_tac o MATCH_MP entry_shape_blocks_length) >>
  simp[] >> strip_tac >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >> simp[]
QED

Resume typed_copy_operand_family[dynarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty`
  >- (simp[Once compile_store_memory_typed_def] >>
      irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> irule enc_operand_action_ignore_bind >> simp[enc_operand_emit_void] >>
      irule enc_operand_action_ignore_bind >> simp[enc_operand_emit_void] >>
      irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >>
      rpt strip_tac >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op]) >>
  rw[enc_operand_action_def] >>
  `entry_shape a b` by
    metis_tac[entry_action_run_shape, cj 4 typed_copy_entry_family] >>
  simp[enc_operand_step_def] >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_inst_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `_ _ = (_,_)`) entry_action_run_shape >>
  simp[typed_copy_entry_family] >>
  disch_then (mp_tac o MATCH_MP entry_shape_blocks_length) >>
  simp[] >> strip_tac >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >> simp[]
QED

Finalise typed_copy_operand_family

Theorem compile_store_memory_typed_same_block_no_labels:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  sa.cs_blocks = sb.cs_blocks /\ (!l. dst <> Label l /\ src <> Label l) ==>
  EVERY (\i. !l. ~MEM (Label l) i.inst_operands) (frag_code sa sb)
Proof
  strip_tac >>
  `enc_operand_action (\x. T) (compile_store_memory_typed cenv dst dty src sty)` by
    (irule (cj 1 typed_copy_operand_family) >> simp[enc_nonlabel_def]) >>
  gvs[enc_operand_action_def, enc_operand_step_def, EVERY_MEM, enc_nonlabel_def] >>
  metis_tac[]
QED

Theorem compile_store_memory_typed_same_block_gas_free:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  sa.cs_blocks = sb.cs_blocks /\ (!l. dst <> Label l /\ src <> Label l) ==>
  frag_gas_free sa sb
Proof
  strip_tac >> drule compile_store_memory_typed_ops_free >>
  drule_all compile_store_memory_typed_same_block_no_labels >>
  simp[frag_gas_free_def, frag_ops_free_def, emitted_blocks_def, EVERY_MEM] >>
  metis_tac[]
QED
