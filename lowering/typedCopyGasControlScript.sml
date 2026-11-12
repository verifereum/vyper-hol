(* Entry-label independence of layout-changing memory copies. *)
Theory typedCopyGasControl
Ancestors
  exprSimAbiEncodeObliviousContext exprSimAbiEncodeObliviousLabels
  freshLabelIntervals exprSimAbiEncodeLabelProvenance emitHelperProps
  context compileEnv fragExec exprLoweringProps emitHelper list rich_list arithmetic

Theorem typed_copy_primitive_entry[local]:
  (!dst src n. entry_action (compile_copy_memory dst src n)) /\
  (!dst src n. entry_action (compile_copy_memory_dynamic dst src n)) /\
  (!base off. entry_action (compile_with_byte_offset base off)) /\
  (!src dst. entry_action (compile_store_bytestring src dst))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (Cases_on `n` >> simp[compile_copy_memory_def, entry_action_return,
                         entry_action_emit_void])
  >- simp[compile_copy_memory_dynamic_def, entry_action_emit_void]
  >- (simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
      simp[entry_action_return, entry_action_emit_op]) >>
  rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  irule entry_action_bind >> simp[entry_action_emit_void] >>
  irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac >>
  irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac >>
  simp[] >> irule entry_action_bind >> simp[entry_action_emit_op]
QED

Theorem typed_copy_entry_family:
  (!cenv dst dty src sty. entry_action (compile_store_memory_typed cenv dst dty src sty)) /\
  (!cenv dst src dtys stys doff soff.
     entry_action (compile_typed_copy_fields cenv dst src dtys stys doff soff)) /\
  (!cenv dst dty src sty n.
     entry_action (compile_copy_sarray_typed cenv dst dty src sty n)) /\
  (!cenv dst dty cap src sty.
     entry_action (compile_copy_dynarray_typed cenv dst dty cap src sty)) /\
  (!cenv dst src dfs sfs doff soff.
     entry_action (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  strip_assume_tac typed_copy_primitive_entry >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, entry_action_return]
  >- simp[Once compile_store_memory_typed_def, entry_action_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, entry_action_return]
  >> suspend "struct"
QED

Resume typed_copy_entry_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  rpt IF_CASES_TAC >> simp[entry_action_bind, entry_action_emit_op,
    entry_action_emit_void] >>
  Cases_on `dty` >> Cases_on `sty` >>
  gvs[entry_action_bind, entry_action_emit_op, entry_action_emit_void] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[]
QED

Resume typed_copy_entry_family[fields]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, entry_action_bind,
       entry_action_ignore_bind]
QED

Resume typed_copy_entry_family[sarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >> IF_CASES_TAC >>
  rewrite_tac[GSYM comp_ignore_bind_def] >>
  simp[entry_action_bind, entry_action_emit_inst,
       entry_action_emit_op, entry_action_emit_void, entry_action_return,
       entry_action_fresh_var, entry_action_fresh_label, entry_action_new_block_unit, entry_action_new_block] >>
  `!d s. entry_action (compile_store_memory_typed cenv d dty s sty)` by
    (rpt gen_tac >> first_x_assum irule >> gvs[]) >>
  rpt (FIRST [irule entry_action_new_block, irule entry_action_bind,
              irule entry_action_ignore_bind] >>
       simp[entry_action_emit_inst, entry_action_emit_op, entry_action_emit_void,
            entry_action_return, entry_action_fresh_var, entry_action_fresh_label,
            entry_action_new_block] >> rpt gen_tac) >> simp[]
QED

Resume typed_copy_entry_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_store_memory_typed_def] >>
  rewrite_tac[GSYM comp_ignore_bind_def] >>
  simp[entry_action_bind,
       entry_action_emit_inst, entry_action_emit_op,
       entry_action_emit_void, entry_action_return, entry_action_fresh_var,
       entry_action_fresh_label, entry_action_new_block_unit, entry_action_new_block] >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty` >>
  gvs[] >>
  rpt (FIRST [irule entry_action_new_block, irule entry_action_bind,
              irule entry_action_ignore_bind] >>
       simp[entry_action_emit_inst, entry_action_emit_op, entry_action_emit_void,
            entry_action_return, entry_action_fresh_var, entry_action_fresh_label,
            entry_action_new_block] >> rpt gen_tac) >>
  `!d s. entry_action (compile_store_memory_typed cenv d dty s sty)` by
    (rpt gen_tac >> first_x_assum irule >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >>
  rpt (FIRST [irule entry_action_new_block, irule entry_action_bind,
              irule entry_action_ignore_bind] >>
       simp[entry_action_emit_inst, entry_action_emit_op, entry_action_emit_void,
            entry_action_return, entry_action_fresh_var, entry_action_fresh_label,
            entry_action_new_block] >> rpt gen_tac) >> simp[]
QED

Resume typed_copy_entry_family[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, entry_action_bind,
       entry_action_ignore_bind] >>
  Cases_on `ALOOKUP sfs name` >> gvs[]
  >- simp[entry_action_bind, entry_action_ignore_bind] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[entry_action_bind, entry_action_ignore_bind]
QED

Finalise typed_copy_entry_family

Theorem compile_store_memory_typed_start_oblivious:
  frag_start_oblivious (compile_store_memory_typed cenv dst dty src sty)
Proof
  irule entry_action_oblivious >> simp[typed_copy_entry_family]
QED

Theorem typed_copy_primitive_labels[local]:
  (!dst src n. fresh_label_action (compile_copy_memory dst src n)) /\
  (!dst src n. fresh_label_action (compile_copy_memory_dynamic dst src n)) /\
  (!base off. fresh_label_action (compile_with_byte_offset base off)) /\
  (!src dst. fresh_label_action (compile_store_bytestring src dst))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (Cases_on `n` >> simp[compile_copy_memory_def, fresh_label_action_def,
       fresh_label_step_def, opened_labels_open, entry_shape_def,
       emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> metis_tac[APPEND_ASSOC])
  >- (simp[compile_copy_memory_dynamic_def, fresh_label_action_def,
       fresh_label_step_def, opened_labels_open, entry_shape_def,
       emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def] >> metis_tac[APPEND_ASSOC])
  >- (simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
      simp[fresh_label_action_return, fresh_label_action_def,
       fresh_label_step_def, opened_labels_open, entry_shape_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, fresh_var_def,
       emit_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      metis_tac[APPEND_ASSOC]) >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       fresh_label_action_def, fresh_label_step_def, opened_labels_open,
       entry_shape_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >> metis_tac[APPEND_ASSOC]
QED

Theorem typed_copy_sarray_label_step[local]:
  (!d s. fresh_label_action (compile_store_memory_typed cenv d dty s sty)) ==>
  fresh_label_action (compile_copy_sarray_typed cenv dst dty src sty n)
Proof
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  simp_tac (srw_ss()) [LET_THM] >> IF_CASES_TAC
  >- simp[typed_copy_primitive_labels] >>
  simp[fresh_label_action_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, fresh_label_def, new_block_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!d s. _` (mp_tac o SRULE[fresh_label_action_def]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `fresh_label_step sm sc` >>
  `fresh_label_step a sm` by
    (simp[Abbr `sm`, fresh_label_step_def, opened_labels_def, emitted_blocks_def,
          fresh_label_between_output, ADD1] >>
     conj_tac
     >- (qpat_x_assum `fresh_label_step _ sc` kall_tac >>
         rewrite_tac[entry_shape_def] >> disj2_tac >>
         simp_tac pure_ss [compile_state_accfupds] >>
         qmatch_goalsub_abbrev_tac `hdr :: entry :: a.cs_blocks` >>
         qexists_tac `[hdr]` >> simp[Abbr `entry`, APPEND_ASSOC]) >>
     strip_tac >> drule fresh_label_output_inj >> simp[]) >>
  irule fresh_label_step_reserved_close >>
  qexistsl_tac [`sc`, `fresh_label_output "typed_sa_exit" (a.cs_next_label + 2)`, `sm`] >>
  simp[Abbr `sm`, opened_labels_def, emitted_blocks_def, ADD1,
       fresh_label_between_output] >>
  reverse conj_tac
  >- (rewrite_tac[entry_shape_def] >> disj2_tac >> qexists_tac `[]` >>
      simp[APPEND_ASSOC]) >>
  rpt conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]
QED

Theorem typed_copy_dynarray_label_step[local]:
  (!d s. fresh_label_action (compile_store_memory_typed cenv d dty s sty)) ==>
  fresh_label_action (compile_copy_dynarray_typed cenv dst dty cap src sty)
Proof
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty`
  >- (simp[fresh_label_action_def, compile_copy_memory_dynamic_def, LET_THM,
        emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
        emit_def] >> rpt strip_tac >> gvs[] >>
      simp[fresh_label_step_def, opened_labels_open, entry_shape_def] >>
      metis_tac[APPEND_ASSOC]) >>
  simp[fresh_label_action_def, LET_THM, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, fresh_label_def, new_block_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!d s. _` (mp_tac o SRULE[fresh_label_action_def]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `fresh_label_step sm sc` >>
  `fresh_label_step a sm` by
    (simp[Abbr `sm`, fresh_label_step_def, opened_labels_def, emitted_blocks_def,
          fresh_label_between_output, ADD1] >>
     conj_tac
     >- (qpat_x_assum `fresh_label_step _ sc` kall_tac >>
         rewrite_tac[entry_shape_def] >> disj2_tac >>
         simp_tac pure_ss [compile_state_accfupds] >>
         qmatch_goalsub_abbrev_tac `hdr :: entry :: a.cs_blocks` >>
         qexists_tac `[hdr]` >> simp[Abbr `entry`, APPEND_ASSOC]) >>
     strip_tac >> drule fresh_label_output_inj >> simp[]) >>
  irule fresh_label_step_reserved_close >>
  qexistsl_tac [`sc`, `fresh_label_output "typed_dyn_exit" (a.cs_next_label + 2)`, `sm`] >>
  simp[Abbr `sm`, opened_labels_def, emitted_blocks_def, ADD1,
       fresh_label_between_output] >>
  reverse conj_tac
  >- (rewrite_tac[entry_shape_def] >> disj2_tac >> qexists_tac `[]` >>
      simp[APPEND_ASSOC]) >>
  rpt conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]
QED

Theorem typed_copy_label_family[local]:
  (!cenv dst dty src sty. fresh_label_action (compile_store_memory_typed cenv dst dty src sty)) /\
  (!cenv dst src dtys stys doff soff.
     fresh_label_action (compile_typed_copy_fields cenv dst src dtys stys doff soff)) /\
  (!cenv dst dty src sty n.
     fresh_label_action (compile_copy_sarray_typed cenv dst dty src sty n)) /\
  (!cenv dst dty cap src sty.
     fresh_label_action (compile_copy_dynarray_typed cenv dst dty cap src sty)) /\
  (!cenv dst src dfs sfs doff soff.
     fresh_label_action (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  strip_assume_tac typed_copy_primitive_labels >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, fresh_label_action_return]
  >- simp[Once compile_store_memory_typed_def, fresh_label_action_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, fresh_label_action_return]
  >> suspend "struct"
QED

Resume typed_copy_label_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  rpt IF_CASES_TAC >> simp[fresh_label_action_bind, fresh_label_action_emit] >>
  Cases_on `dty` >> Cases_on `sty` >>
  gvs[fresh_label_action_bind, fresh_label_action_emit] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[]
QED

Resume typed_copy_label_family[fields]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, fresh_label_action_bind,
       fresh_label_action_ignore_bind]
QED

Resume typed_copy_label_family[sarray]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- simp[Once compile_store_memory_typed_def, typed_copy_primitive_labels] >>
  irule typed_copy_sarray_label_step >> rpt gen_tac >>
  first_x_assum irule >> gvs[]
QED

Resume typed_copy_label_family[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, fresh_label_action_bind,
       fresh_label_action_ignore_bind] >>
  Cases_on `ALOOKUP sfs name` >> gvs[]
  >- simp[fresh_label_action_bind, fresh_label_action_ignore_bind] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[fresh_label_action_bind, fresh_label_action_ignore_bind]
QED

Resume typed_copy_label_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty`
  >- (simp[Once compile_store_memory_typed_def, fresh_label_action_def,
        compile_copy_memory_dynamic_def, LET_THM, emit_op_def, emit_void_def,
        emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
      simp[fresh_label_step_def, opened_labels_open, entry_shape_def] >>
      metis_tac[APPEND_ASSOC]) >>
  irule typed_copy_dynarray_label_step >> rpt gen_tac >>
  first_x_assum irule >> gvs[]
QED

Finalise typed_copy_label_family

Theorem compile_store_memory_typed_gas_boundary:
  compile_store_memory_typed cenv dst dty src sty sa = (u,sb) ==>
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  strip_tac >> irule fresh_label_step_current_excluded >>
  metis_tac[typed_copy_label_family, fresh_label_action_def]
QED
