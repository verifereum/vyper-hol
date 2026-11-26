(* Endpoint of the read-only BLOBHASH suffix, before restoring linked frames. *)
Theory bodyBlobHashReadSuffixMods
Ancestors
  bodyFullHashKeccakFixed stateRelProj fragGasSeqPtr ptrSafeRun ptrDiscipline
  venomInst venomState vyperStorageTrace venomExecSemantics fragGasOriginPtr
  exprLoweringProps decoderGhostFramePtr codegenRel fragExec emitHelperProps
  allocaHistory finite_map compileEnv exprUnopSimDefs exprSimProps loweringPosts
  vyperContext valueEncoding valueEncodingProofs words rich_list list
  loweringStateRelDefs vyperStorageFootprint exprSimUnopProps

Theorem blobhash_read_physical_suffix:
  !arg sa op sb func st0 cenv cx mid s ctx DF lo G tn explicit PG i.
    emit_op BLOBHASH [arg] sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    storage_trace_domain cx st0 mid.storage_trace /\
    local_ptrs_reserved cenv sa /\ 0 <= i /\ i < 2 ** 256 /\
    eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
    op_taint tn arg = {} /\ op_prov G arg = NONE /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    allocas_from lo s /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         stmt_state_rel H ctx func cenv cx mid s) ==>
    ?r G' tn'. !H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
      (case unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash
               [BaseT (UintT 256)] (IntV i) mid of
         INL v => ?t. r = OK t /\ ~t.vs_halted /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) /\
           expr_val_rel cx (BaseT (BytesT (Fixed 32))) v op t /\
           op_taint tn' op = {} /\ op_prov G' op = NONE /\
           stmt_state_rel H ctx func cenv cx mid t /\ alloca_history func t /\
           tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
           tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
           (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
             FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
       | INR ex => (?u. r = Abort Revert_abort u) /\ expr_exit (INR ex) r /\
           halt_exit H cx mid (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id BLOBHASH [arg] [dst]` >>
  qabbrev_tac `w = typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
                     (evaluate_blob_hash cx.txn (Num i))` >>
  qabbrev_tac `u = update_var dst w s` >>
  `op = Var dst /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `dst`, emitHelperTheory.emit_op_def, comp_bind_def,
        fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!p. not_fresh_at sa p ==> p <> dst` by
    (simp[Abbr `dst`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[Abbr `inst`, Abbr `dst`] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
    (fs[storage_trace_domain_def] >> metis_tac[]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx` by
    metis_tac[stmt_state_rel_state_rel, state_rel_call_ctx_rel] >>
  `step_inst_base inst s = OK u` by
    (simp[Abbr `inst`, Abbr `u`, Abbr `w`, step_inst_base_opcode_eqs,
          mk_inst_def, exec_read1_def] >>
     gvs[call_ctx_rel_def, typed_val_to_w256_def, evaluate_blob_hash_def] >>
     `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
     gvs[val_to_w256_def, integer_wordTheory.i2w_pos, wordsTheory.dimword_def,
         PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes]) >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G inst u` >>
  qabbrev_tac `tn' = step_taint inst s u tn` >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    simp[Abbr `t`, Abbr `u`, update_var_def] >>
  `alloca_history func t` by
    (drule_all alloca_history_base_step >>
     simp[Abbr `t`, Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `op_taint tn' (Var dst) = {} /\ op_prov G' (Var dst) = NONE` by
    simp[Abbr `tn'`, Abbr `G'`, Abbr `inst`, step_taint_def, op_taint_def,
         set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE, out_taint_def,
         step_prov_def, out_prov_def, set_prov_def, op_prov_def, FLOOKUP_DRESTRICT] >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (simp[Abbr `tn'`, Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
          new_site_bytes_def, range_bytes_def, written_taint_def,
          source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
          imm_taint_def, Abbr `u`, update_var_def, mk_inst_def,
          pred_setTheory.EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
       FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> `p <> dst` by metis_tac[] >>
     simp[Abbr `tn'`, Abbr `G'`, Abbr `t`, Abbr `u`, Abbr `inst`,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, step_prov_other_output,
          step_taint_other_output, mk_inst_def]) >>
  `expr_val_rel cx (BaseT (BytesT (Fixed 32))) (evaluate_blob_hash cx.txn (Num i)) op t` by
    simp[expr_val_rel_def, expr_val_at_def, vyperValueTheory.evaluate_type_def,
         is_word_type_def, Abbr `w`, Abbr `t`, Abbr `u`, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`OK t`, `G'`, `tn'`] >> qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx mid s` by metis_tac[] >>
  reverse conj_tac
  >- (`stmt_state_rel H ctx func cenv cx mid t` by
        (simp[stmt_state_rel_inst_idx, Abbr `t`, Abbr `u`] >>
         irule stmt_state_rel_update_var >> simp[] >>
         irule exprSimOperandsTheory.fresh_not_local_ptr >>
         qexists_tac `sa` >> metis_tac[]) >>
      gvs[unop_result_def, evaluate_builtin_def]) >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `taint_ok func tn inst s` by
    simp[taint_ok_def, Abbr `inst`, mk_inst_def,
         contextCodegenRelTheory.source_memory_read_ranges_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def] >>
     `step_inst 0 ctx inst s = OK u` by
       simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def] >>
     simp[] >> fs[Abbr `inst`, mk_inst_def, access_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def,
       Abbr `u`, update_var_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ (ctx_has_dalloca ctx ==> dalloca_no_wrap inst s)` by
    simp[unitTransformDefsTheory.dalloca_no_wrap_def, Abbr `inst`, mk_inst_def,
         is_terminator_def] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (simp[Abbr `t`, Abbr `G'`, Abbr `tn'`] >>
     drule_all straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED
