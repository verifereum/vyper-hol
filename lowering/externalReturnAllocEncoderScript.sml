Theory externalReturnAllocEncoder
Ancestors
  externalReturnOutputWindowRun externalReturnCopyAlloc exprSimAlloc
  abiEncoderWindowContract exprLoweringProps compileEnv loweringStateRelDefs fragExec
  venomState venomInst venomMemDefs valueEncoding words

Theorem return_output_alloc_encoder_continuation:
  compile_alloc_buffer msz st = (buf,mid) /\
  compile_abi_encode_to_buf buf.buf_operand src ei mid = (out,en) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv st /\ msz < dimword (:256) /\
  LENGTH (enc at av) <= msz /\ abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  (0 < cap ==>
    (?aid b len. aid < st.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes s name b len /\
      b <= sb /\ sb + cap <= b + len)) ==>
  ?u w.
    frag_exec ctx st mid (\z. z = s) (\z. z = u) (\r. F) /\
    stmt_state_rel ctx func cenv cx es u /\
    u.vs_labels = s.vs_labels /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (w2n w,msz) /\
    ((~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts) ==>
     ?t. abi_encoder_window_result ctx func mid en out at av (w2n w) u t /\
         eval_operand buf.buf_operand t = SOME w)
Proof
  strip_tac >> drule_all alloc_buffer_source_frag_labels >>
  disch_then (qspec_then `\r. F` strip_assume_tac) >>
  `0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (w2n w,msz)` by
    (strip_tac >>
     `sb + cap <= w2n w \/ w2n w + msz <= sb` by
       (irule return_alloc_source_separation >>
        (conj_tac >- simp[]) >>
        qexistsl_tac [`cenv`, `es`, `s`, `st`, `u`] >>
        asm_rewrite_tac[]) >>
     simp[venomMemDefsTheory.regions_disjoint_def]) >>
  `local_ptrs_reserved cenv mid` by
    (irule return_output_alloc_reserved >> metis_tac[]) >>
  `st.cs_next_var <= mid.cs_next_var` by
    (qspecl_then [`msz`, `st`] mp_tac ci_mono_compile_alloc_buffer >>
     gvs[ci_mono_def]) >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at mid x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `0 < cap ==>
    (?aid b len. aid < mid.cs_next_id /\
      FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes u name b len /\
      b <= sb /\ sb + cap <= b + len)` by
    (strip_tac >>
     qpat_x_assum `0 < cap ==> (?aid b len. _) \/ _` drule >> strip_tac
     >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `len`] >>
         simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
     disj2_tac >> qexistsl_tac [`name`, `b`, `len`] >>
     simp[] >> metis_tac[return_alloc_local_region_frame]) >>
  qexistsl_tac [`u`, `w`] >> asm_rewrite_tac[] >> strip_tac >>
  `?t. abi_encoder_window_result ctx func mid en out at av (w2n w) u t` by
    (irule return_output_window_run >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`cap`, `cenv`, `cx`, `buf.buf_operand`, `ei`, `es`,
                   `msz`, `st.cs_next_id`, `sb`, `src`] >>
     asm_rewrite_tac[n2w_w2n]) >>
  qexists_tac `t` >> simp[] >>
  gvs[eval_operand_def] >> irule abi_encoder_window_result_vars >>
  goal_assum (drule_at Any) >> simp[]
QED
