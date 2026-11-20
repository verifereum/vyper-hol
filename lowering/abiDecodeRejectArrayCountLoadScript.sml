(* A dynamic-array count is loaded only after its ABI head is readable. *)
Theory abiDecodeRejectArrayCountLoad
Ancestors
  abiMalformedRecursiveInterface abiMalformedNavigation abiDecoderReentry
  abiDecoderBytesBound abiDecodePtrMemberFrame exprSimAccounts stateRelProj
  allocaSiteResource fragGasOriginPtr loweringStateRelDefs ptrDiscipline
  venomState abiDecoderContract words arithmetic list

(* These closed premises are discharged by the corresponding local cuts in
   FirstFailure. Keeping them as premises avoids importing the consumer. *)
val bytes_head_cut = ``
  !PG st pos hi head sh func s p L G tn ctx lo.
    abi_decode_bytes_head pos hi st = (head,sh) /\ hi <> Lit 0w /\
    fn_has_code st sh func /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh) /\
    eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
    abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
    p < dimword(:256) /\ L < dimword(:256) /\
    op_prov G pos = NONE /\ op_taint tn pos = {} /\
    op_prov G hi = NONE /\ op_taint tn hi = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    (?u G' tn'.
       u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
       u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (Abort Revert_abort u,G',tn'))) \/
    (p+32 <= L /\ ?u G' tn'.
       u = s with <| vs_vars := u.vs_vars; vs_inst_idx := LENGTH sh.cs_current_insts |> /\
       (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
          FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
       (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
          eval_operand op u = SOME w /\ op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op) /\
       eval_operand head u = SOME (n2w (p+32)) /\
       abi_decoder_operand_live sh.cs_next_var head /\
       op_prov G' head = NONE /\ op_taint tn' head = {} /\ tn'.t_mem = tn.t_mem /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,G',tn')))``;

val scalar_load_cut = ``
  !PG source pos st addr sa value sb func G tn s B L p ctx lo.
    emit_op ADD [Var source;pos] st = (Var addr,sa) /\
    emit_op MLOAD [Var addr] sa = (value,sb) /\
    fn_has_code st sa func /\ fn_has_code sa sb func /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    eval_operand pos s = SOME (n2w p) /\
    op_prov G pos = NONE /\ op_taint tn pos = {} /\
    p+32 <= L /\ B+L < dimword(:256) /\ B+p+32 <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?loaded HG th.
      eval_operand value loaded = SOME (abi_decode_load MLOAD (n2w (B+p):bytes32) s) /\
      op_prov HG value = NONE /\ op_taint th value = {} /\
      allocas_from lo loaded /\ (ctx_has_dalloca ctx ==> allocas_below_fmp loaded) /\
      ~loaded.vs_halted /\
      loaded.vs_current_bb = sb.cs_current_bb /\
      loaded.vs_inst_idx = LENGTH sb.cs_current_insts /\
      loaded.vs_accounts = s.vs_accounts /\ loaded.vs_transient = s.vs_transient /\
      loaded.vs_call_ctx = s.vs_call_ctx /\ loaded.vs_immutables = s.vs_immutables /\
      loaded.vs_memory = s.vs_memory /\ loaded.vs_labels = s.vs_labels /\
      (!x. not_fresh_at st x ==> lookup_var x loaded = lookup_var x s /\
        FLOOKUP HG x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK loaded,HG,th))``;

Theorem malformed_dynarray_head_load_outcome:
  ^bytes_head_cut ==> ^scalar_load_cut ==>
  abi_decode_bytes_head pos hi st = (head,sh) /\
  emit_op ADD [Var source;pos] sh = (Var addr,sa) /\
  emit_op MLOAD [Var addr] sa = (cnt,sl) /\
  fn_has_code st sh func /\ fn_has_code sh sa func /\ fn_has_code sa sl func /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh) /\
  st.cs_next_var <= sh.cs_next_var /\
  abi_malformed_entry H0 ctx func cenv cx es st sites dstid live
    (Var source) hi pos dst B L xs p d outsz s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?u H z.
     u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
     u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort u,H,z))) \/
  (p+32 <= L /\ w2n (mload (B+p) s) = abi_head_word (DROP p xs) /\
   EVERY (abi_decoder_operand_live sl.cs_next_var) [head;cnt;hi] /\
   ?v H z.
     eval_operand head v = SOME (n2w (p+32)) /\
     eval_operand cnt v = SOME (mload (B+p) s) /\
     eval_operand hi v = SOME (n2w L) /\
     op_prov H head = NONE /\ op_taint z head = {} /\
     op_prov H cnt = NONE /\ op_taint z cnt = {} /\
     op_prov H hi = NONE /\ op_taint z hi = {} /\
     allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\ ~v.vs_halted /\
     v.vs_current_bb = sl.cs_current_bb /\ v.vs_inst_idx = LENGTH sl.cs_current_insts /\
     v.vs_accounts = s.vs_accounts /\ v.vs_transient = s.vs_transient /\
     v.vs_call_ctx = s.vs_call_ctx /\ v.vs_immutables = s.vs_immutables /\
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK v,H,z)))
Proof
  disch_then (mk_asm "head_cut") >> disch_then (mk_asm "load_cut") >>
  strip_tac >>
  imp_res_tac abi_decode_bytes_head_fragment_shape >>
  fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  `L < dimword(:256)` by decide_tac >>
  asm_x "head_cut" drule_all >>
  disch_then (qspec_then `PG`
    (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th) STRIP_ASSUME_TAC)) >>
  rename1 `r = s with <|vs_vars := r.vs_vars; vs_inst_idx := _|>` >>
  `r.vs_labels = s.vs_labels /\ r.vs_memory = s.vs_memory /\
   r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
   ~r.vs_halted /\ r.vs_current_bb = sh.cs_current_bb /\
   r.vs_inst_idx = LENGTH sh.cs_current_insts /\
   r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
   r.vs_call_ctx = s.vs_call_ctx /\ r.vs_immutables = s.vs_immutables` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
      (once_rewrite_tac o single) >> simp[]) >>
  `not_fresh_at st source` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `abi_decode_ptr_window G' tn' r source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> metis_tac[]) >>
  `allocas_from lo r` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `B+p+32 <= r.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     drule_all alloca_site_registered_below >> decide_tac) >>
  `eval_operand pos r = SOME (n2w p) /\ op_prov G' pos = NONE /\ op_taint tn' pos = {}` by
    metis_tac[] >>
  `eval_operand hi r = SOME (n2w L) /\ op_prov G' hi = NONE /\ op_taint tn' hi = {} /\
   abi_decoder_operand_live sh.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o SRULE [allocas_below_fmp_def])) >>
  asm_x "load_cut" drule_all >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `!op. abi_decoder_operand_live sh.cs_next_var op ==>
    eval_operand op loaded = eval_operand op r /\
    op_prov HG op = op_prov G' op /\ op_taint th op = op_taint tn' op` by
    (gen_tac >> Cases_on `op` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def,
          eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[op_taint_def]) >>
  `sh.cs_next_var <= sl.cs_next_var` by
    metis_tac[emit_op_extends_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `abi_decoder_operand_live sl.cs_next_var head /\
   abi_decoder_operand_live sl.cs_next_var cnt /\
   abi_decoder_operand_live sl.cs_next_var hi` by
    (simp[] >> metis_tac[abi_decoder_operand_live_mono, abi_decoder_operand_live_emit]) >>
  `B+p < dimword(:256)` by decide_tac >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) r = mload (B+p) s` by
    simp[abi_decode_load_def, w2n_n2w, LESS_MOD, mload_def] >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w (abi_head_word (DROP p xs)) /\
   abi_head_word (DROP p xs) < dimword(:256)` by
    (irule abi_checked_offset_load >> qexists_tac `L` >> simp[abi_decode_source_def]) >>
  `w2n (n2w (B+p):bytes32) = B+p` by metis_tac[w2n_n2w, LESS_MOD] >>
  `w2n (mload (B+p) s) = abi_head_word (DROP p xs)` by
    gvs[abi_decode_load_def, w2n_n2w, LESS_MOD] >>
  disj2_tac >> simp[] >> qexistsl_tac [`loaded`, `HG`, `th`] >> simp[] >>
  `eval_operand head loaded = SOME (n2w (p+32)) /\
   eval_operand hi loaded = SOME (n2w L) /\
   op_prov HG head = NONE /\ op_taint th head = {} /\
   op_prov HG hi = NONE /\ op_taint th hi = {}` by metis_tac[] >>
  simp[] >> rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
