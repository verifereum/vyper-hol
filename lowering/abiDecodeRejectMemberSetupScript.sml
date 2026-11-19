(* One member's setup, before the child decoder is entered. *)
Theory abiDecodeRejectMemberSetup
Ancestors
  abiDecoderMemberSetup abiDecoderMemberCode exprSimAbiDecodeCompositePrefix
  emitHelper emitHelperProps compileEnv fragExec exprSimAccounts
  abiDecoderReentryAddress abiDecoderReentryPointer abiDecoderReentry abiDecodeStaticProps
  decoderNavigationPtr loweringStateRelDefs fragGasOriginPtr bodyPtrDefs
  allocaHistory venomState words arithmetic ptrDiscipline finite_map
  ghostPcTransportPtr abiEncoderPathProps decoderMemberPrefixPtr
  abiMalformedRecursiveInterface abiDecodePtrMemberFrame decoderGhostFramePtr
  bodyPtrSignedConvertSourceFrame bodyBinopFragMemory stmtReasonLitFragMemory
  freshWrites

Theorem malformed_table_setup_split[local]:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  fn_has_code st en func ==>
  ?mid. compile_getelemptr_abi src dyn ao MLOAD base_op hi st = (FST ops,mid) /\
    emit_op ADD [dst;Lit (n2w vo)] mid = (SND ops,en) /\
    mid.cs_blocks = st.cs_blocks /\ mid.cs_current_bb = st.cs_current_bb /\
    inst_extends st mid /\ inst_extends mid en /\
    fn_has_code st mid func /\ fn_has_code mid en func /\
    mid.cs_next_var <= en.cs_next_var
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi _ _ _ _ _ _ st = (_,mid)` >>
  rename1 `emit_op ADD _ mid = (_,en)` >>
  drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  `inst_extends mid en` by metis_tac[inst_extends_emit_op] >>
  `cs_extends st mid` by
    (simp[cs_extends_def] >> fs[inst_extends_def]) >>
  drule emit_op_extends_next_var >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[]
QED

(* Static navigation changes just the temporary and the physical PC. *)
Theorem malformed_table_static_position[local]:
  compile_getelemptr_abi pos F ao MLOAD (Var source) hi sa = (out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  op_prov G pos = NONE /\ allocas_from lo s /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?r H u. eval_operand out r = SOME (n2w (p+ao)) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    fresh_vars_wrt ceiling r /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK r,H,u))
Proof
  strip_tac >> drule getelemptr_static_emit >> strip_tac >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao) /\
   op_taint tn (Lit (n2w ao)) = {} /\ op_prov G (Lit (n2w ao)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `OK t` >>
  drule_all (SRULE [] (Q.SPEC `ADD` emit_scalar_binop_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`u`] >>
  simp[] >>
  `eval_operand out t = SOME (n2w (p+ao))` by fs[word_add_n2w] >>
  simp[fresh_vars_wrt_inst_idx, word_add_n2w] >>
  conj_tac
  >- simp[Abbr `t`, update_var_def] >>
  simp[lookup_var_def] >>
  gvs[lookup_var_def]
QED

Theorem malformed_table_destination_add[local]:
  emit_op ADD [Var output; Lit (n2w vo)] mid = (dst,en) /\
  fn_has_code mid en func /\ ~ctx_has_dalloca ctx /\ ~r.vs_halted /\
  r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
  lookup_var output r = SOME (n2w d) /\ ptr_covers G tn output r outsz /\
  vo + k <= outsz /\ d + vo < dimword (:256) /\ allocas_from lo r /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling r ==>
  ?t H u x. dst = Var x /\ eval_operand dst t = SOME (n2w (d+vo)) /\
    ptr_covers H u x t k /\ fresh_vars_wrt ceiling t /\
    t = r with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH en.cs_current_insts|> /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (r,G,tn) [] (OK t,H,u))
Proof
  strip_tac >>
  `eval_operand (Var output) r = SOME (n2w d) /\
   eval_operand (Lit (n2w vo)) r = SOME (n2w vo) /\
   op_taint tn (Lit (n2w vo)) = {} /\ op_prov G (Lit (n2w vo)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >>
  strip_tac >> qmatch_asmsub_abbrev_tac `OK raw` >>
  `w2n (n2w d : bytes32) = d` by simp[w2n_n2w, LESS_MOD] >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by simp[] >>
  drule_all member_navigation_emit_pointer_pc_uniform_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `x`
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`,`H`,`u`,`x`] >>
  simp[fresh_vars_wrt_inst_idx, eval_operand_def, word_add_n2w] >>
  conj_tac >- simp[Abbr `raw`, update_var_def] >>
  `r with vs_inst_idx := LENGTH mid.cs_current_insts = r` by
    (qpat_assum `r.vs_inst_idx = _` (fn th => once_rewrite_tac [GSYM th]) >>
     simp[venom_state_fupdselfid]) >>
  gvs[lookup_var_def]
QED

(* Read-only setup changes the physical PC and temporary registers only. *)
Theorem malformed_table_resource_frame[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >> irule abi_malformed_resource_post_frame_intro >>
  `!H0 : (bool # bytes32 # type_value) list # num list.
      stmt_state_rel H0 ctx func cenv cx es s ==>
      stmt_state_rel H0 ctx func cenv cx es t` by
    (rpt strip_tac >> irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`s`,`st`] >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es t` by simp[] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >> simp[]) >>
  simp[] >> conj_tac
  >- (Cases >> simp[eval_operand_def, abi_decoder_operand_live_def,
                   abi_decoder_older_vars_def, GSYM not_fresh_at_def]) >>
  qexists_tac `H` >> simp[]
QED

Theorem malformed_table_setup_history[local]:
  abi_decode_member_setup dst pos MLOAD src hi dyn ao vo st = (ops,en) /\
  fn_has_code st en func /\ alloca_history func s /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH en.cs_current_insts|> ==>
  alloca_history func t /\ en.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >> simp[] >>
  `en.cs_current_insts = st.cs_current_insts ++ emitted_insts st en` by
    simp[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all fn_has_code_code >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st en ++ rest` by
    fs[rich_listTheory.IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts st en)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[venomInstTheory.is_alloca_op_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts st en)` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >> simp[listTheory.LENGTH_APPEND]) >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st en))` by
    (irule alloca_history_no_alloca_slice >> gvs[]) >>
  qpat_x_assum `alloca_history func (t with vs_inst_idx := _)` mp_tac >>
  qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th, venom_state_fupdselfid])
QED

(* The dynamic premise concerns only the source slice at the incoming triple.
   A successful nonwrap guard need not place the child inside the window. *)
Theorem malformed_table_member_setup_cut:
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi dyn ao vo st = (ops,en) /\
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs b d outsz s /\
  fn_has_code st en func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s source (n2w B) L /\ ptr_covers G tn output s outsz /\
  op_taint tn pos = {} /\ op_prov G pos = NONE /\
  op_taint tn hi = {} /\ op_prov G hi = NONE /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  vo + k <= outsz /\ b + ao + (if dyn then 32 else 0) <= L /\
  (!mid out. dyn /\ compile_getelemptr_abi pos T ao MLOAD (Var source) hi st = (out,mid) /\
    fn_has_code st mid func /\ mid.cs_next_var <= ceiling.cs_next_var ==>
    (?r G1 tn1. r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
      r.vs_immutables = s.vs_immutables /\ r.vs_call_ctx = s.vs_call_ctx /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort r,G1,tn1)) \/
    (b + abi_head_word (DROP (b+ao) xs) < dimword (:256) /\
     ?r G1 tn1. eval_operand out r = SOME (n2w (b + abi_head_word (DROP (b+ao) xs))) /\
      op_taint tn1 out = {} /\ op_prov G1 out = NONE /\
      r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH mid.cs_current_insts|> /\
      fresh_vars_wrt ceiling r /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==> lookup_var x r = lookup_var x s /\
        FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK r,G1,tn1))) ==>
  (?r G1 tn1. r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
    r.vs_immutables = s.vs_immutables /\ r.vs_call_ctx = s.vs_call_ctx /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort r,G1,tn1)) \/
  (?t H1 u x. SND ops = Var x /\
    abi_malformed_entry H ctx func cenv cx es en sites dstid live
      (Var source) hi (FST ops) (Var x) B L xs
      (b + (if dyn then abi_head_word (DROP (b+ao) xs) else ao)) (d+vo) k t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    ptr_covers H1 u x t k /\ abi_decode_ptr_window H1 u t source (n2w B) L /\
    op_taint u (FST ops) = {} /\ op_prov H1 (FST ops) = NONE /\
    op_taint u hi = {} /\ op_prov H1 hi = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt ceiling t /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\ t.vs_call_ctx = s.vs_call_ctx /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H1 x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,H1,u))
Proof
  strip_tac >> drule_all malformed_table_setup_split >> strip_tac >>
  drule abi_decoder_member_pointer_counters >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= ceiling.cs_next_var /\
   st.cs_next_var <= en.cs_next_var` by
    (Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[] >> decide_tac) >>
  `B + L < dimword (:256) /\ d + outsz < dimword (:256) /\
   eval_operand pos s = SOME (n2w b) /\ lookup_var output s = SOME (n2w d) /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [Var source;hi;pos;Var output]` by
    fs[abi_malformed_entry_def,abi_malformed_allocated_window_def,eval_operand_def] >>
  qabbrev_tac `q = b + (if dyn then abi_head_word (DROP (b+ao) xs) else ao)` >>
  `(?r G1 tn1. r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
      r.vs_immutables = s.vs_immutables /\ r.vs_call_ctx = s.vs_call_ctx /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort r,G1,tn1)) \/
   (q < dimword (:256) /\
    ?r G1 tn1. eval_operand (FST ops) r = SOME (n2w q) /\
      op_taint tn1 (FST ops) = {} /\ op_prov G1 (FST ops) = NONE /\
      r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH mid.cs_current_insts|> /\
      fresh_vars_wrt ceiling r /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==> lookup_var x r = lookup_var x s /\
        FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK r,G1,tn1))` by
    (Cases_on `dyn`
     >- (qpat_x_assum `!mid out. _` (qspecl_then [`mid`,`FST ops`] mp_tac) >>
         simp[Abbr `q`]) >>
     disj2_tac >> simp[Abbr `q`] >>
     conj_tac >- (fs[] >> decide_tac) >>
     drule_all malformed_table_static_position >>
     disch_then (qspec_then `PG` mp_tac) >> simp[]) >-
    (disj1_tac >> qexistsl_tac [`r`,`G1`,`tn1`] >> simp[]) >>
  qpat_x_assum `!mid out. dyn /\ compile_getelemptr_abi _ _ _ _ _ _ _ = _ /\ _ ==> _` kall_tac >>
  `not_fresh_at st output /\ not_fresh_at st source /\
   (!x. hi = Var x ==> not_fresh_at st x)` by
    (Cases_on `hi` >> gvs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
   r.vs_inst_idx = LENGTH mid.cs_current_insts /\ allocas_from lo r` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac [th]) >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `lookup_var output r = SOME (n2w d) /\ ptr_covers G1 tn1 output r outsz` by
    (qpat_assum `!x. not_fresh_at st x ==> _` (drule_then strip_assume_tac) >>
     simp[] >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `d + vo < dimword (:256)` by decide_tac >>
  drule_all malformed_table_destination_add >>
  disch_then (qspec_then `PG` (qx_choose_then `t` (qx_choose_then `H1`
    (qx_choose_then `u` (qx_choose_then `x` strip_assume_tac))))) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH en.cs_current_insts|>` by
    (map_every (fn pat => qpat_assum pat (fn th => once_rewrite_tac [th]))
      [`t = r with <|vs_vars := _; vs_inst_idx := _|>`,`r = s with <|vs_vars := _; vs_inst_idx := _|>`] >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H1 x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at mid x'` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[]) >>
  `eval_operand (FST ops) t = SOME (n2w q) /\
   op_taint u (FST ops) = {} /\ op_prov H1 (FST ops) = NONE` by
    (`t.vs_labels = r.vs_labels` by
       (qpat_assum `t = r with <|vs_vars := _; vs_inst_idx := _|>`
          (fn th => once_rewrite_tac [th]) >> simp[]) >>
     Cases_on `FST ops` >>
     gvs[eval_operand_def, op_taint_def, op_prov_def,
         abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `op_taint u hi = {} /\ op_prov H1 hi = NONE` by
    (Cases_on `hi` >>
     gvs[op_taint_def, op_prov_def, abi_decoder_operand_live_def,
         abi_decoder_older_vars_def, GSYM not_fresh_at_def]) >>
  `stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv st` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    (irule malformed_table_resource_frame >>
     `t.vs_inst_idx = LENGTH en.cs_current_insts` by
        (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
           (fn th => once_rewrite_tac [th]) >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `alloca_history func t /\ en.cs_current_bb = st.cs_current_bb` by
    (drule_all malformed_table_setup_history >> simp[]) >>
  `local_ptrs_reserved cenv en` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `EVERY (abi_decoder_operand_live en.cs_next_var) [Var source;hi;FST ops;Var x]` by
    (fs[] >> metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]) >>
  `abi_malformed_entry H ctx func cenv cx es en sites dstid live (Var source) hi
     (FST ops) (Var x) B L xs q (d+vo) k t` by
    (irule abi_malformed_child_entry >>
     `d <= d+vo /\ d+vo+k <= d+outsz /\ d+vo+k < dimword (:256)` by decide_tac >>
     `eval_operand (Var x) t = SOME (n2w (d+vo))` by metis_tac[] >>
     simp[] >>
     qhdtm_assum `abi_malformed_entry` (irule_at Any) >> simp[] >> decide_tac) >>
  `abi_decode_ptr_window H1 u t source (n2w B) L` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `source` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
   t.vs_inst_idx = LENGTH en.cs_current_insts /\ allocas_from lo t /\
   lo <= t.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  disj2_tac >> qexistsl_tac [`t`,`H1`,`u`,`x`] >> simp[] >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED
