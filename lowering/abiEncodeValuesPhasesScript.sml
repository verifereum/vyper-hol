Theory abiEncodeValuesPhases
Ancestors
  assignTuplePtrCopyLen abiEncoderWindowPhase abiEncoderWindowCursor abiEncoderWindowSequence
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedArrayBody
  abiEncoderPrimitiveEffect abiEncoderWindowContract abiEncoderRegisteredEffect
  bodyFullAbiEncodeOffset bodyFullAbiEncodeStore
  bodyPtrMakeArrayPrimitiveInstall
  allocaSiteResource wordLoadStorePtr instMemFrontier unitTransformDefs memSafeRun entryDecodeProps memoryReadProps
  fragGasOriginPtr bodyPtrDefs ptrDiscipline
  decoderNavigationPtr[qualified,ignore_grammar]
  fragExec emitHelperProps emitHelper exprLoweringProps loweringPosts loweringStateRelDefs compileEnv
  context vyperValue vyperTyping vyperABI contractABI
  valueEncodingProps valueEncodingDefs venomExecSemantics venomState venomInst venomMemDefs
  words byte finite_map pred_set arithmetic list pair

Theorem abi_encode_values_head_address_endpoint:
  emit_op ADD [Var dst;Lit (n2w off)] st = (head,en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  off + n <= cap /\ b + cap <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p t G' tn'.
    head = Var p /\ not_fresh_at en p /\ ptr_covers G' tn' p t n /\
    eval_operand head t = SOME (n2w (b+off)) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    t = (update_var p (n2w b + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `b + off < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `b < dimword (:256)` by decide_tac >>
  `lookup_var dst s = SOME (n2w b)` by fs[eval_operand_def] >>
  `w2n (n2w b : bytes32) + off < dimword (:256)` by simp[w2n_n2w] >>
  drule_all abi_encode_owned_offset_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `p` (qx_choose_then `t`
      (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))))) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st en s raw` >>
  drule emitted_insts_emit_op >> strip_tac >>
  `p = STRING #"%" (toString st.cs_next_var)` by metis_tac[operand_11] >>
  `raw = update_var p (n2w b + n2w off) s` by
    (qpat_assum `window_pure_seq st en s raw` (mp_tac o REWRITE_RULE [window_pure_seq_def, window_seq_def]) >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operands_def, ADD_COMM]) >>
  `LENGTH en.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `t = raw with vs_inst_idx := LENGTH en.cs_current_insts` by simp[] >>
  `abi_encode_exec_frame func s raw` by
    (irule abi_encode_framed_ordinary_pure_sequence >>
     qexistsl_tac [`en`,`st`] >> simp[mk_inst_def, is_terminator_def,
       is_alloca_op_def, is_ext_call_op_def]) >>
  `window_phase ctx func st en {} [] s t` by metis_tac[window_pure_seq_phase] >>
  `!x. not_fresh_at st x ==> x <> p` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand head t = SOME (n2w (b + off))` by
    (qpat_assum `head = Var p` (fn th => PURE_REWRITE_TAC [th,eval_operand_def]) >>
     qpat_assum `lookup_var p t = SOME _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[w2n_n2w]) >>
  `abi_encode_exec_frame func s t` by
    (qpat_assum `t = raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [abi_encode_exec_frame_inst_idx] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`p`,`t`,`G'`,`tn'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

Theorem abi_encode_values_head_address:
  emit_op ADD [Var dst;Lit (n2w off)] st = (head,en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  off + n <= cap /\ b + cap <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p t G' tn'.
    head = Var p /\ not_fresh_at en p /\ ptr_covers G' tn' p t n /\
    eval_operand head t = SOME (n2w (b+off)) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_head_address_endpoint >> metis_tac[]
QED

(* Delayed materialization keeps cursor and destination allocations that
   were reserved before the read and are disjoint from its live locals. *)
Theorem abi_encode_values_unwrap_window:
  wb_frame ce ee ee st s t /\ ghost_kept_at lo ce ee st G tn s G' tn' /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) /\ id < st.cs_next_id /\
  (!name a n. local_region ce ee.scopes s name a n ==>
    b + sz <= a \/ a + n <= b) /\ b <= q /\ q + len <= b + sz ==>
  FLOOKUP t.vs_allocas id = SOME (b,sz) /\
  mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory /\
  (!i. q <= i /\ i < q + len /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas id = SOME (b,sz) /\
   mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  `q - b + len <= sz` by decide_tac >>
  `b + (q - b) = q` by decide_tac >>
  `!u. mem_bytes_at q len u.vs_memory =
    TAKE len (DROP (q - b) (mem_bytes_at b sz u.vs_memory))` by
    (gen_tac >> drule read_memory_subwindow >>
     disch_then (qspecl_then [`b`,`u`] mp_tac) >>
     simp[read_memory_eq_mem_bytes_at]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  fs[ghost_kept_at_def] >> rpt strip_tac >>
  `b <= i /\ i < b + sz` by decide_tac >> metis_tac[]
QED

Theorem abi_encode_values_cursor_load:
  emit_op MLOAD [Var cursor] st = (out,en) /\
  eval_operand (Var cursor) s = SOME (n2w b) /\
  ptr_covers G tn cursor s 32 /\ b + 32 <= s.vs_alloca_next /\
  (!i. b <= i /\ i < b + 32 ==> i NOTIN tn.t_mem) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    eval_operand out t = SOME (mem_word_at b s.vs_memory) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ op_taint tn' out = {} /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn'))
Proof
  strip_tac >>
  `b < dimword (:256)` by
    (drule alloca_room_next_lt >> decide_tac) >>
  drule_all window_cursor_load_sequence >> strip_tac >>
  rename1 `window_pure_seq st en s raw` >>
  `run_inst_seq (emitted_insts st en) s = OK raw` by
    fs[window_pure_seq_def, window_seq_def] >>
  `lookup_var cursor s = SOME (n2w b)` by fs[eval_operand_def] >>
  `!i. w2n (n2w b : bytes32) <= i /\ i < w2n (n2w b : bytes32) + 32 ==>
       i NOTIN tn.t_mem` by simp[w2n_n2w] >>
  drule_all decoderNavigationPtrTheory.emit_mload_clean_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`, `ARB`, `ctx`, `PG`, `ARB`] strip_assume_tac) >>
  rename1 `op_taint tf out = {}` >> rename1 `op_prov GF out = NONE` >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`, `GF`, `tf`] >>
  `abi_encode_exec_frame func s raw` by
    (irule abi_encode_framed_ordinary_pure_sequence >>
     qexistsl_tac [`en`, `st`] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def,
       is_alloca_op_def, is_ext_call_op_def]) >>
  `window_phase ctx func st en {} [] s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_pure_seq_phase >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),GF,tf)` by
    (rpt strip_tac >> first_x_assum irule >> simp[w2n_n2w]) >>
  Cases_on `out` >>
  fs[eval_operand_def, lookup_var_def, GSYM mem_word_at_eq_mload]
QED

Theorem abi_encode_values_head_store:
  emit_void MSTORE [Var head;src] st = ((),en) /\
  eval_operand (Var head) s = SOME (n2w d) /\
  eval_operand src s = SOME w /\ op_taint tn src = {} /\
  ptr_covers G tn head s 32 /\ d + 32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t tn'.
    mem_bytes_at d 32 t.vs_memory = word_to_bytes w T /\
    window_phase ctx func st en {} [(d,32)] s t /\ abi_encode_exec_frame func s t /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d + 32} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tn'))
Proof
  strip_tac >>
  `d < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `lookup_var head s = SOME (n2w d)` by fs[eval_operand_def] >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  `inst_mem_below_frontier (mk_inst st.cs_next_id MSTORE [Var head;src] []) s /\
   inst_dload_in_section (mk_inst st.cs_next_id MSTORE [Var head;src] []) s` by
    simp[below_frontier_MSTORE, inst_dload_in_section_def, mk_inst_def, w2n_n2w] >>
  qabbrev_tac `tn' = step_taint
    (mk_inst st.cs_next_id MSTORE [Var head;src] []) s (mstore d w s) tn` >>
  qabbrev_tac `t = (mstore d w s) with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `LENGTH en.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tn')` by
    (gen_tac >>
     mp_tac (Q.SPECL [`s`,`ctx`,`func`,`bb`,`st.cs_next_id`,
       `head`,`src`,`n2w d`,`w`,`D`,`lo`,`explicit`,`PG`,`G`,`tn`]
       abi_encode_mstore_origin_path) >>
     simp[w2n_n2w, Abbr `t`, Abbr `tn'`]) >>
  `window_phase ctx func st en {} [(d,32)] s t` by
    (unabbrev_all_tac >> irule window_store_phase >>
     simp[abi_encoder_output_store] >>
     qexistsl_tac [`Var head`,`src`] >> simp[]) >>
  qexistsl_tac [`t`, `tn'`] >>
  drule_all mstore_ghost_frame >> simp[Abbr `t`, Abbr `tn'`, w2n_n2w,
    mem_bytes_at_mstore_same, step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem abi_encode_values_word_head:
  compile_store_memory ce src (Var head) ty ty st = ((),en) /\
  is_word_type ty /\ evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand (Var head) s = SOME (n2w d) /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
  ptr_covers G tn head s 32 /\ d + 32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t tn'.
    mem_bytes_at d 32 t.vs_memory = enc (vyper_to_abi_type env ty) av /\
    window_phase ctx func st en {} [(d,32)] s t /\ abi_encode_exec_frame func s t /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d + 32} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tn'))
Proof
  strip_tac >>
  `emit_void MSTORE [Var head;src] st = ((),en)` by
    fs[compile_store_memory_def] >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  drule_all abi_encode_values_head_store >> simp[]
QED

(* Each cursor action and recursive child protects pre-existing windows
   disjoint from its writes, including their readable-byte taint status. *)
Theorem abi_encode_values_protected_window:
  window_phase ctx func st en ids outs s t /\
  q + n <= s.vs_alloca_next /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs /\
  (!id b sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) /\
  (!i. EVERY (\(b,sz). i < b \/ b+sz <= i) outs /\
    (!id b sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      i < b \/ b+sz <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory /\
  (!i. q <= i /\ i < q + n /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  conj_tac
  >- (mp_tac (Q.INST [`ids` |-> `ids`, `outs` |-> `outs`, `s` |-> `s`, `t` |-> `t`,
          `q` |-> `q`, `n` |-> `n`] window_alloca_growth_frame) >>
      asm_rewrite_tac[]) >>
  rpt strip_tac >>
  `EVERY (\(b,sz). i < b \/ b+sz <= i) outs` by
    (simp[EVERY_MEM, FORALL_PROD] >> qx_genl_tac [`b`,`sz`] >> disch_tac >>
     qpat_assum `EVERY (\r. regions_disjoint _ r) outs`
       (qspec_then `(b,sz):num # num` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     asm_simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!id r. FLOOKUP s.vs_allocas id = SOME r ==> FLOOKUP t.vs_allocas id = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `!id b sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      i < b \/ b+sz <= i` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`q` |-> `q`,`n` |-> `n`,`ids` |-> `ids`,
         `s` |-> `s`,`t` |-> `t`] window_alloca_growth_protected) >>
     asm_rewrite_tac[] >> disch_then (qspecl_then [`id`,`b`,`sz`] mp_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!j. EVERY _ _ /\ _ ==> _` (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[]
QED

(* Cursor and payload windows are subranges of registered allocations.
   Recursively allocated scratch is disjoint from each earlier window. *)
Theorem abi_encode_values_registered_window:
  window_phase ctx func st en ids outs s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (b,sz) /\ owner NOTIN ids /\
  b <= q /\ q+n <= b+sz /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs /\
  (!i. EVERY (\(p,k). i < p \/ p+k <= i) outs /\
    (!id p k. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      i < p \/ p+k <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  FLOOKUP t.vs_allocas owner = SOME (b,sz) /\
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory /\
  (!i. q <= i /\ i < q+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  drule_then assume_tac window_phase_effect >>
  `FLOOKUP t.vs_allocas owner = SOME (b,sz)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `b+sz <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `q+n <= s.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >>
  irule abi_encode_values_protected_window >>
  qpat_assum `window_phase ctx func st en ids outs s t` (irule_at Any) >>
  asm_rewrite_tac[] >> qx_genl_tac [`id`,`p`,`k`] >> strip_tac >>
  `id <> owner` by metis_tac[] >>
  `venomMemDefs$regions_disjoint (b,sz) (p,k)` by
    metis_tac[alloca_site_registered_disjoint] >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_values_pointer_frame:
  window_phase ctx func st en ids outs s t /\
  not_fresh_at st x /\ eval_operand (Var x) s = SOME w /\
  ptr_covers G tn x s n /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  eval_operand (Var x) t = SOME w /\ ptr_covers G' tn' x t n
Proof
  simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  `lookup_var x t = SOME w` by metis_tac[window_phase_vars] >>
  asm_rewrite_tac[] >> metis_tac[ptr_covers_lookup_frame]
QED
