(* Straight-line memory tail of ordinary slices. *)
Theory exprSimSliceData
Ancestors
  loweringStateRelDefs
  exprSimSliceMemory exprSimSliceBounds exprSimCalldataSlice exprSimPrecompiles
  exprSimBufferStore abiCanonicalHeadSize valueEncodingProps abiDecoderString
  builtinBytes emitHelperProps fragExec exprLoweringProps venomInst
  venomExecSemantics venomState
  compileEnv context words arithmetic list rich_list finite_map

Theorem slice_data_decompose:
  compile_slice_data src_len src_data start len sz sa = (out,sb) ==>
  ?sc sd se sf out_data copy_src.
    compile_assert_slice_bounds start len src_len sa = ((),sc) /\
    compile_slice_out_buf sz sc = ((out,out_data),sd) /\
    emit_op ADD [src_data; start] sd = (copy_src,se) /\
    emit_void MCOPY [out_data; copy_src; len] se = ((),sf) /\
    emit_void MSTORE [out; len] sf = ((),sb)
Proof
  simp[compile_slice_data_def, compile_slice_out_buf_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem slice_mcopy_payload:
  mem_bytes_at src (LENGTH bs) s.vs_memory = bs /\
  start + len <= LENGTH bs ==>
  mcopy dst (src + start) len s =
    write_memory_with_expansion dst (TAKE len (DROP start bs)) s
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`src`, `start`, `len`, `LENGTH (bs:word8 list)`, `s.vs_memory`]
    mem_bytes_at_window) >>
  simp[ADD_COMM] >> strip_tac >>
  simp[mcopy_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem slice_copy_store_run:
  emit_void MCOPY [dst; src; len] sa = ((),sm) /\
  emit_void MSTORE [out; len] sm = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n p) n (mcopy (w2n d) (w2n a) (w2n n) s))
Proof
  strip_tac >>
  qpat_x_assum `emit_void MCOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       mcopy_def, write_memory_with_expansion_def, eval_operand_def] >>
  Cases_on `out` >> Cases_on `len` >>
  gvs[eval_operand_def, lookup_var_def]
QED

(* The saved source pointer and offset are consumed before copying. *)
Theorem slice_data_suffix_run:
  emit_op ADD [src; start] sa = (copy_src,sm) /\
  emit_void MCOPY [dst; copy_src; len] sm = ((),sn) /\
  emit_void MSTORE [out; len] sn = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand dst s = SOME d /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\
  (!z. len = Var z ==> not_fresh_at sa z) /\
  (!z. out = Var z ==> not_fresh_at sa z) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s =
      OK (mstore (w2n p) n (mcopy (w2n d) (w2n (a+b)) (w2n n) t)) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (a+b) s` >>
  reverse conj_tac
  >- (simp[update_var_def, not_fresh_at_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[]) >>
  qpat_x_assum `emit_void MCOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       exec_write2_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `dst` >> Cases_on `len` >> Cases_on `out` >>
  gvs[eval_operand_def, lookup_var_update_var, not_fresh_at_def,
      mcopy_def, write_memory_with_expansion_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >>
  rpt (first_x_assum (qspec_then `sa.cs_next_var` mp_tac)) >> simp[]
QED

Theorem slice_copy_store_encoding:
  mem_bytes_at src (LENGTH bs) s.vs_memory = bs /\
  start + len <= LENGTH bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE len (DROP start bs))) p
    (mstore p (n2w len) (mcopy (p+32) (src+start) len s)).vs_memory
Proof
  strip_tac >> drule_all slice_mcopy_payload >>
  disch_then (qspecl_then [`p+32`] SUBST1_TAC) >>
  `LENGTH (TAKE len (DROP start bs)) = len` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  metis_tac[bytes_buffer_write_encoding]
QED

Theorem slice_data_insts:
  compile_slice_data src_len src_data start len sz sa = (out,sb) /\
  compile_assert_slice_bounds start len src_len sa = ((),sc) /\
  compile_slice_out_buf sz sc = ((out,out_data),sd) /\
  emit_op ADD [src_data; start] sd = (copy_src,se) /\
  emit_void MCOPY [out_data; copy_src; len] se = ((),sf) /\
  emit_void MSTORE [out; len] sf = ((),sb) ==>
  emitted_insts sa sb = emitted_insts sa sc ++
    (emitted_insts sc sd ++ emitted_insts sd sb) /\
  sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb
Proof
  strip_tac >>
  drule slice_out_buf_decompose >> strip_tac >>
  drule (cj 3 slice_bounds_shape) >> strip_tac >>
  qpat_assum `emit_op ADD _ sd = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any strip_assume_tac emit_void_extends) >>
  qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any strip_assume_tac emit_void_extends) >>
  `sb.cs_current_insts = sd.cs_current_insts ++
     (emitted_insts sd se ++ emitted_insts se sf ++ emitted_insts sf sb)` by
    simp[APPEND_ASSOC] >>
  `emitted_insts sd sb =
     emitted_insts sd se ++ emitted_insts se sf ++ emitted_insts sf sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `sd.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sd` by
    (mp_tac (Q.SPECL [`sc`, `sm`, `sd`] emitted_insts_append) >>
     simp[APPEND_ASSOC]) >>
  `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` by
    (mp_tac (Q.SPECL [`sc`, `sd`, `sb`] emitted_insts_append) >>
     simp[APPEND_ASSOC]) >>
  `sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb` by
    (qpat_assum `emitted_insts sd sb = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `emitted_insts sc sb = emitted_insts sc sd ++ emitted_insts sd sb` by
    (match_mp_tac emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (match_mp_tac emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  simp[APPEND_ASSOC]
QED

(* Straight-line compiler interface; concrete bounds instructions stay opaque. *)
Theorem slice_data_control:
  compile_slice_data sl data start len sz sa = (out,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  strip_tac >> drule slice_data_decompose >> strip_tac >>
  drule slice_out_buf_decompose >> strip_tac >>
  drule (cj 3 slice_bounds_shape) >> strip_tac >>
  drule (cj 4 slice_bounds_shape) >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac emit_op_extends >>
  fs[same_blocks_def] >>
  CONV_TAC (RAND_CONV (REWR_CONV emitted_insts_def)) >>
  qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
  simp[NoAsms, DROP_APPEND1]
QED

Theorem slice_data_embedding:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func /\ r.vs_current_bb = sa.cs_current_bb /\
  r.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP r.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule slice_data_control >> strip_tac >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem slice_data_abort:
  compile_slice_data src_len src_data start len sz sa = (out,sb) /\
  eval_operand start s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand src_len s = SOME l /\
  (!z. start = Var z ==> not_fresh_at sa z) /\
  (!z. len = Var z ==> not_fresh_at sa z) /\
  (!z. src_len = Var z ==> not_fresh_at sa z) /\
  (a+n <+ a \/ l <+ a+n) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >> drule slice_data_decompose >> strip_tac >>
  drule_all slice_data_insts >> strip_tac >>
  drule_all slice_bounds_run >> simp[] >> strip_tac >>
  qexists_tac `t` >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
  mp_tac (Q.SPECL [`emitted_insts sa sc`,
    `emitted_insts sc sd ++ emitted_insts sd sb`, `s`] run_inst_seq_append_err) >>
  simp[]
QED

Theorem slice_copy_store_string_encoding:
  mem_bytes_at src (LENGTH text) s.vs_memory = MAP (n2w o ORD) text /\
  start + len <= LENGTH text ==>
  val_in_memory (BaseTV (StringT bound))
    (StringV (TAKE len (DROP start text))) p
    (mstore p (n2w len) (mcopy (p+32) (src+start) len s)).vs_memory
Proof
  strip_tac >>
  `mem_bytes_at src (LENGTH (MAP (n2w o ORD) text : word8 list)) s.vs_memory =
    MAP (n2w o ORD) text` by simp[] >>
  drule_at (Pos hd) slice_copy_store_encoding >>
  simp[GSYM MAP_TAKE, GSYM MAP_DROP, valueEncodingDefsTheory.val_in_memory_def]
QED

Theorem slice_allocated_bytes_write_frame:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) /\
  32 + LENGTH bytes <= sz /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint p sz off len) /\
  (!aid b len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint p sz b len) ==>
  let t = mstore p (n2w (LENGTH bytes))
            (write_memory_with_expansion (p+32) bytes s)
  in stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sa s t
Proof
  strip_tac >> simp[] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s /\
   immutable_alloca_sep func cenv cx es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore p (n2w (LENGTH bytes))
      (write_memory_with_expansion (p+32) bytes s))` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >>
     qexists_tac `s` >>
     conj_tac
     >- (simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
              immutableMemoryFrameTheory.immutable_write_memory_capacity,
              MAX_DEF] >> decide_tac) >>
     conj_tac >- simp[mstore_def, write_memory_with_expansion_def] >>
     simp[] >> rpt strip_tac >>
     `regions_disjoint p sz off (type_memory_size tv)` by
       (fs[immutable_alloca_sep_def] >>
        first_x_assum drule_all >> strip_tac >>
        `regions_disjoint off (type_memory_size tv) p sz` by metis_tac[] >>
        fs[regions_disjoint_def] >> decide_tac) >>
     irule bytes_buffer_write_frame >>
     fs[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (irule bytes_buffer_write_state_rel >> simp[] >> qexists_tac `sz` >>
      simp[] >> rpt strip_tac >>
      first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  conj_tac >- simp[mstore_def, lookup_var_def] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac
  >- (rpt strip_tac >> irule bytes_buffer_write_frame >>
      `regions_disjoint p sz off sz'` by
        (qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
         qexists_tac `aid` >> simp[]) >>
      fs[regions_disjoint_def] >> decide_tac) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists_tac `s` >> simp[exprSimPropsTheory.locals_kept_refl] >>
  rpt strip_tac >> irule bytes_buffer_write_frame >>
  first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

(* The same write keeps the pure frame of an effect-free expression: it lands
   inside a fresh ALLOCA's buffer, clear of the live locals. *)
Theorem slice_allocated_bytes_pure_frame:
  !cenv func es sa s t inst p sz bytes.
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
     FLOOKUP t.vs_allocas aid = SOME b) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (p,sz) /\
  32 + LENGTH bytes <= sz /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint p sz off len) /\
  t.vs_memory = (mstore p (n2w (LENGTH bytes))
                   (write_memory_with_expansion (p+32) bytes s)).vs_memory ==>
  pure_frame cenv func es sa s t
Proof
  rpt strip_tac >>
  match_mp_tac (Q.SPECL [`cenv`, `func`, `es`, `sa`, `s`, `s`, `t`, `inst`,
                         `p`, `sz`] exprSimPropsTheory.pure_frame_buffer_tail) >>
  simp[] >> rpt strip_tac
  >~ [`regions_disjoint p sz lb lsz`]
  >- (qpat_x_assum `!name off len. _` drule >> simp[]) >>
  qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
  irule bytes_buffer_write_frame >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem slice_data_success_run:
 compile_slice_data src_len src_data start len sz sa = (out,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
 eval_operand src_len s = SOME (n2w (LENGTH bs)) /\
 eval_operand src_data s = SOME (n2w src_base) /\
 eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
 (!op z. MEM op [src_len;src_data;start;len] /\ op = Var z ==> not_fresh_at sa z) /\
 mem_bytes_at src_base (LENGTH bs) s.vs_memory = bs /\
 src_base + LENGTH bs < dimword (:256) /\ a+n <= LENGTH bs /\
 32+n <= sz /\ sz < dimword (:256) ==>
 ?t p aid.
 run_inst_seq (emitted_insts sa sb) s = OK t /\
 stmt_state_rel ctx func cenv cx es t /\ loweringPosts$wb_frame cenv es es sa s t /\
 eval_operand out t = SOME p /\
 FLOOKUP t.vs_allocas aid = SOME (w2n p,sz) /\
 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
 w2n p + sz < dimword (:256) /\
 (!name b l. local_region cenv es.scopes t name b l ==> regions_disjoint (w2n p) sz b l) /\
 t.vs_memory = (mstore (w2n p) (n2w n)
   (write_memory_with_expansion (w2n p+32) (TAKE n (DROP a bs)) s)).vs_memory /\
 (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_id = aid)
Proof
  strip_tac >> drule slice_data_decompose >> strip_tac >>
  drule_all slice_data_insts >> strip_tac >>
  `LENGTH bs < dimword (:256) /\ a < dimword (:256) /\ n < dimword (:256)` by decide_tac >>
  `~((n2w a + n2w n : bytes32) <+ n2w a \/
      (n2w (LENGTH bs) : bytes32) <+ n2w a + n2w n)` by
    (mp_tac (Q.INST [`limit` |-> `LENGTH (bs:word8 list)`] slice_bounds_word) >>
     fs[dimword_def]) >>
  `!z. start = Var z ==> not_fresh_at sa z` by metis_tac[MEM] >>
  `!z. len = Var z ==> not_fresh_at sa z` by metis_tac[MEM] >>
  `!z. src_len = Var z ==> not_fresh_at sa z` by metis_tac[MEM] >>
  drule_all slice_bounds_run_frame >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK u` >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >> fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  drule slice_bounds_shape >> strip_tac >>
  qpat_x_assum `emitted_insts sa sc = _` kall_tac >>
  `local_ptrs_reserved cenv sc` by
    (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[DECIDE ``a+5 <= n ==> a <= n``]) >>
  drule slice_out_buf_decompose >> strip_tac >>
  `MEM (mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sc.cs_next_var)]) (fn_insts func)` by
    (irule exprSimHashTheory.hash_emitted_inst_mem >>
     qexistsl_tac [`sa`, `sb`] >>
     `emitted_insts sc sd = emitted_insts sc sm ++ emitted_insts sm sd` by
       (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
     `emitted_insts sc sm =
       [mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sc.cs_next_var)]]` by
       (drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
        CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
        simp[rich_listTheory.DROP_APPEND1]) >>
     simp[MEM_APPEND]) >>
  drule_all slice_out_buf_run >> strip_tac >>
  `!op. MEM op [src_len;src_data;start;len] ==> eval_operand op t = eval_operand op s` by
    (`u.vs_labels = s.vs_labels` by
       (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
     `t.vs_labels = s.vs_labels` by simp[] >>
     rpt strip_tac >> Cases_on `op` >>
     simp[eval_operand_def] >>
     rename1 `MEM (Var z) _` >>
     `not_fresh_at sa z` by
       (qpat_x_assum `!op z. _ ==> not_fresh_at sa z` irule >>
        qexists_tac `Var z` >> simp[]) >>
     `not_fresh_at sc z` by
       (qpat_x_assum `not_fresh_at sa z` mp_tac >>
        pure_rewrite_tac[not_fresh_at_def] >> disch_tac >>
        gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
     fs[lookup_var_def]) >>
  `!z. len = Var z ==> not_fresh_at sd z` by
    (rpt strip_tac >>
     `sc.cs_next_var <= sd.cs_next_var` by
       (`sc.cs_next_var <= sm.cs_next_var` by
          (mp_tac (Q.SPEC `sz` ci_mono_compile_alloc_buffer) >>
           simp[ci_mono_def] >> disch_then (qspec_then `sc` mp_tac) >> simp[]) >>
        qpat_assum `emit_op ADD _ sm = _`
          (mp_then Any strip_assume_tac emitted_insts_emit_op) >> decide_tac) >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``a <= a+5``]) >>
  `eval_operand src_data t = SOME (n2w src_base) /\
   eval_operand start t = SOME (n2w a) /\
   eval_operand len t = SOME (n2w n)` by simp[] >>
  `(!z. out = Var z ==> not_fresh_at sd z) /\
   (!z. out_data = Var z ==> not_fresh_at sd z)` by simp[] >>
  qpat_assum `emit_op ADD _ sd = _`
    (mp_then Any mp_tac slice_data_suffix_run) >>
  disch_then drule_all >>
  strip_tac >> rename1 `v = t with vs_vars := v.vs_vars` >>
  `w2n (p + 32w) = w2n p + 32 /\
   w2n ((n2w src_base : bytes32) + n2w a) = src_base+a /\
   w2n (n2w n : bytes32) = n` by
    (`w2n p + 32 < dimword (:256) /\ src_base+a < dimword (:256)` by decide_tac >>
     simp[word_add_def, w2n_n2w]) >>
  `v.vs_memory = s.vs_memory` by
    (qpat_assum `v = t with vs_vars := _` SUBST1_TAC >>
     simp[NoAsms] >>
     qpat_assum `t.vs_memory = u.vs_memory` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  `mem_bytes_at src_base (LENGTH bs) v.vs_memory = bs` by simp[] >>
  drule_all slice_mcopy_payload >> disch_then (qspec_then `w2n p+32` assume_tac) >>
  qpat_x_assum `run_inst_seq (emitted_insts sd sb) t = _` mp_tac >>
  simp[] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sd sb) t = OK final` >>
  `run_inst_seq (emitted_insts sa sb) s = OK final` by
    (qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     qpat_assum `run_inst_seq (emitted_insts sa sc) s = OK u`
       (mp_then Any (fn th => rewrite_tac[th]) run_inst_seq_append) >>
     qpat_assum `run_inst_seq (emitted_insts sc sd) u = OK t`
       (mp_then Any (fn th => rewrite_tac[th]) run_inst_seq_append) >>
     first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume slice_data_success_run[finish]:
  `sa.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id < sb.cs_next_id` by
    (qpat_assum `emit_op ADD _ sd = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_void MCOPY _ se = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     `sc.cs_next_var <= sm.cs_next_var` by
       (mp_tac (Q.SPEC `sz` ci_mono_compile_alloc_buffer) >>
        simp[ci_mono_def] >> disch_then (qspec_then `sc` mp_tac) >> simp[]) >>
     qpat_assum `emit_op ADD _ sm = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> decide_tac) >>
  qpat_x_assum `compile_slice_data _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_assert_slice_bounds _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_slice_out_buf _ _ = _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `_.cs_current_insts = _` kall_tac) >>
  qpat_x_assum `emitted_insts sa sb = _` kall_tac >>
  `local_ptrs_reserved cenv sd` by
    (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `stmt_state_rel ctx func cenv cx es v` by
    (qpat_assum `v = t with vs_vars := _` SUBST1_TAC >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >> fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  rpt (qpat_x_assum `eval_operand _ s = _` kall_tac) >>
  qpat_x_assum `eval_operand src_data t = _` kall_tac >>
  qpat_x_assum `eval_operand start t = _` kall_tac >>
  qpat_x_assum `eval_operand len t = _` kall_tac >>
  qpat_x_assum `!op z. _` kall_tac >>
  qpat_x_assum `!op. MEM op _ ==> _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `same_blocks _ _` kall_tac >>
  qpat_x_assum `~(_ <+ _ \/ _)` kall_tac >>
  `FLOOKUP v.vs_allocas sc.cs_next_id = SOME (w2n p,sz)` by
    (qpat_assum `v = t with vs_vars := _` SUBST1_TAC >> simp[NoAsms] >>
     first_assum ACCEPT_TAC) >>
  `!aid b l. aid < sa.cs_next_id /\ FLOOKUP v.vs_allocas aid = SOME (b,l) ==>
      regions_disjoint (w2n p) sz b l` by
    (rpt strip_tac >> irule exprSimPrecompilesTheory.state_allocations_disjoint >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `wb_frame cenv es es sa s u` by
    (rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     conj_tac >- (simp[lookup_var_def] >> metis_tac[]) >>
     qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
     simp[NoAsms, exprSimPropsTheory.locals_kept_mem]) >>
  `wb_frame cenv es es sa s t` by
    (match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s`, `sa`, `es`, `es`,
                            `sc`, `u`, `t`, `ctx`] exprSimWordArgsTheory.wb_frame_trans) >>
     simp[] >> decide_tac) >>
  `wb_frame cenv es es sa s v` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> qexists_tac `sd` >> simp[] >>
     conj_tac >- (rpt strip_tac >> fs[lookup_var_def]) >>
     qpat_assum `v = t with vs_vars := _` SUBST1_TAC >> simp[NoAsms] >>
     qpat_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  `!name b l. local_region cenv es.scopes v name b l ==>
      regions_disjoint (w2n p) sz b l` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b l` by
       (irule exprSimPropsTheory.local_region_frame >>
        conj_tac
        >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sd`, `es.scopes`, `v`] >> simp[] >>
        rpt strip_tac >> fs[lookup_var_def]) >>
     qpat_x_assum `!name off len. local_region cenv es.scopes t _ _ _ ==> _` drule >>
     simp[]) >>
  `LENGTH (TAKE n (DROP a bs)) = n` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `final = mstore (w2n p) (n2w n)
      (write_memory_with_expansion (w2n p+32) (TAKE n (DROP a bs)) v)` by
    (simp[Abbr `final`] >>
     AP_TERM_TAC >>
     qpat_assum `mcopy _ _ _ v = _` (fn th =>
       POP_ASSUM_LIST (K all_tac) >> metis_tac[th, ADD_COMM])) >>
  `final = mstore (w2n p) (n2w (LENGTH (TAKE n (DROP a bs))))
     (write_memory_with_expansion (w2n p+32) (TAKE n (DROP a bs)) v)` by simp[] >>
  `stmt_state_rel ctx func cenv cx es final /\ wb_frame cenv es es sa v final` by
    (qpat_assum `final = mstore _ (n2w (LENGTH _)) _` SUBST1_TAC >>
     irule (SIMP_RULE std_ss [LET_THM] slice_allocated_bytes_write_frame) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
                    [STRING #"%" (toString sc.cs_next_var)]`, `sz`] >>
     simp[mk_inst_def] >>
     qpat_assum `sc.cs_next_id = _` (fn th => once_rewrite_tac[GSYM th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sa s final` by
    (match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s`, `sa`, `es`, `es`,
                            `sa`, `v`, `final`, `ctx`] exprSimWordArgsTheory.wb_frame_trans) >>
     simp[]) >>
  `eval_operand out v = SOME p` by
    (qpat_assum `out = Var x` SUBST1_TAC >>
     fs[eval_operand_def, lookup_var_def]) >>
  `final.vs_vars = v.vs_vars /\ final.vs_allocas = v.vs_allocas` by
    (qpat_assum `final = mstore _ (n2w n) _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [mstore_def, write_memory_with_expansion_def,
                      LET_THM, venom_state_accfupds]) >>
  qexistsl_tac [`final`, `p`, `sc.cs_next_id`] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq (emitted_insts sa sc) s = OK u`
        (mp_then Any (fn th => pure_rewrite_tac[th]) run_inst_seq_append) >>
      qpat_assum `run_inst_seq (emitted_insts sc sd) u = OK t`
        (mp_then Any (fn th => pure_rewrite_tac[th]) run_inst_seq_append) >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `eval_operand out v = _` mp_tac >>
      simp[eval_operand_def, lookup_var_def] >>
      qpat_assum `eval_operand out t = SOME p` mp_tac >>
      qpat_assum `out = Var x` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[eval_operand_def, lookup_var_def]) >>
  conj_tac
  >- (qpat_assum `final.vs_allocas = _` (fn th => pure_rewrite_tac[th]) >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes v name b l` by
        (irule exprSimPropsTheory.local_region_frame >>
         conj_tac
         >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`sa`, `es.scopes`, `final`] >> simp[lookup_var_def]) >>
      qpat_assum `!name b l. local_region cenv es.scopes v _ _ _ ==> _` drule >>
      simp[]) >>
  conj_tac
  >- (qpat_assum `final = mstore _ (n2w n) _` SUBST1_TAC >>
      qpat_assum `v.vs_memory = s.vs_memory` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp_tac std_ss [mstore_def, write_memory_with_expansion_def,
                       LET_THM, venom_state_accfupds]) >>
  qexists_tac `mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
                 [STRING #"%" (toString sc.cs_next_var)]` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[mk_inst_def]
QED

Finalise slice_data_success_run
