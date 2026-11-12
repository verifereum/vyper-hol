(* Source and code partitions for primitive storage Append composition. *)
Theory stmtSimAppendStorageCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  appendStorageRel stmtSimAppendStorage stmtSimAssignStorage stmtSimAssignStorageCopy fragExec
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq fragGasSeqAbort list rich_list
  varsExt freshWrites stateFrame venomState finite_map 
  accountsRelProps vyperStorage vyperStorageBackend vyperValue vfmState
  exprOperandVar stmtSimStoreCopyState bodyAppendStorageStaging externalEntryShape loweringHalt context abiTupleProps
  vyperInterpreter vyperState vyperExprNoControl stmtLowering exprLowering
  exprLoweringProps compileEnv loweringStateRelDefs emitHelper emitHelperProps venomInst venomExecSemantics
Libs
  monadsyntax

Theorem append_storage_word_code_parts:
  stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e) sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 ==>
  c = cenv /\ ?sb op.
    lower_value compile_expr cenv elem e sa = (op,sb) /\
    compile_dynarray_append cenv (Lit slot) op 1 1 elem
      (lowered_value_type cenv e) cap T
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf)
Proof
  strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `tr` >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       load_opc_for_def, store_opc_for_def] >>
  Cases_on `lower_value compile_expr cenv elem e sa` >>
  rename1 `lower_value _ _ _ _ _ = (op,sb)` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = (u,_)` >>
  Cases_on `u` >> simp[]
QED

Theorem append_storage_copy_code_parts:
  stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e) sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\ ~is_word_type elem ==>
  c = cenv /\ ?sb raw tmp sc sd.
    lower_value compile_expr cenv elem e sa = (raw,sb) /\
    compile_alloc_buffer (type_memory_bytes cenv elem) sb = (tmp,sc) /\
    compile_store_memory cenv raw tmp.buf_operand elem
      (lowered_value_type cenv e) sc = ((),sd) /\
    compile_dynarray_append cenv (Lit slot) tmp.buf_operand 1
      ((type_memory_bytes cenv elem + 31) DIV 32) elem elem cap F
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sd = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def,
       target_root_type_def, target_root_capacity_def, target_to_expr_def,
       compile_target_base_def, infer_array_location_def] >>
  Cases_on `tr` >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       load_opc_for_def, store_opc_for_def] >>
  Cases_on `lower_value compile_expr cenv elem e sa` >>
  rename1 `lower_value _ _ _ _ _ = (raw,sb)` >> simp[] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv elem) sb` >>
  rename1 `compile_alloc_buffer _ _ = (tmp,sc)` >> simp[] >>
  Cases_on `compile_store_memory cenv raw tmp.buf_operand elem (lowered_value_type cenv e) sc` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sd)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem append_storage_copy_suffix_parts:
  compile_dynarray_append cenv bop vop 1 stride dt st cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) s0 = ((),s9) <=>
  ?lop valid dop off pop nop u s1 s2 s3 s4 s5 s6 s7 s8.
    emit_op (if tr then TLOAD else SLOAD) [bop] s0 = (lop,s1) /\
    emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
    emit_void ASSERT [valid] s2 = ((),s3) /\
    emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
    emit_op MUL [lop; Lit (n2w stride)] s4 = (off,s5) /\
    emit_op ADD [dop; off] s5 = (pop,s6) /\
    compile_word_copy_loop vop pop stride LocMemory
      (if tr then LocTransient else LocStorage) F s6 = (u,s7) /\
    emit_op ADD [lop; Lit 1w] s7 = (nop,s8) /\
    emit_void (if tr then TSTORE else SSTORE) [bop; nop] s8 = ((),s9)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  pairarg_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `(\(_0,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem append_storage_copy_prefix_path:
  emit_op (if tr then TLOAD else SLOAD) [bop] s0 = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w stride)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (pop,s6) /\
  fn_has_code s0 s6 func /\ cap < dimword (:256) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME b /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at s0 x) /\
  ~s.vs_halted /\ s.vs_current_bb = s0.cs_current_bb /\
  s.vs_inst_idx = LENGTH s0.cs_current_insts ==>
  let len = if tr then tload slot s else sload slot s in
  (!x. lop = Var x \/ pop = Var x ==> not_fresh_at s6 x) /\
  (if w2n len < cap then
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
      t.vs_inst_idx = LENGTH s6.cs_current_insts /\
      eval_operand lop t = SOME len /\
      eval_operand pop t = SOME (slot + 1w + len * n2w stride) /\
      eval_operand vop t = SOME b /\ store_copy_normalize s t = s /\
      (!x. not_fresh_at s0 x ==> lookup_var x t = lookup_var x s)
   else ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  conj_tac >- (rw[not_fresh_at_def] >>
    goal_assum (drule_at Any) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `w2n len < cap` >>
  qmatch_asmsub_abbrev_tac `fn_has_code s0 sf func` >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s0 sf) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, Abbr `sf`, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `code = emitted_insts s0 sf` by simp[Abbr `code`] >>
  qpat_x_assum `Abbrev (code = _)` kall_tac >>
  `code = [
    mk_inst s0.cs_next_id (if tr then TLOAD else SLOAD) [bop]
      [STRING #"%" (toString s0.cs_next_var)];
    mk_inst (s0.cs_next_id+1) LT
      [Var (STRING #"%" (toString s0.cs_next_var)); Lit (n2w cap)]
      [STRING #"%" (toString (s0.cs_next_var+1))];
    mk_inst (s0.cs_next_id+2) ASSERT
      [Var (STRING #"%" (toString (s0.cs_next_var+1)))] [];
    mk_inst (s0.cs_next_id+3) ADD [bop; Lit 1w]
      [STRING #"%" (toString (s0.cs_next_var+2))];
    mk_inst (s0.cs_next_id+4) MUL
      [Var (STRING #"%" (toString s0.cs_next_var)); Lit (n2w stride)]
      [STRING #"%" (toString (s0.cs_next_var+3))];
    mk_inst (s0.cs_next_id+5) ADD
      [Var (STRING #"%" (toString (s0.cs_next_var+2)));
       Var (STRING #"%" (toString (s0.cs_next_var+3)))]
      [STRING #"%" (toString (s0.cs_next_var+4))]]` by
    (simp[emitted_insts_def, Abbr `sf`] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  `!n w u. s0.cs_next_var <= n ==>
    eval_operand bop (update_var (STRING #"%" (toString n)) w u) =
      eval_operand bop u /\
    eval_operand vop (update_var (STRING #"%" (toString n)) w u) =
      eval_operand vop u` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     metis_tac[]) >>
  `?u. run_inst_seq code s =
    (if w2n len < cap then OK u else
      Abort Revert_abort (revert_state (set_returndata [] u))) /\
    (w2n len < cap ==>
      ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
      eval_operand (Var (STRING #"%" (toString s0.cs_next_var))) u = SOME len /\
      eval_operand (Var (STRING #"%" (toString (s0.cs_next_var+4)))) u =
        SOME (slot+1w+len*n2w stride) /\
      eval_operand vop u = SOME b /\ store_copy_normalize s u = s /\
      (!x. not_fresh_at s0 x ==> lookup_var x u = lookup_var x s))` by
    (qpat_x_assum `code = [_;_;_;_;_;_]` SUBST1_TAC >>
     Cases_on `tr` >>
     simp[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
          exec_read1_def, exec_pure2_def, eval_operand_update_var,
          eval_operand_update_other, eval_operand_def, lookup_var_update_var,
          wordsTheory.w2n_n2w, bool_to_word_def, Abbr `len`] >>
     (IF_CASES_TAC >- (simp[lookup_var_update_var] >> metis_tac[]) >>
      simp[lookup_var_update_var] >>
      simp[update_var_def,
           stmtSimStoreCopyTheory.store_copy_normalize_def,
           venom_state_component_equality] >>
      rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[])) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0 /\
   LENGTH code = 6` by
    (qpat_x_assum `code = [_;_;_;_;_;_]` SUBST1_TAC >>
     Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  IF_CASES_TAC >> fs[]
  >- (qspecl_then [`code`, `s`, `u`, `ctx`, `func`, `bb`]
        mp_tac tuple_run_inst_seq_gas_path >>
      impl_tac >- (fs[EVERY_MEM] >> metis_tac[]) >> strip_tac >>
      qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 6` >>
      simp[gas_marked_path_def, eval_operand_def, lookup_var_def] >>
      fs[eval_operand_def, lookup_var_def] >> gvs[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem append_storage_copy_header_path:
  emit_op ADD [lop; Lit 1w] s7 = (nop,s8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] s8 = ((),s9) /\
  fn_has_code s7 s9 func /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME len /\
  (!x. bop = Var x \/ lop = Var x ==> not_fresh_at s7 x) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = s7.cs_current_bb /\
  s.vs_inst_idx = LENGTH s7.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = s9.cs_current_bb /\
    t.vs_inst_idx = LENGTH s9.cs_current_insts /\
    (!x. not_fresh_at s7 x ==> lookup_var x t = lookup_var x s) /\
    store_copy_normalize s t =
      (if tr then tstore else sstore) slot (len+1w) s
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  qmatch_asmsub_abbrev_tac `fn_has_code s7 sf func` >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s7 sf) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, Abbr `sf`, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `code = [mk_inst s7.cs_next_id ADD [lop; Lit 1w]
       [STRING #"%" (toString s7.cs_next_var)];
     mk_inst (s7.cs_next_id+1) (if tr then TSTORE else SSTORE)
       [bop; Var (STRING #"%" (toString s7.cs_next_var))] []]` by
    (simp[Abbr `code`, emitted_insts_def, Abbr `sf`] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  `!w u. eval_operand bop
       (update_var (STRING #"%" (toString s7.cs_next_var)) w u) =
       eval_operand bop u` by
    (rpt strip_tac >> irule
       (cj 1 exprSimWordBuiltinsTheory.eval_operand_update_not_fresh) >>
     qexists_tac `s7` >> simp[] >> metis_tac[]) >>
  `?u. run_inst_seq code s = OK u /\ ~u.vs_halted /\
     u.vs_current_bb = s.vs_current_bb /\
     (!x. not_fresh_at s7 x ==> lookup_var x u = lookup_var x s) /\
     store_copy_normalize s u =
       (if tr then tstore else sstore) slot (len+1w) s` by
    (qpat_x_assum `code = [_;_]` SUBST1_TAC >>
     Cases_on `tr` >>
     simp[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
          exec_pure2_def, exec_write2_def, eval_operand_def,
          eval_operand_update_var, lookup_var_update_var] >>
     `eval_operand bop
       (s with vs_vars := s.vs_vars |+
         (STRING #"%" (toString s7.cs_next_var), len+1w)) = SOME slot` by
       metis_tac[update_var_def] >>
     simp[update_var_def, FLOOKUP_UPDATE] >>
     simp[sstore_def, tstore_def, LET_THM, lookup_var_def,
          stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality] >>
     rpt strip_tac >> fs[not_fresh_at_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0 /\
   LENGTH code = 2` by
    (qpat_x_assum `code = [_;_]` SUBST1_TAC >>
     Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  qspecl_then [`code`, `s`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- (fs[EVERY_MEM] >> metis_tac[]) >> strip_tac >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 2` >>
  simp[gas_marked_path_def, lookup_var_def,
       stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, lookup_var_def]
QED

Theorem append_copy_prefix_call_ctx[local]:
  !n. (store_copy_prefix loc b k s n).vs_call_ctx = s.vs_call_ctx /\
      (store_copy_prefix loc b k s n).vs_labels = s.vs_labels
Proof
  Induct >> fs[stmtSimStoreCopyTheory.store_copy_prefix_def,
    COUNT_LIST_SNOC, FOLDL_SNOC] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def, LET_THM]
QED

Theorem append_copy_prefix_suc[local]:
  store_copy_prefix loc b k c (SUC n) =
    (if loc = LocStorage then sstore else tstore) (k+n2w n)
      (mload (w2n (b+n2w n*32w)) c) (store_copy_prefix loc b k c n)
Proof
  simp[stmtSimStoreCopyTheory.store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem append_copy_normalize_store[local]:
  store_copy_normalize a ((if tr then tstore else sstore) k v c) =
  (if tr then tstore else sstore) k v (store_copy_normalize a c)
Proof
  Cases_on `tr` >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem append_copy_normalize_nest[local]:
  store_copy_normalize a (store_copy_normalize d c) = store_copy_normalize a c
Proof
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def]
QED

Theorem append_copy_normalize_prefix[local]:
  !n. store_copy_normalize a (store_copy_prefix loc b k c n) =
      store_copy_prefix loc b k (store_copy_normalize a c) n
Proof
  `!p. mload p (store_copy_normalize a c) = mload p c` by
    simp[stmtSimStoreCopyTheory.store_copy_normalize_def, mload_def] >>
  Induct
  >- simp[stmtSimStoreCopyTheory.store_copy_prefix_def, COUNT_LIST_def] >>
  simp[append_copy_prefix_suc] >>
  Cases_on `loc = LocStorage` >>
  fs[SRULE [] (Q.INST [`tr` |-> `T`] append_copy_normalize_store),
     SRULE [] (Q.INST [`tr` |-> `F`] append_copy_normalize_store)]
QED

Theorem append_storage_copy_suffix_path:
  compile_dynarray_append cenv bop vop 1 stride dt st cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  fn_has_code sa sf func /\ cap < dimword (:256) /\ stride < dimword (:256) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME b /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let len = if tr then tload slot s else sload slot s in
  if w2n len < cap then
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      store_copy_normalize s t =
        (if tr then tstore else sstore) slot (len+1w)
          (store_copy_prefix (if tr then LocTransient else LocStorage)
             b (slot+1w+len*n2w stride) s stride)
  else ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [append_storage_copy_suffix_parts]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\
   ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sf` by
    (metis_tac[ci_mono_emit_op, ci_mono_emit_void,
               ci_mono_compile_word_copy_loop, pairTheory.SND]) >>
  `cs_extends sa s6 /\ cs_extends s6 s7 /\ cs_extends s7 sf /\
   sa.cs_next_var <= s6.cs_next_var /\ s6.cs_next_var <= s7.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all append_storage_copy_prefix_path >>
  simp_tac (srw_ss()) [LET_THM] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `w2n len < cap` >>
  reverse IF_CASES_TAC >- metis_tac[] >>
  fs[] >> rename1 `gas_marked_path F ctx func s 0 (OK pre)` >>
  `~pre.vs_call_ctx.cc_static` by
    (qpat_x_assum `store_copy_normalize s pre = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality] >> metis_tac[]) >>
  `!x. vop = Var x \/ pop = Var x ==> not_fresh_at s6 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_store_copy_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspec_then `pre` mp_tac) >>
  simp[] >>
  impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[]) >> strip_tac >>
  rename1 `gas_marked_path F ctx func pre 0 (OK copied)` >>
  fs[stmtSimStoreCopyTheory.store_copy_frame_def] >>
  `copied.vs_call_ctx = pre.vs_call_ctx /\
   copied.vs_labels = pre.vs_labels` by
    (qpat_x_assum `store_copy_normalize pre copied = _` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality, append_copy_prefix_call_ctx]) >>
  `!x. bop = Var x \/ lop = Var x ==> not_fresh_at s7 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `pre.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s pre = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality]) >>
  `!x. bop = Var x ==> not_fresh_at s6 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand bop copied = SOME slot /\ eval_operand lop copied = SOME len` by
    (Cases_on `bop` >> Cases_on `lop` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `~copied.vs_call_ctx.cc_static` by metis_tac[] >>
  drule_all append_storage_copy_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func copied 0 (OK t)` >>
  `store_copy_normalize s copied =
    store_copy_prefix (if tr then LocTransient else LocStorage)
      b (slot+1w+len*n2w stride) s stride` by
    (qpat_x_assum `store_copy_normalize pre copied = _`
       (mp_tac o AP_TERM ``store_copy_normalize s``) >>
     simp[append_copy_normalize_nest, append_copy_normalize_prefix]) >>
  `store_copy_normalize s t =
    (if tr then tstore else sstore) slot (len+1w)
      (store_copy_prefix (if tr then LocTransient else LocStorage)
        b (slot+1w+len*n2w stride) s stride)` by
    (qpat_x_assum `store_copy_normalize copied t = _`
       (mp_tac o AP_TERM ``store_copy_normalize s``) >>
     simp[append_copy_normalize_nest, append_copy_normalize_store]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem append_storage_word_suffix_structure:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  same_blocks sa sf /\ inst_extends sa sf /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode) (emitted_insts sa sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem append_storage_word_code_frame:
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  compile_dynarray_append cenv (Lit slot) op 1 1 elem
    (lowered_value_type cenv e) cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sa sf func ==>
  cs_extends sa sb /\ cs_extends sb sf /\
  fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  strip_tac >>
  `cs_extends sa sb` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  `cs_extends sb sf` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, inst_extends_def]) >>
  metis_tac[fn_has_code_split]
QED

Theorem stmt_state_rel_reserved_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  state_frame t = state_frame s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >> irule stmt_state_rel_operand_frame >>
  qexists_tac `drop_fresh sa s` >> conj_tac
  >- (Cases >> simp[eval_operand_def] >> rpt strip_tac >>
      fs[lookup_var_def, drop_fresh_def, FLOOKUP_DRESTRICT, IN_DEF] >>
      metis_tac[lookup_var_def]) >>
  conj_tac >- asm_simp_tac bool_ss [drop_fresh_def, state_frame_vars] >>
  metis_tac[stmt_state_rel_drop_fresh]
QED

Theorem append_storage_word_frame_fields[local]:
  state_frame u = state_frame
    (if tr then tstore slot h (tstore addr w s)
     else sstore slot h (sstore addr w s)) ==>
  u.vs_current_bb = s.vs_current_bb /\
  u.vs_halted = s.vs_halted /\ u.vs_allocas = s.vs_allocas
Proof
  Cases_on `tr` >>
  simp[state_frame_def, sstore_def, tstore_def, LET_THM,
       venom_state_component_equality]
QED

Theorem append_storage_header_agree[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr)
Proof
  strip_tac >>
  `accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule accounts_rel_storage_transient >>
  disch_then (drule_at Any) >> strip_tac >>
  `storage_read_live cx tr (get_storage cx es tr) slot
     (ArrayTV tv (Dynamic cap))` by
    metis_tac[declared_storage_region_read_live] >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[storage_rel_def, transient_rel_def, get_storage_def, lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by
    simp[type_slot_size_def] >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >> simp[tload_def, sload_def]
QED

Theorem append_storage_word_suffix_open[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) ==>
  ~block_is_terminated sf
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
  Cases_on `sb.cs_current_insts` >>
  simp[block_is_terminated_def, mk_inst_def, is_terminator_def,
       listTheory.LAST_CONS_cond, rich_listTheory.LAST_APPEND_NOT_NIL]
QED

(* ===== Counted source action ===== *)

Theorem get_storage_gas_obs:
  get_storage cx (st with gas_obs := g) b = get_storage cx st b
Proof
  Cases_on `b` >> simp[get_storage_def]
QED

Theorem set_storage_gas_obs:
  set_storage cx (st with gas_obs := g) b x =
  set_storage cx st b x with gas_obs := g
Proof
  Cases_on `b` >> simp[set_storage_def]
QED

(* Appending to a storage array reads no gas. *)
Theorem append_storage_place_gas_obs:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v st =
    (res, st') ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
    (st with gas_obs := g) = (res, st' with gas_obs := g)
Proof
  strip_tac >>
  qpat_x_assum `append_place _ _ _ _ = _` mp_tac >>
  simp[append_place_def, get_storage_backend_eq, bind_def, LET_THM,
       ignore_bind_def, check_def, assert_def, return_def, raise_def,
       write_storage_slot_eq, get_storage_gas_obs] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[get_storage_gas_obs, set_storage_gas_obs, raise_def,
           return_def])
QED

(* A storage root resolves to the same place from every state. *)
Theorem append_toplevel_place_any:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot tv), es) ==>
  !st. eval_target_place cx (TopLevelNameTarget nid) st =
         (INL (StoragePlace tr slot tv), st)
Proof
  PairCases_on `nid` >>
  `!st. eval_target_place cx (TopLevelNameTarget (nid0,nid1)) st =
        bind (lookup_global cx nid0 nid1) get_place st` by
    (gen_tac >> simp[Once evaluate_def] >>
     simp[Once evaluate_def, bind_def]) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  Cases_on `get_module_code cx nid0` >>
  simp[bind_def, lookup_global_def, lift_option_type_def, return_def,
       raise_def, LET_THM] >>
  rename1 `find_var_decl_by_name nid1 ts` >>
  Cases_on `find_var_decl_by_name nid1 ts`
  >- (simp[get_immutables_def, get_address_immutables_def, bind_def,
           lift_option_type_def, return_def, raise_def] >>
      Cases_on `ALOOKUP es.immutables cx.txn.target` >>
      simp[return_def, raise_def] >>
      rename1 `get_source_immutables nid0 imms` >>
      Cases_on `FLOOKUP (get_source_immutables nid0 imms) nid1` >>
      simp[get_place_def, return_def, raise_def]) >>
  rename1 `find_var_decl_by_name nid1 ts = SOME decl` >> PairCases_on `decl` >> Cases_on `decl0` >>
  simp[] >>
  rename1 `lookup_var_slot_from_layout cx istr nid0 decl1` >>
  Cases_on `lookup_var_slot_from_layout cx istr nid0 decl1` >>
  simp[bind_def, get_place_def, return_def, raise_def] >>
  rename1 `evaluate_type (get_tenv cx) vty` >>
  Cases_on `evaluate_type (get_tenv cx) vty` >>
  simp[bind_def, get_place_def, return_def, raise_def]
QED

Theorem eval_append_storage_bind:
  (!st. eval_target_place cx (TopLevelNameTarget nid) st = (INL p, st)) ==>
  eval_stmt cx (Append (TopLevelNameTarget nid) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p)
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw, st1)` >>
  Cases_on `raw` >> simp[] >>
  Cases_on `read_result cx x' st1` >> rename1 `_ = (r2, st2)` >>
  Cases_on `r2` >> simp[]
QED

Theorem append_forced_admissible[local]:
  eval_stmt cx (Append (TopLevelNameTarget nid) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p) /\
  gas_admissible (eval_stmt cx (Append (TopLevelNameTarget nid) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_stmt cx (Append (TopLevelNameTarget nid) e) (es with gas_obs := gs) =
     (INR ex, ee)` by simp[Once bind_def] >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem append_forced_exempt[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
       (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
     (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (append_place cx p v) (return ()))` by
    (simp[ignore_bind_def, FUN_EQ_THM, bind_def] >>
     gen_tac >> Cases_on `eval_expr cx e x` >>
     rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >>
     rename1 `read_result cx v est` >>
     Cases_on `read_result cx v est` >>
     rename1 `read_result cx v est = (forced,forced_es)` >>
     Cases_on `forced` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >> simp[]
QED


(* ===== Counted target suffix ===== *)

Theorem storage_load_drop_fresh[local]:
  tload slot (drop_fresh sb s) = tload slot s /\
  sload slot (drop_fresh sb s) = sload slot s
Proof
  simp[drop_fresh_def, tload_def, sload_def,
       contract_transient_def, contract_storage_def]
QED

Theorem append_storage_word_suffix_no_gas[local]:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

Theorem append_storage_word_suffix_code[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sf) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sb sf) = LENGTH sf.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode)
      (emitted_insts sb sf)
Proof
  strip_tac >>
  drule append_storage_word_suffix_no_gas >> strip_tac >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND] >>
  conj_tac
  >- (qexists_tac `l` >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  fs[EVERY_MEM]
QED

(* From the operand's state, the suffix either aborts on a full array or
   stores the element and the new length, along an actual path with no GAS
   reads. *)
Theorem append_storage_word_suffix_path:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  !ctx.
  (cap <= w2n (if tr then tload slot s else sload slot s) ==>
     ?a t. gas_marked_path F ctx func s 0 (Abort a t)) /\
  (!len. len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
     ?u. gas_marked_path F ctx func s 0
           (OK (u with vs_inst_idx := LENGTH sf.cs_current_insts)) /\
         state_frame u = state_frame
           (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
            else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
         (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
                lookup_var x u = SOME a))
Proof
  strip_tac >> gen_tac >>
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `fresh_vars_wrt sb (drop_fresh sb s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand (Lit slot) (drop_fresh sb s) = SOME slot` by
    simp[eval_operand_def] >>
  `eval_operand op (drop_fresh sb s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  `vars_ext_result (run_inst_seq (emitted_insts sb sf) (drop_fresh sb s))
     (run_inst_seq (emitted_insts sb sf) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM]) >>
  conj_tac
  >- suspend "abort" >>
  suspend "store"
QED

Resume append_storage_word_suffix_path[abort]:
  strip_tac >>
  `cap <= w2n (if tr then tload slot (drop_fresh sb s)
               else sload slot (drop_fresh sb s))` by
    simp[storage_load_drop_fresh] >>
  drule_all compile_dynarray_append_word_abort >> strip_tac >>
  `?a t'. run_inst_seq (emitted_insts sb sf) s = Abort a t'` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >>
     simp[vars_ext_result_def] >> metis_tac[]) >>
  qspecl_then [`emitted_insts sb sf`, `s`, `t'`, `a`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_abort_zero_path >>
  impl_tac >- fs[EVERY_MEM] >>
  metis_tac[]
QED

Resume append_storage_word_suffix_path[store]:
  rpt strip_tac >>
  `len = w2n (if tr then tload slot (drop_fresh sb s)
              else sload slot (drop_fresh sb s))` by
    simp[storage_load_drop_fresh] >>
  `~(drop_fresh sb s).vs_call_ctx.cc_static` by simp[drop_fresh_def] >>
  drule_all compile_dynarray_append_word_run >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sb sf) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >>
     simp[vars_ext_result_def]) >>
  qspecl_then [`emitted_insts sb sf`, `s`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- fs[EVERY_MEM] >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sb sf)) = 0` by
    (simp[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  qexists_tac `u` >> conj_tac
  >- (simp[gas_marked_path_def] >> metis_tac[]) >>
  conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      qpat_x_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
      qpat_x_assum `state_frame t = _` (fn th => pure_once_rewrite_tac [th]) >>
      Cases_on `tr` >>
      simp[drop_fresh_def, sstore_def, tstore_def, LET_THM]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sb s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Finalise append_storage_word_suffix_path[local]

(* The stored state relates to the source after the append. *)
Theorem append_storage_word_success_post[local]:
  !ctx func cenv cx es s u sb tr slot len w mid n tv cap v res es'.
  state_frame u = state_frame
    (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
     else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
  (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
         lookup_var x u = SOME a) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es' u /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
  u.vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  drule append_storage_word_frame_fields >> strip_tac >>
  qmatch_asmsub_abbrev_tac `state_frame u = state_frame su` >>
  drule_all stmt_state_rel_append_storage_word >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' su` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ es' _` mp_tac >>
     simp_tac bool_ss [Abbr `su`, GSYM wordsTheory.word_add_n2w,
                      wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  irule stmt_state_rel_reserved_frame >> qexistsl_tac [`su`, `sb`] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  qpat_x_assum `lookup_var _ su = SOME _` mp_tac >>
  Cases_on `tr` >>
  simp_tac (srw_ss()) [Abbr `su`, sstore_def, tstore_def, LET_THM,
                       lookup_var_def] >>
  strip_tac >>
  qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a`
    (qspec_then `x` mp_tac) >> simp[lookup_var_def]
QED

(* storage.append(e) for a word element: e's fragment, whose errors exit,
   then the bounds check and the two stores, from the readings the actual
   target path selects. *)
Theorem compile_append_storage_word_stmt_frag:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_slot_size tv = 1 /\ cap < dimword (:256) /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]) /\
  expr_sim ctx func cenv cx elem e es ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all append_storage_word_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op,sB)` >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  drule_all append_storage_word_code_frame >> strip_tac >>
  drule append_toplevel_place_any >> strip_tac >>
  drule eval_append_storage_bind >> disch_then (qspec_then `e` assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[append_forced_admissible] >>
  `!x. op = Var x ==> not_fresh_at sB x` by metis_tac[compile_lower_value_var] >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved cenv sB` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  irule append_forced_exempt >> first_assum ACCEPT_TAC
QED

Resume compile_append_storage_word_stmt_frag[summary]:
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "operand" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_append_storage_word_stmt_frag[operand]:
  gvs[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     metis_tac[]) >>
  `(if tr then tload slot t else sload slot t) =
   lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr)` by
    metis_tac[append_storage_header_agree] >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all append_storage_word_suffix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v
              (es_end with gas_obs := [])` >>
  rename1 `_ = (res1, ee1)` >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v
            (es_end with gas_obs := tail) = (res1, ee1 with gas_obs := tail)` by
    (gen_tac >> drule append_storage_place_gas_obs >>
     disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
  `ee1 with gas_obs := [] = ee1` by
    (qpat_assum `!tail. append_place _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     metis_tac[pairTheory.PAIR_EQ]) >>
  Cases_on `w2n (lookup_storage slot
                   (get_storage cx (es_end with gas_obs := []) tr)) < cenv.ce_module_dynarray_capacity nid`
  >- suspend "stored" >>
  suspend "full"
QED

Resume compile_append_storage_word_stmt_frag[full]:
  `cenv.ce_module_dynarray_capacity nid <= w2n (lookup_storage slot
                 (get_storage cx (es_end with gas_obs := []) tr))` by
    decide_tac >>
  `cenv.ce_module_dynarray_capacity nid <= w2n (if tr then tload slot t else sload slot t)` by metis_tac[] >>
  qpat_x_assum `cenv.ce_module_dynarray_capacity nid <= w2n (if _ then _ else _) ==> _` drule >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (Abort a ta)` >>
  `res1 = INR (Error (RuntimeError "append full storage array"))` by
    (drule append_storage_full >>
     disch_then (qspecl_then [`v`, `tv`] mp_tac) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_marked_exec F (ctx,func)
     (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v)
     (es_end with gas_obs := [], t) []
     (INR (Error (RuntimeError "append full storage array"))) ee1 (Abort a ta)` by
    simp[gas_marked_exec_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "append full storage array"))`, `ee1`,
                `Abort a ta`] >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def] >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[]
QED

Resume compile_append_storage_word_stmt_frag[stored]:
  qpat_x_assum `!len. _`
    (qspec_then `w2n (lookup_storage slot
                        (get_storage cx (es_end with gas_obs := []) tr))` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es_end with gas_obs := []`, `t`,
               `u`, `sB`, `tr`, `slot`,
               `w2n (lookup_storage slot
                       (get_storage cx (es_end with gas_obs := []) tr))`,
               `typed_val_to_w256 etv v`, `mid`, `n`, `tv`, `cenv.ce_module_dynarray_capacity nid`, `v`,
               `res1`, `ee1`]
    mp_tac append_storage_word_success_post >>
  impl_tac
  >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  strip_tac >>
  `gas_marked_exec F (ctx,func)
     (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v)
     (es_end with gas_obs := [], t) [] res1 ee1
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    simp[gas_marked_exec_def] >>
  qexistsl_tac [`res1`, `ee1`,
                `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
  disj1_tac >> simp[] >>
  `sb.cs_current_bb = sB.cs_current_bb` by
    (drule append_storage_word_suffix_structure >> simp[same_blocks_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w` by
    (rpt strip_tac >> simp[lookup_var_def] >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
     `lookup_var x u = SOME w` by metis_tac[] >>
     fs[lookup_var_def]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by
    (rpt strip_tac >> qpat_x_assum `u.vs_allocas = _` SUBST1_TAC >>
     qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `u.vs_memory = t.vs_memory` by
    (qpat_x_assum `state_frame u = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `tr` >> simp[state_frame_def, sstore_def, tstore_def,
       LET_THM, venom_state_component_equality]) >>
  `MAP FDOM es_end.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `gas_marked_exec F (ctx,func) _ (es,s0) _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM ee1.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `append_place _ _ _ (es_end with gas_obs := []) = _`
       (assume_tac o MATCH_MP vyperScopePreservationTheory.append_place_scopes_dom) >>
     fs[]) >>
  `!aid off sz.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
     mem_bytes_at off sz (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory =
     mem_bytes_at off sz s0.vs_memory` by
    (rpt strip_tac >> simp[] >> qpat_x_assum `u.vs_memory = _` SUBST1_TAC >>
     qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _`
       (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
         rpt strip_tac >>
         qpat_x_assum `!n b sz'. local_region cenv es.scopes s0 _ _ _ ==> _` irule >>
         qpat_assum `local_region cenv es.scopes s0 _ _ _` (irule_at Any)) >>
     disch_then ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv ee1
     (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (mp_tac (Q.INST [`es'` |-> `ee1`,
                     `s` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
               (SPEC_ALL alloca_frame_of_mem_frame)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  simp[stmt_post_def, stmt_lands_def, stmt_state_rel_inst_idx] >>
  simp[cenv_top_ext_refl] >>
  metis_tac[append_storage_word_suffix_open]
QED

Finalise compile_append_storage_word_stmt_frag

Theorem append_storage_copy_success_post:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' name' subs' slot' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
      (w2n slot') (type_slot_size tv')) /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ val_in_memory tv v (w2n b) s.vs_memory /\
  w2n b + 32 * type_slot_size tv <= dimword (:256) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  store_copy_normalize s u =
    (if tr then tstore else sstore) slot (n2w (len+1))
      (store_copy_prefix (if tr then LocTransient else LocStorage)
        b (slot+n2w (1+len*type_slot_size tv)) s (type_slot_size tv)) /\
  (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es' u
Proof
  strip_tac >>
  drule stmtSimStoreCopyStateTheory.stmt_state_selected_storage_agree >>
  disch_then (qspec_then `tr` assume_tac) >>
  drule_at (Pat `storage_agree _ _ _`)
    (Q.INST [`k` |-> `slot+n2w (1+len*type_slot_size tv)`]
      append_storage_agree_copy) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_at (Pat `storage_agree _ _ _`)
    stmtSimStoreCopyStateTheory.stmt_state_storage_patch >>
  disch_then drule >> strip_tac >>
  drule stmtSimStoreCopyStateTheory.place_store_prefix_backend_natural >>
  disch_then (qspecl_then [`s`, `slot+n2w (1+len*type_slot_size tv)`, `tr`] assume_tac) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `append_place _ _ _ _ = _` mp_tac >>
  simp[append_storage_writes, ignore_bind_def, bind_def,
       write_storage_slot_eq, get_storage_after_set, encode_value_def,
       encode_base_to_slot_def, integer_wordTheory.i2w_def, apply_writes_def] >>
  strip_tac >> gvs[] >>
  irule place_store_normalize_state >> qexistsl_tac [`s`, `sb`] >> simp[] >>
  qpat_x_assum `store_copy_normalize s u = _` SUBST1_TAC >>
  `!st1 st2. set_storage cx (set_storage cx es tr st1) tr st2 =
    set_storage cx es tr st2` by
    (Cases_on `tr` >> simp[set_storage_def, update_account_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM]) >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[stmtSimStoreCopyStateTheory.place_store_prefix_state_patch] >>
  Cases_on `tr` >>
  gvs[sstore_def, tstore_def, LET_THM, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def,
      combinTheory.APPLY_UPDATE_THM]
QED


Theorem compile_append_storage_aggregate_stmt_frag:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  lowered_value_type cenv e = elem /\ post_value_type cenv e = elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  0 < type_slot_size tv /\
  type_memory_bytes cenv elem = 32 * type_slot_size tv /\
  type_memory_bytes cenv elem < dimword (:256) /\ cap < dimword (:256) /\
  (!gs v ee.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
    value_has_type tv v /\ val_wf tv v /\ val_footprint tv v <= type_memory_bytes cenv elem) /\
  (!ee s u sb b len v res ee'.
    stmt_state_rel ctx func cenv cx ee s /\ local_ptrs_reserved cenv sb /\
    value_has_type tv v /\ val_in_memory tv v (w2n b) s.vs_memory /\
    w2n b + 32 * type_slot_size tv <= dimword (:256) /\
    len = w2n (lookup_storage slot (get_storage cx ee tr)) /\ len < cap /\
    store_copy_normalize s u =
      (if tr then tstore else sstore) slot (n2w (len+1))
        (store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+n2w (1+len*type_slot_size tv)) s (type_slot_size tv)) /\
    (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
    append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v ee = (res,ee') ==>
    res = INL () /\ stmt_state_rel ctx func cenv cx ee' u) /\
  expr_sim ctx func cenv cx elem e es ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  strip_tac >> simp[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all append_storage_copy_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (raw,sB)` >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sc` by metis_tac[compile_alloc_buffer_extends] >>
  `compile_copy_memory tmp.buf_operand raw (type_memory_bytes cenv elem) sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `cs_extends sc sd` by
    (drule compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sd sb` by metis_tac[compile_dynarray_append_labels, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sd func /\ fn_has_code sd sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule append_toplevel_place_any >> strip_tac >>
  drule eval_append_storage_bind >> disch_then (qspec_then `e` assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[append_forced_admissible] >>
  `!x. raw = Var x ==> not_fresh_at sB x` by metis_tac[compile_lower_value_var] >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved cenv sB` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sB`, `raw`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  irule append_forced_exempt >> first_assum ACCEPT_TAC
QED

Resume compile_append_storage_aggregate_stmt_frag[summary]:
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "operand" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_append_storage_aggregate_stmt_frag[operand]:
  gvs[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `?sw. eval_operand raw t = SOME sw /\ val_in_memory tv v (w2n sw) t.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `value_has_type tv v /\ val_wf tv v /\ val_footprint tv v <= 32 * type_slot_size tv` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     qpat_x_assum `!gs v ee. bind (eval_expr cx e) (read_result cx) _ = _ ==> _` drule >> simp[]) >>
  drule append_storage_aggregate_staging_bounded_path >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (OK staged)` >>
  `(if tr then tload slot staged else sload slot staged) =
   lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr)` by
    (irule append_storage_header_agree >>
     metis_tac[]) >>
  `~staged.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    append_storage_copy_suffix_path >>
  disch_then (drule_at (Pat `fn_has_code sd sb func`)) >>
  disch_then (qspecl_then [`slot`, `staged`, `ctx`, `w`] mp_tac) >>
  simp[eval_operand_def, LET_THM] >>
  Cases_on `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v (es_end with gas_obs := [])` >>
  rename1 `_ = (res1,ee1)` >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v (es_end with gas_obs := tail) = (res1,ee1 with gas_obs := tail)` by
    (gen_tac >> drule append_storage_place_gas_obs >>
     disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
  `ee1 with gas_obs := [] = ee1` by
    (qpat_assum `!tail. append_place _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> metis_tac[pairTheory.PAIR_EQ]) >>
  Cases_on `w2n (lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr)) < cenv.ce_module_dynarray_capacity nid`
  >- suspend "stored" >>
  suspend "full"
QED

Resume compile_append_storage_aggregate_stmt_frag[stored]:
  simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func staged 0 (OK fin)` >>
  `store_copy_normalize staged fin =
    (if tr then tstore else sstore) slot
      (n2w (w2n (lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr))+1))
      (store_copy_prefix (if tr then LocTransient else LocStorage) w
        (slot+n2w (1+w2n (lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr))*type_slot_size tv)) staged (type_slot_size tv))` by
    (simp[GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
          wordsTheory.WORD_ADD_ASSOC]) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sB` >>
     simp[] >>
     `ci_mono sB sc /\ ci_mono sc sd` by
       metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  qpat_x_assum `!ee s u sb' b v' res ee'. _` drule >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspecl_then [`fin`, `sd`, `res1`, `ee1`] mp_tac) >>
  impl_tac
  >- (asm_simp_tac bool_ss [arithmeticTheory.MULT_COMM] >> simp[]) >>
  strip_tac >>
  `gas_marked_path F ctx func t 0 (OK fin)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `gas_marked_exec F (ctx,func)
     (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v)
     (es_end with gas_obs := [],t) [] res1 ee1 (OK fin)` by
    simp[gas_marked_exec_def] >>
  qexistsl_tac [`res1`, `ee1`, `OK fin`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
  disj1_tac >> simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      rewrite_tac[append_storage_copy_suffix_parts] >> strip_tac >>
      drule exprOpenPrimitivesTheory.emit_void_terminated >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sB x /\ not_fresh_at sd x` by
        ( `ci_mono sB sc /\ ci_mono sc sd` by
            metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
          fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
      metis_tac[]) >>
  `!i loc b k base. (store_copy_prefix loc b k base i).vs_allocas = base.vs_allocas` by
    (Induct >- simp[stmtSimStoreCopyTheory.store_copy_prefix_def, COUNT_LIST_SNOC] >>
     rpt gen_tac >>
     pure_rewrite_tac[stmtSimStoreCopyTheory.store_copy_prefix_def,
                      COUNT_LIST_SNOC, FOLDL_SNOC] >>
     rewrite_tac[GSYM stmtSimStoreCopyTheory.store_copy_prefix_def] >>
     Cases_on `loc = LocStorage` >> simp[sstore_def, tstore_def, LET_THM]) >>
  `fin.vs_allocas = staged.vs_allocas` by
    (qpat_x_assum `store_copy_normalize staged fin = _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_allocas``) >>
     simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >> Cases_on `tr` >>
     simp[sstore_def, tstore_def, LET_THM]) >>
  metis_tac[]
QED

Resume compile_append_storage_aggregate_stmt_frag[full]:
  simp[] >> strip_tac >>
  `cenv.ce_module_dynarray_capacity nid <= w2n (lookup_storage slot (get_storage cx (es_end with gas_obs := []) tr))` by decide_tac >>
  rename1 `gas_marked_path F ctx func staged 0 (Abort Revert_abort fin)` >>
  `gas_marked_path F ctx func t 0 (Abort Revert_abort fin)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `res1 = INR (Error (RuntimeError "append full storage array"))` by
    (drule append_storage_full >>
     disch_then (qspecl_then [`v`, `tv`] mp_tac) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_marked_exec F (ctx,func)
     (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic (cenv.ce_module_dynarray_capacity nid)))) v)
     (es_end with gas_obs := [],t) []
     (INR (Error (RuntimeError "append full storage array"))) ee1 (Abort Revert_abort fin)` by
    simp[gas_marked_exec_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "append full storage array"))`, `ee1`, `Abort Revert_abort fin`] >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def] >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[]
QED

Finalise compile_append_storage_aggregate_stmt_frag
