(* Counted paths for aggregate storage Append. *)
Theory bodyMemAppendAggregatePath
Ancestors
  bodyMemAssignTopCopyPaths placeStoreCopyPath bodyMemAppendFacts
  exprLowering emitHelper emitHelperProps compileEnv
  fragGasMode fragGasPathMem fragExecMem venomState venomInst venomExecSemantics
  words list rich_list pair fragExec exprSimStorageCopy stmtSimAppendStorage
  stmtSimAppendStorageCompose
  loweringStateRelDefs stateFrame exprLoweringProps varsExt freshWrites
  appendStorageStageTransportPtr bodyDeclMemoryCounted instMemFrontier memSafeRun

Theorem append_storage_aggregate_address_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit (n2w n)] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  fresh_vars_wrt st3 ss ==>
  ?t. run_inst_seq (emitted_insts st3 st6) ss = OK t /\
    eval_operand pop t = SOME (slot + 1w + len * n2w n) /\
    same_blocks st3 st6 /\ fresh_vars_wrt st6 t /\
    state_frame t = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) ss = SOME 1w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) ss = OK ss4` >>
  `eval_operand lop ss4 = SOME len /\
   eval_operand (Lit (n2w n)) ss4 = SOME (n2w n)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) ss4 = OK ss5` >>
  `eval_operand dop ss5 = SOME (slot + 1w)` by metis_tac[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st5) ss = OK ss5` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) ss = OK ss'` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss5`, `st5`] >> simp[]) >>
  `state_frame ss' = state_frame ss` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st3 st6` >> simp[] >>
     `emitted_insts st3 st6 = emitted_insts st3 st4 ++
       emitted_insts st4 st5 ++ emitted_insts st5 st6` by
       metis_tac[inst_extends_trans, inst_extends_def, emitted_insts_append] >>
     imp_res_tac emitted_insts_emit_op >>
     simp[EVERY_APPEND, mk_inst_def]) >>
  gvs[same_blocks_def] >> metis_tac[]
QED

Theorem append_storage_aggregate_prefix_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt sa s /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
  ?t. run_inst_seq (emitted_insts sa s6) s = OK t /\
    eval_operand dst t = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop t = SOME (n2w len) /\
    same_blocks sa s6 /\ fresh_vars_wrt s6 t /\
    state_frame t = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `w2n (if tr then tload slot s else sload slot s) < cap` by metis_tac[] >>
  drule_all append_storage_guard_run >> strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  `eval_operand bop ss' = SOME slot` by metis_tac[] >>
  drule_all append_storage_aggregate_address_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa s3 /\ inst_extends s3 s6` by
    metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s6) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss'`, `s3`] >> simp[]) >>
  qexists_tac `t` >> gvs[same_blocks_def] >> metis_tac[n2w_w2n]
QED

Theorem append_storage_aggregate_prefix_layout:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) ==>
  same_blocks sa s6 /\ inst_extends sa s6 /\
  (!x. not_fresh_at sa x ==> not_fresh_at s6 x) /\
  (!x. dst = Var x \/ lop = Var x ==> not_fresh_at s6 x) /\
  EVERY (\i. MEM i.inst_opcode [SLOAD; TLOAD; LT; ASSERT; ADD; MUL])
    (emitted_insts sa s6)
Proof
  simp[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def,
       DROP_LENGTH_APPEND, mk_inst_def, Excl "isPREFIX"] >>
  Cases_on `tr` >> simp[not_fresh_at_def, Excl "isPREFIX"] >>
  rpt strip_tac >> gvs[fresh_var_distinct] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem append_storage_aggregate_prefix_run_unpruned:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
  ?u. run_inst_seq (emitted_insts sa s6) s = OK u /\
    eval_operand dst u = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop u = SOME (n2w len) /\ state_frame u = state_frame s /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x u = SOME a)
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by simp[eval_operand_drop_fresh] >>
  `len = w2n (if tr then tload slot (drop_fresh sa s)
             else sload slot (drop_fresh sa s))` by
    simp[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  drule_all append_storage_aggregate_prefix_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa s6) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa s6) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?u. run_inst_seq (emitted_insts sa s6) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >> asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa s6) s` >> simp[vars_ext_result_def]) >>
  qexists_tac `u` >> asm_rewrite_tac [] >>
  conj_tac >- metis_tac[vars_ext_eval_operand] >>
  conj_tac >- metis_tac[vars_ext_eval_operand] >>
  conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      gvs[drop_fresh_def, state_frame_vars]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  `eval_operand (Var x) u = SOME a` by metis_tac[vars_ext_eval_operand] >>
  fs[eval_operand_def]
QED

Theorem append_storage_aggregate_prefix_path:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  fn_has_code sa s6 func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand dst t = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop t = SOME (n2w len) /\
    state_frame t = state_frame (s with vs_inst_idx := LENGTH s6.cs_current_insts) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  drule_all append_storage_aggregate_prefix_run_unpruned >> strip_tac >>
  `s6.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa s6` by
    fs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa s6)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa s6) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >>
     simp[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH s6.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH s6.cs_current_insts` >>
  gvs[gas_marked_path_def, same_blocks_def, state_frame_def,
      eval_operand_def, lookup_var_def]
QED

Theorem append_storage_aggregate_code_bounds:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  compile_word_copy_loop vop dst n LocMemory
    (if tr then LocTransient else LocStorage) F s6 = (u,s7) /\
  emit_op ADD [lop; Lit 1w] s7 = (fresh,s8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s8 = ((),sf) /\
  fn_has_code sa sf func ==>
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\
  fn_has_code s7 sf func /\
  (!x. not_fresh_at sa x ==> not_fresh_at s6 x) /\
  (!x. dst = Var x \/ lop = Var x ==> not_fresh_at s6 x) /\
  (!x. not_fresh_at s6 x ==> not_fresh_at s7 x)
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `cs_extends sa s6` by
    (fs[same_blocks_def, inst_extends_def] >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
  `ci_mono s6 s7` by metis_tac[ci_mono_compile_word_copy_loop, SND] >>
  `ci_mono s7 s8` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono s8 sf` by metis_tac[ci_mono_emit_void, SND] >>
  `cs_extends s6 s7 /\ cs_extends s7 sf` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `cs_extends sa s7` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s7 func /\ fn_has_code s7 sf func` by
    metis_tac[fn_has_code_split] >>
  simp[] >> conj_tac >- metis_tac[fn_has_code_split] >>
  conj_tac >- metis_tac[fn_has_code_split] >>
  conj_tac >- asm_rewrite_tac [] >>
  fs[ci_mono_def] >> simp[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. s6.cs_next_var <= n ==> _` irule >> decide_tac
QED

Theorem append_storage_aggregate_header_run:
  emit_op ADD [lop; Lit 1w] sa = (fresh,s1) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s1 = ((),sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME len /\
  ~s.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    state_frame t = state_frame
      (if tr then tstore slot (len+1w) s else sstore slot (len+1w) s) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    same_blocks sa sb /\ inst_extends sa sb /\
    EVERY (\i. MEM i.inst_opcode [ADD;SSTORE;TSTORE]) (emitted_insts sa sb)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    simp[not_fresh_at_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `same_blocks sa sb` by
    (imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     fs[same_blocks_def]) >>
  qmatch_asmsub_abbrev_tac `fresh = Var v` >>
  `!x. not_fresh_at sa x ==> x <> v` by metis_tac[Abbr `v`] >>
  `eval_operand bop (update_var v (len+1w) s) = SOME slot` by
    (Cases_on `bop` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [lop;Lit 1w] [v]) s =
    OK (update_var v (len+1w) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  qexists_tac `if tr then tstore slot (len+1w) (update_var v (len+1w) s)
              else sstore slot (len+1w) (update_var v (len+1w) s)` >>
  conj_tac
  >- (asm_rewrite_tac [] >> pure_rewrite_tac [APPEND] >>
      rewrite_tac[run_inst_seq_def] >>
      asm_rewrite_tac [] >> Cases_on `tr` >>
      simp[stepInstBaseLib.simp_opcode_clause ``SSTORE``,
           stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def,
           exec_write2_def, eval_operand_update_var] >>
      gvs[update_var_def]) >>
  Cases_on `tr` >>
  simp[state_frame_def, tstore_def, sstore_def, update_var_def, mk_inst_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem append_storage_aggregate_header_path:
  emit_op ADD [lop; Lit 1w] sa = (fresh,s1) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s1 = ((),sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME len /\
  ~s.vs_call_ctx.cc_static /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    state_frame t = state_frame
      ((if tr then tstore slot (len+1w) s else sstore slot (len+1w) s)
       with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted
Proof
  strip_tac >> drule_all append_storage_aggregate_header_run >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> i.inst_opcode = ADD \/ _` drule >>
     simp[] >> strip_tac >>
     gvs[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `tr` >>
  gvs[gas_marked_path_def, same_blocks_def, state_frame_def,
      sstore_def, tstore_def, lookup_var_def]
QED

Theorem append_storage_aggregate_success_path:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME b /\
  cap < dimword (:256) /\ n < dimword (:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  fn_has_code sa sf func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      (if tr then tstore else sstore) slot (n2w len+1w)
        (store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) s n) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    ~t.vs_halted
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  drule_all append_storage_aggregate_code_bounds >> strip_tac >>
  `!x. bop = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all append_storage_aggregate_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path T ctx func s 0 (OK r)` >>
  `r.vs_alloca_next = s.vs_alloca_next /\ r.vs_call_ctx = s.vs_call_ctx` by
    fs[state_frame_def] >>
  `eval_operand bop r = SOME slot /\ eval_operand vop r = SOME b` by
    (Cases_on `bop` >> Cases_on `vop` >>
     gvs[eval_operand_def, state_frame_def] >> metis_tac[]) >>
  `!x. vop = Var x \/ dst = Var x ==> not_fresh_at s6 x` by metis_tac[] >>
  `?q. gas_marked_path T ctx func r 0 (OK q) /\
    store_copy_frame s6 (if tr then LocTransient else LocStorage)
      b (slot+1w+n2w len*n2w n) r n q /\ ~q.vs_halted /\
    q.vs_current_bb = s7.cs_current_bb /\ q.vs_inst_idx = LENGTH s7.cs_current_insts` by
    (irule topcopy_compile_loop_path >> simp[] >>
     reverse conj_tac >- (Cases_on `tr` >> simp[]) >>
     qexistsl_tac [`dst`, `vop`, `u`] >> asm_rewrite_tac [] >> simp[]) >>
  `eval_operand bop q = SOME slot /\ eval_operand len' q = SOME (n2w len)` by
    (conj_tac >> irule topcopy_frame_operand >> metis_tac[]) >>
  `!x. bop = Var x ==> not_fresh_at s7 x` by metis_tac[] >>
  `~q.vs_call_ctx.cc_static` by metis_tac[topcopy_frame_call_ctx] >>
  drule_all append_storage_aggregate_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "post"
QED

Resume append_storage_aggregate_success_path[post]:
  qexists_tac `t` >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `q` >> simp[]) >>
  reverse conj_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
      simp[stmtSimStoreCopyTheory.store_copy_frame_def] >> metis_tac[]) >>
  suspend "normalize"
QED

Resume append_storage_aggregate_success_path[normalize]:
  `r.vs_memory = s.vs_memory /\ store_copy_normalize s r = s` by
    (qpat_x_assum `state_frame r = _` mp_tac >>
     simp[state_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     rpt strip_tac >> simp[venom_state_component_equality]) >>
  `!i. store_copy_normalize s
       (store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) r i) =
       store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) s i` by
    (Cases_on `tr` >> simp[] >> Induct >>
     simp[topcopy_prefix_suc,
       SRULE [] (Q.INST [`loc` |-> `LocStorage`] topcopy_normalize_store),
       SRULE [] (Q.INST [`loc` |-> `LocTransient`] topcopy_normalize_store),
       mload_def]) >>
  `store_copy_normalize s q =
    store_copy_prefix (if tr then LocTransient else LocStorage)
      b (slot+1w+n2w len*n2w n) s n` by
    (qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_frame_def] >> strip_tac >>
     qpat_x_assum `store_copy_normalize r q = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     first_x_assum (qspec_then `n` mp_tac) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     metis_tac[]) >>
  qpat_x_assum `state_frame t = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
  simp[state_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  strip_tac >> asm_rewrite_tac [] >>
  Cases_on `tr` >>
  qpat_x_assum `store_copy_normalize s q = _` mp_tac >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality,
       sstore_def, tstore_def] >> rpt strip_tac >> simp[]
QED

Finalise append_storage_aggregate_success_path


Theorem append_storage_aggregate_abort_path:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot s else sload slot s) /\
  fn_has_code sa sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?a t. gas_marked_path T ctx func s 0 (Abort a t)
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  drule_all append_storage_aggregate_code_bounds >> strip_tac >>
  drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by simp[eval_operand_drop_fresh] >>
  drule_all append_storage_guard_run >> strip_tac >>
  `~(w2n (if tr then tload slot (drop_fresh sa s)
           else sload slot (drop_fresh sa s)) < cap)` by
    (simp[drop_fresh_def, tload_def, sload_def, contract_transient_def, contract_storage_def] >>
     qpat_x_assum `cap <= _` mp_tac >>
     simp[tload_def, sload_def, contract_transient_def, contract_storage_def]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac [] >> strip_tac >>
  suspend "abort_run"
QED

Resume append_storage_aggregate_abort_path[abort_run]:
  `inst_extends sa s3 /\ inst_extends s3 s6` by
    (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `run_inst_seq (emitted_insts sa s6) (drop_fresh sa s) =
    Abort Revert_abort (revert_state (set_returndata [] ss'))` by
    (`emitted_insts sa s6 = emitted_insts sa s3 ++ emitted_insts s3 s6` by
       metis_tac[emitted_insts_append, inst_extends_def] >>
     asm_rewrite_tac [] >>
     irule EQ_TRANS >> qexists_tac `run_inst_seq (emitted_insts sa s3) (drop_fresh sa s)` >>
     conj_tac >- (irule run_inst_seq_append_err >> simp[]) >> simp[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa s6) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa s6) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >> gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?a t. run_inst_seq (emitted_insts sa s6) s = Abort a t` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >> asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa s6) s` >> simp[vars_ext_result_def]) >>
  suspend "path"
QED

Resume append_storage_aggregate_abort_path[path]:
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa s6)` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[EVERY_MEM] >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >>
     simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa s6) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     simp[] >> strip_tac >> gvs[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa s6 ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa s6) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all bodyUnopFragMemoryTheory.run_inst_seq_abort_zero_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Finalise append_storage_aggregate_abort_path


Theorem append_storage_aggregate_suffix_mem:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  fn_has_code sa sf func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (cap <= w2n (if tr then tload slot s else sload slot s) ==>
    ?a t. gas_marked_path T ctx func s 0 (Abort a t)) /\
  (!b len. eval_operand vop s = SOME b /\ n < dimword (:256) /\
    w2n b + 32*n <= s.vs_alloca_next /\
    len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        (if tr then tstore else sstore) slot (n2w len+1w)
          (store_copy_prefix (if tr then LocTransient else LocStorage)
            b (slot+1w+n2w len*n2w n) s n) /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      ~t.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >> conj_tac
  >- (strip_tac >>
      `!x. bop = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      drule_all append_storage_aggregate_abort_path >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all append_storage_aggregate_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac [] >>
  `!i. (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_memory = s.vs_memory /\
         (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_allocas = s.vs_allocas /\
         (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `tr` >> Induct >> gvs[topcopy_prefix_suc, sstore_def, tstore_def]) >>
  qpat_x_assum `store_copy_normalize s t = _`
    (mp_tac o Q.AP_TERM `\q. (q.vs_memory,q.vs_allocas,q.vs_alloca_next)`) >>
  Cases_on `tr` >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def]
QED
