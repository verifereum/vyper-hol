Theory assignEffectfulIndexStorageCompositeFrame
Ancestors
  exprSimUnwrap exprSimCopy exprSimStorageCopy storageCopyGasPath
  placeStoreStorage placeMemoryStaging exprSimAlloc exprLoweringProps
  stmtSimDefs exprLowering context compileEnv loweringPosts
  freshWrites emitHelper emitHelperProps venomState venomInst
  venomExecSemantics fragGasMode fragGasPath fragExec
  immutableMemoryFrame valueEncodingProps
Libs
  monadsyntax

(* The optimized one-slot suffix needs the same content/frame interface as
   the general storage-copy loop. *)
Theorem snapshot_storage_word_run[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_prefix loc a b 1 s 1 t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `step_inst_base (mk_inst sa.cs_next_id
    (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
    OK (update_var v w s)` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         Abbr `w`, copy_runtime_word_def]) >>
  `eval_operand dst (update_var v w s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (gvs[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [dst; Var v] [])
    (update_var v w s) = OK (mstore b w (update_var v w s))` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_update_var]) >>
  qexists_tac `mstore b w (update_var v w s)` >>
  simp[run_inst_seq_def, GSYM mk_inst_def] >> conj_tac
  >- (`copy_prefix loc a b 1 s (0+1)
        (mstore (b+32*0) (copy_runtime_word loc s (a+n2w 0))
          (update_var v w s))` by
        (irule copy_prefix_extend >> simp[copy_prefix_update_var, copy_prefix_zero]) >>
      gvs[Abbr `w`, Abbr `v`, wordsTheory.WORD_ADD_0]) >>
  simp[immutable_mstore_capacity, update_var_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem snapshot_storage_word_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all snapshot_storage_word_run >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
         rich_listTheory.DROP_LENGTH_APPEND]) >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >>
     simp[mk_inst_def, is_terminator_def] >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx, lookup_var_def]
QED

Theorem snapshot_storage_suffix_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (fs[] >> irule snapshot_storage_word_content_path >> simp[] >>
      qexistsl_tac [`dst`, `src`] >> gvs[] >> metis_tac[]) >>
  fs[] >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (compile_storage_copy_content_capacity_path
    |> Q.SPEC `F`
    |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
    |> Q.SPEC `(ctx,func)`) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem snapshot_storage_suffix_value_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\ n = type_slot_size tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  n < 2**256 /\ w2n w + 32*n < 2**256 /\ fn_has_code mid sb func /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand dst u = SOME (n2w (w2n w))` by simp[] >>
  drule_all snapshot_storage_suffix_content_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a (w2n w) (type_slot_size tv) u (type_slot_size tv) z` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `eval_operand dst z = SOME w` by
    (drule storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >> simp[]) >>
  qexists_tac `z` >>
  gvs[copy_prefix_def, type_memory_size_slots] >> metis_tac[]
QED
