(* Counted one-word storage copy at its concrete endpoint. *)
Theory bodyIntCallStorageWord
Ancestors
  storageCopyGasPath exprSimCopy exprSimStorageCopy exprLoweringProps
  stmtReasonLitFragMemory fragExec venomExecSemantics venomState venomInst
  context compileEnv words finite_map rich_list loweringSlice
Libs
  monadsyntax

Theorem storage_copy_word_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst;v] od sa = (r,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME (n2w b) /\
  b + 32 < 2**256 /\ ~u.vs_halted /\
  u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    copy_prefix loc a b 1 u 1 z /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[prefix_drop_equiv, emitted_insts_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [mk_inst _ _ _ [x]; _]` >>
  qabbrev_tac `w = copy_runtime_word loc u a` >>
  qabbrev_tac `t = mstore b w (update_var x w u)` >>
  `eval_operand dst (update_var x w u) = SOME (n2w b)` by
    (Cases_on `dst` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) u = OK t` by
    (Cases_on `loc = LocStorage` >>
     gvs[run_inst_seq_def, step_inst_base_def, exec_read1_def,
         exec_write2_def, mk_inst_def, Abbr `t`, Abbr `w`,
         copy_runtime_word_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE, w2n_n2w, dimword_def]) >>
  `gas_marked_path F ctx func u 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.SPECL [`emitted_insts sa sb`, `u`, `t`, `F`, `ctx`, `func`, `bb`]
      storage_copy_seq_path) >>
     simp[mk_inst_def, is_terminator_def] >>
     impl_tac >- (qpat_x_assum `isPREFIX _ _` mp_tac >>
       simp[mk_inst_def, is_terminator_def]) >> simp[]) >>
  `copy_prefix loc a b 1 u 0 (update_var x w u)` by
    simp[copy_prefix_update_var, copy_prefix_zero] >>
  drule copy_prefix_extend >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[Abbr `t`, Abbr `w`, copy_prefix_idx, WORD_ADD_0] >>
  conj_tac >- simp[venomMemPropsTheory.LENGTH_mstore_eq, update_var_def] >>
  simp[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* The typed consumer uses the very endpoint of the two-instruction path. *)
Theorem storage_copy_word_owned_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst;v] od sa = (r,sb) /\
  type_slot_size tv = 1 /\ fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME (n2w b) /\
  type_slot_size tv < 2**256 /\ b + 32 * type_slot_size tv < 2**256 /\
  ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es u /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ type_memory_size tv <= sz ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
      copy_prefix loc a b (type_slot_size tv) u (type_slot_size tv) z /\
      LENGTH u.vs_memory <= LENGTH z.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_static z = copy_static u /\
      FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
      val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
      val_footprint tv v <= type_memory_size tv /\
      eval_operand dst z = SOME (n2w b)
Proof
  strip_tac >>
  `b + 32 < 2**256` by gvs[] >>
  `?z. gas_marked_path F ctx func u 0 (OK z) /\
       copy_prefix loc a b 1 u 1 z /\
       LENGTH u.vs_memory <= LENGTH z.vs_memory /\
       (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule storage_copy_word_path >> metis_tac[]) >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `z.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
  `eval_operand dst z = eval_operand dst u` by
    (irule storage_copy_operand_preserved >> metis_tac[]) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
      a b (type_slot_size tv) u (type_slot_size tv) z` by gvs[] >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  qexists_tac `z` >> gvs[]
QED
