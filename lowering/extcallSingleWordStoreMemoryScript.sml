(* Actual ADD and MSTORE for a positional word snapshot. *)
Theory extcallSingleWordStoreMemory
Ancestors
  extcallStoreStagesMemory extcallWordStoreMemory extcallCalldataOpsMemory
  exprSimMapKey bodyFieldMemoryProps exprSimCopy exprSimBufferStore
  exprSimVVFrame exprLoweringProps emitHelperProps freshWrites
  loweringPosts loweringStateRelDefs exprLowering compileEnv context
  fragGasPathMem fragExec venomState exprBopSimProps words instIdxIndep

Theorem extcall_single_word_store_mem:
  compile_extcall_store_values ce [(StackValue tag op,ty)] buf off sa = ((),sb) /\
  is_word_type ty /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ abi_tuple_word tv v /\
  b+off+32 < dimword (:256) /\ b+off+32 <= s.vs_alloca_next /\
  (!x. op = Var x \/ buf = Var x ==> not_fresh_at sa x) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= b+off \/ b+off+32 <= a) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) 32) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (b+off) z.vs_memory /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!a k. a+k <= b+off \/ b+off+32 <= a ==>
      mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule_all extcall_single_store_stages >> strip_tac >>
  `src = op /\ su = sm` by gvs[unwrap_value_def,comp_return_def] >> gvs[] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all emit_ADD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all attr_add_history >> strip_tac >>
  drule_all attr_add_gas_path >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `gas_path_mem ctx func s 0 (OK u)` by metis_tac[] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   t.vs_data_section = s.vs_data_section /\
   t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
     simp[contract_storage_def,contract_transient_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl_tac [`0`,`0`,`sa`] >> simp[regions_disjoint_def] >>
     qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
   u.vs_data_section = s.vs_data_section /\ ~u.vs_halted /\
   u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s /\
   stmt_state_rel ctx func ce cx es u` by
    (simp[Abbr `u`,stmt_state_rel_inst_idx,contract_storage_def,contract_transient_def] >>
     fs[contract_storage_def,contract_transient_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`,lookup_var_def] >> fs[lookup_var_def]) >>
  `eval_operand op u = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand dst u = SOME (n2w (b+off))` by
    simp[Abbr `u`,eval_op_inst_idx,word_add_n2w] >>
  `b+off < dimword (:256)` by decide_tac >>
  `local_ptrs_reserved ce sm` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!name a n. local_region ce es.scopes u name a n ==>
    a+n <= b+off \/ b+off+32 <= a` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name a n` by
       metis_tac[copy_buffer_local_region_frame] >> metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  `?p. dst = Var p` by metis_tac[emitted_insts_emit_op] >> gvs[] >>
  `lookup_var p u = SOME (n2w (b+off)) /\
   w2n (n2w (b+off):bytes32)+32 <= u.vs_alloca_next` by
    (fs[eval_operand_def] >> simp[]) >>
  `w2n (n2w (b+off):bytes32) = b+off` by
    (simp[] >> decide_tac) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `u`,
                  `d` |-> `n2w (b+off)`, `src` |-> `op`]
    extcall_word_store_result_mem) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[] >> metis_tac[])) >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK z)` by
    (qpat_x_assum `!ctx. gas_path_mem ctx func s 0 (OK u)`
       (qspec_then `ctx` assume_tac) >>
     drule_all gas_path_mem_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
     fs[lookup_var_def]) >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED
