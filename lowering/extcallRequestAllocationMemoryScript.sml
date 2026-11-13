(* Actual shared-buffer allocation and the selector store. *)
Theory extcallRequestAllocationMemory
Ancestors
  bodyMemAggregateAlloc bodyDeclWordMemory extcallCalldataOpsMemory
  exprSimAlloc exprSimHash exprSimProps exprLoweringProps loweringPosts
  localPtrsProps fragGasPathMem fragGasPathFrameMem fragGasMode allocaHistory
  emitHelperProps compileEnv context venomState venomInst venomMemDefs fragExec
  valueEncodingProps words list arithmetic finite_map abiCallerAllocation
  loweringStateRelDefs freshWrites

Theorem extcall_shared_buffer_selector_mem:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit (n2w method_id)] sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ 32 <= sz /\ sz < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?inst x b t.
    buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [x] /\ inst.inst_id < sb.cs_next_id /\
    not_fresh_at sb x /\ local_ptrs_reserved ce sb /\
    (!scopes. not_local_ptr ce scopes x) /\
    gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
    stmt_state_rel ctx func ce cx es t /\ wb_frame ce es es sa s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b+sz < dimword (:256) /\ b+sz <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    mem_bytes_at b 32 t.vs_memory = word_to_bytes (n2w method_id:bytes32) T /\
    (!name p n. local_region ce es.scopes t name p n ==>
      loweringStateRelDefs$regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n <=>
      local_region ce es.scopes s name p n) /\
    (!aid p n. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME(p,n) ==>
      loweringStateRelDefs$regions_disjoint b sz p n)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_emit_void,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK allocated)` >>
  `gas_path_mem ctx func s 0 (OK allocated)` by fs[gas_marked_path_def] >>
  `b+32 <= allocated.vs_alloca_next /\ b+32 < dimword (:256)` by decide_tac >>
  `alloca_inv allocated` by fs[stmt_state_rel_def] >>
  `inst.inst_opcode = ALLOCA` by
    (drule_all buffer_alloc_code >> strip_tac >>
     `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]` by
       (irule fn_inst_ids_distinct_inj >> simp[mk_inst_def] >>
        qexists_tac `func` >> fs[mk_inst_def]) >>
     simp[mk_inst_def]) >>
  `emit_void MSTORE [Var x;Lit (n2w method_id)] sm = ((),sb)` by fs[] >>
  `eval_operand (Lit (n2w method_id)) allocated = SOME (n2w method_id)` by
    simp[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `b MOD dimword (:256) = b` by
    (irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `w2n (n2w b:bytes32) = b` by simp[wordsTheory.w2n_n2w] >>
  `w2n (n2w b:bytes32)+32 <= allocated.vs_alloca_next` by simp[] >>
  drule_all annassign_word_mstore_path_mem >>
  disch_then (qspec_then `ctx` (fn th => strip_assume_tac
    (REWRITE_RULE [ASSUME ``w2n (n2w b:bytes32) = b``,
      ASSUME ``b MOD dimword (:256) = b``] th))) >>
  qabbrev_tac `t = mstore b (n2w method_id) allocated with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_path_mem ctx func allocated 0 (OK t) /\ alloca_history func t` by
    (simp[Abbr `t`] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_path_mem ctx func s 0 (OK t)` by metis_tac[gas_path_mem_then,ADD] >>
  suspend "state"
QED

Resume extcall_shared_buffer_selector_mem[state]:
  `stmt_state_rel ctx func ce cx es t` by
    (simp[Abbr `t`,stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
     conj_tac >- (qexistsl_tac [`b`,`inst`,`sz`] >> simp[] >>
       rpt strip_tac >>
       qpat_x_assum `!name p n. local_region ce es.scopes allocated name p n ==> _`
         (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
       asm_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     first_assum ACCEPT_TAC) >>
  `sb.cs_current_bb = sm.cs_current_bb /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (imp_res_tac emit_void_extends >> fs[ci_mono_def,same_blocks_def]) >>
  `local_ptrs_reserved ce sb /\ not_fresh_at sb x /\ inst.inst_id < sb.cs_next_id` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >>
       asm_rewrite_tac []) >>
     conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sm` >>
       asm_rewrite_tac []) >> decide_tac) >>
  `!name p n. local_region ce es.scopes t name p n <=>
     local_region ce es.scopes s name p n` by
    (qpat_x_assum `!name p n. local_region ce es.scopes allocated name p n <=> _`
       mp_tac >> simp[Abbr `t`,local_region_def,lookup_var_def,mstore_def]) >>
  suspend "frame"
QED

Resume extcall_shared_buffer_selector_mem[frame]:
  `!name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     `loweringStateRelDefs$regions_disjoint b sz p n` by
       (qpat_x_assum `!name p n. local_region ce es.scopes allocated name p n ==> _`
          (qspecl_then [`name`,`p`,`n`] mp_tac) >> asm_rewrite_tac []) >>
     simp[Abbr `t`] >>
     `mem_bytes_at p n (mstore b (n2w method_id) allocated).vs_memory =
       mem_bytes_at p n allocated.vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`b`,`sz`] >>
        asm_rewrite_tac [] >> decide_tac) >> asm_rewrite_tac []) >>
  `wb_frame ce es es sa s t` by
    (rewrite_tac[wb_frame_def] >> conj_tac
     >- (qx_genl_tac [`z`,`w`] >> strip_tac >>
         `lookup_var z allocated = lookup_var z s` by metis_tac[] >>
         simp[Abbr `t`,lookup_var_def,mstore_def] >> fs[lookup_var_def]) >>
     conj_tac
     >- (rpt strip_tac >> simp[Abbr `t`,mstore_def] >> metis_tac[]) >>
     conj_tac
     >- (qx_genl_tac [`aid`,`off`,`n`] >> strip_tac >>
         `loweringStateRelDefs$regions_disjoint b sz off n` by metis_tac[] >>
         `mem_bytes_at off n (mstore b (n2w method_id) allocated).vs_memory =
           mem_bytes_at off n allocated.vs_memory` by
           (irule mstore_region_frame >> qexistsl_tac [`b`,`sz`] >>
            asm_rewrite_tac [] >> decide_tac) >> simp[Abbr `t`]) >>
     irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `!aid p n. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME(p,n) ==>
      loweringStateRelDefs$regions_disjoint b sz p n` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas inst.inst_id = SOME(b,sz)` by
      (simp[Abbr `t`,mstore_def] >> metis_tac[]) >>
     `alloca_inv t` by fs[stmt_state_rel_def] >>
     `inst.inst_id <> aid` by decide_tac >>
     drule_all abi_caller_allocation_separate >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `FLOOKUP allocated.vs_allocas sa.cs_next_id = SOME(b,sz)` by
    (ACCEPT_TAC (REWRITE_RULE [ASSUME ``inst.inst_id = sa.cs_next_id``]
      (ASSUME ``FLOOKUP allocated.vs_allocas inst.inst_id = SOME(b,sz)``))) >>
  `mem_bytes_at b 32 t.vs_memory = word_to_bytes (n2w method_id:bytes32) T` by
    simp[Abbr `t`,mem_bytes_at_mstore_same] >>
  `!name p n. local_region ce es.scopes s name p n ==>
    loweringStateRelDefs$regions_disjoint b sz p n` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name p n. local_region ce es.scopes allocated name p n ==> _`
       (qspecl_then [`name`,`p`,`n`] mp_tac) >> asm_rewrite_tac []) >>
  qexistsl_tac [`inst`,`x`,`b`,`t`] >> asm_rewrite_tac [] >>
  simp[Abbr `t`,eval_operand_def,lookup_var_def,mstore_def,mem_bytes_at_mstore_same] >>
  fs[lookup_var_def] >> rpt conj_tac >> rpt strip_tac >>
  first_assum ACCEPT_TAC
QED

Finalise extcall_shared_buffer_selector_mem
