(* The Boolean head and bytes tail share one endpoint for every dead mask. *)
Theory bodyFullRawCallTupleStore
Ancestors
  rawCallBufferPtr typedCopyPtr fragGasCopyLoop
  stmtAppendStorageRunPtr exprSimProps
  fragGasSeqPtr fragGasOriginPtr fragExecMem fragExecPtr fragExec instIdxIndep
  ptrDiscipline bodyPtrDefs ghostPcTransportPtr exprLoweringProps
  emitHelperProps loweringShapeRules compileEnv emitHelper context loweringStateRelDefs
  venomExecSemantics venomInst venomState venomMemProps
  valueEncodingDefs valueEncoding loweringPosts vfmConstants
  words list rich_list finite_map pred_set arithmetic
  gasEvents gasCount instMemFrontier memSafeRun freshWrites ssaOperandFrame
Libs monadsyntax pairLib

Theorem raw_call_tuple_store_origin_ptr:
  !sa sb dst src ok tw w success padded n rd s G tn lo explicit ctx func PG.
  (do emit_void MSTORE [Var dst;ok];
      d <- emit_op ADD [Var dst;Lit 32w];
      emit_void MCOPY [d;Var src;Lit (n2w (32+padded))] od) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  (!x. ok = Var x ==> not_fresh_at sa x) /\
  lookup_var dst s = SOME tw /\ lookup_var src s = SOME w /\
  eval_operand ok s = SOME (bool_to_word success) /\ op_taint tn ok = {} /\
  ptr_covers G tn dst s (64+padded) /\ ptr_covers G tn src s (32+padded) /\
  w2n tw+64+padded < dimword (:256) /\ 32+padded < dimword (:256) /\
  w2n tw+64+padded <= s.vs_alloca_next /\
  w2n w+32+padded <= s.vs_alloca_next /\
  regions_disjoint (w2n tw) (64+padded) (w2n w) (32+padded) /\
  val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n rd)) <= 32+padded /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n rd)) (w2n w) mem)
  ==>
  ?z_raw z J un.
    run_inst_seq (emitted_insts sa sb) s = OK z_raw /\
    z = z_raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
    z = (mcopy (w2n tw+32) (w2n w) (32+padded)
      (mstore (w2n tw) (bool_to_word success) s))
      with <|vs_vars := z.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    z.vs_current_bb = sb.cs_current_bb /\
    ptr_covers J un dst z (64+padded) /\
    un.t_mem =
      ((tn.t_mem DIFF {i | w2n tw <= i /\ i < w2n tw+32})
        DIFF {i | w2n tw+32 <= i /\ i < w2n tw+32+(32+padded)}) UNION
      {w2n tw+32+i | i | i < 32+padded /\
        w2n w+i IN (tn.t_mem DIFF {j | w2n tw <= j /\ j < w2n tw+32})} /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x)) /\
    (!mem. mem_agree_outside un.t_mem z.vs_memory mem ==>
      val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
        (ArrayV (TupleV [BoolV success;BytesV (TAKE n rd)])) (w2n tw) mem) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,J,un))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?s1 d s2.
    emit_void MSTORE [Var dst;ok] sa = ((),s1) /\
    emit_op ADD [Var dst;Lit 32w] s1 = (d,s2) /\
    emit_void MCOPY [d;Var src;Lit (n2w (32+padded))] s2 = ((),sb)` by
    (qpat_x_assum `_ = ((),sb)` mp_tac >>
     simp[comp_bind_def,comp_ignore_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_assum `emit_op ADD _ s1 = (d,s2)`
    (mp_then Any mp_tac emit_op_facts) >>
  disch_then (qx_choose_then `dx` strip_assume_tac) >>
  qpat_x_assum `d = Var dx` SUBST_ALL_TAC >>
  `ci_mono sa s1` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `!x. not_fresh_at sa x ==> x <> dx` by
    (rpt strip_tac >> fs[ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `dst <> dx /\ src <> dx` by simp[] >>
  qabbrev_tac `i_store = mk_inst sa.cs_next_id MSTORE [Var dst;ok] []` >>
  qabbrev_tac `i_add = mk_inst s1.cs_next_id ADD [Var dst;Lit 32w] [dx]` >>
  qabbrev_tac `i_copy = mk_inst s2.cs_next_id MCOPY
    [Var dx;Var src;Lit (n2w (32+padded))] []` >>
  `emitted_insts sa sb = [i_store;i_add;i_copy] /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [i_store;i_add;i_copy]` by
    (qpat_x_assum `emit_void MSTORE _ sa = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ s1 = _` mp_tac >>
     qpat_x_assum `emit_void MCOPY _ s2 = _` mp_tac >>
     simp[emit_void_def,emit_op_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,fresh_var_def,fresh_id_def,emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def,Abbr `i_store`,Abbr `i_add`,
       Abbr `i_copy`,DROP_LENGTH_APPEND,APPEND_ASSOC]) >>
  suspend "native"
QED

Resume raw_call_tuple_store_origin_ptr[native]:
  `w2n (tw+32w) = w2n tw+32` by
    (simp[wordsTheory.w2n_add_2] >>
     `w2n tw+32 < dimword (:256)` by decide_tac >> simp[]) >>
  qabbrev_tac `t_store = mstore (w2n tw) (bool_to_word success) s` >>
  qabbrev_tac `t_add = update_var dx (tw+32w) t_store` >>
  qabbrev_tac `z_raw = mcopy (w2n tw+32) (w2n w) (32+padded) t_add` >>
  `FLOOKUP s.vs_vars dst = SOME tw /\ FLOOKUP s.vs_vars src = SOME w` by
    fs[lookup_var_def] >>
  `step_inst_base i_store s = OK t_store` by
    simp[Abbr `i_store`,Abbr `t_store`,step_inst_base_opcode_eqs,mk_inst_def,
      exec_write2_def,eval_operand_def] >>
  `eval_operand (Var dst) t_store = SOME tw /\
   eval_operand (Lit 32w) t_store = SOME 32w` by
    simp[Abbr `t_store`,eval_operand_def] >>
  `step_inst_base i_add t_store = OK t_add` by
    simp[Abbr `i_add`,Abbr `t_add`,step_inst_base_opcode_eqs,mk_inst_def,
      exec_pure2_def] >>
  `eval_operand (Var dx) t_add = SOME (tw+32w) /\
   eval_operand (Var src) t_add = SOME w /\
   eval_operand (Lit (n2w (32+padded))) t_add = SOME (n2w (32+padded))` by
    simp[Abbr `t_add`,Abbr `t_store`,eval_operand_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE,mstore_vars] >>
  `step_inst_base i_copy t_add = OK z_raw` by
    simp[Abbr `i_copy`,Abbr `z_raw`,step_inst_base_opcode_eqs,mk_inst_def,
      eval_operand_def,wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `run_inst_seq (emitted_insts sa sb) s = OK z_raw` by
    simp[run_inst_seq_def] >>
  qabbrev_tac `tn_store = tn with t_mem :=
    tn.t_mem DIFF {i | w2n tw <= i /\ i < w2n tw+32}` >>
  qabbrev_tac `tn_add = tn_store with t_var := tn_store.t_var |+ (dx,{})` >>
  qabbrev_tac `J = step_prov PG G i_add t_add` >>
  qabbrev_tac `un = step_taint i_copy t_add z_raw tn_add` >>
  `step_taint i_store s t_store tn = tn_store /\
   step_prov PG G i_store t_store = G` by
    simp[Abbr `i_store`,Abbr `t_store`,Abbr `tn_store`,
      raw_call_mstore_clean_effect,scalar_void_prov] >>
  `step_taint i_add t_store t_add tn_store = tn_add` by
    simp[Abbr `i_add`,Abbr `t_add`,Abbr `tn_add`,scalar_add_taint,update_var_def] >>
  suspend "ghost"
QED

Resume raw_call_tuple_store_origin_ptr[ghost]:
  `?b sz. FLOOKUP G dst = SOME (b,sz) /\
    b <= w2n tw /\ w2n tw+(64+padded) <= b+sz /\
    op_taint tn (Var dst) = {}` by
    (qpat_x_assum `ptr_covers G tn dst s _` mp_tac >> simp[ptr_covers_def]) >>
  `J = G |+ (dx,(b,sz))` by
    simp[Abbr `J`,Abbr `i_add`,step_prov_def,set_prov_def,out_prov_def,
      mk_inst_def,first_prov_def,op_prov_def] >>
  `step_prov PG J i_copy z_raw = J /\ un.t_var = tn_add.t_var /\
   un.t_stor = tn_add.t_stor /\ un.t_trans = tn_add.t_trans /\
   un.t_mem = (tn_add.t_mem DIFF
     {i | w2n tw+32 <= i /\ i < w2n tw+32+(32+padded)}) UNION
     {w2n tw+32+i | i | i < 32+padded /\ w2n w+i IN tn_add.t_mem}` by
    (mp_tac (Q.SPECL [`PG`,`J`,`tn_add`,`t_add`,`s2.cs_next_id`,
       `Var dx`,`Var src`,`Lit (n2w (32+padded))`,`w`,`tw+32w`,
       `n2w (32+padded)`] mcopy_operand_ghost_frame) >>
     simp[Abbr `i_copy`,Abbr `un`,Abbr `z_raw`,wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]) >>
  `un.t_imm = tn_add.t_imm` by
    simp[Abbr `un`,Abbr `i_copy`,step_taint_def,mk_inst_def,
      set_var_taint_def,store_taint_def,adopt_reset_def,step_writes_def,
      written_taint_def,imm_taint_def] >>
  `ptr_covers G tn dst s 32` by
    (simp[ptr_covers_def] >> qexistsl_tac [`tw`,`b`,`sz`] >>
     simp[] >> decide_tac) >>
  `ptr_covers J tn_add dx t_add (32+padded)` by
    (simp[ptr_covers_def,Abbr `tn_add`,op_taint_def,FLOOKUP_UPDATE,
       Abbr `t_add`,lookup_var_def,update_var_def] >> decide_tac) >>
  `ptr_covers J tn_add src t_add (32+padded)` by
    (qpat_x_assum `ptr_covers G tn src s _` mp_tac >>
     simp[ptr_covers_def,Abbr `tn_add`,Abbr `tn_store`,Abbr `t_add`,
       Abbr `t_store`,op_taint_def,FLOOKUP_UPDATE,lookup_var_def,
       update_var_def,mstore_vars]) >>
  suspend "checks"
QED

Resume raw_call_tuple_store_origin_ptr[checks]:
  `~is_terminator i_store.inst_opcode /\ ~is_terminator i_add.inst_opcode /\
   ~is_terminator i_copy.inst_opcode` by
    simp[Abbr `i_store`,Abbr `i_add`,Abbr `i_copy`,mk_inst_def,is_terminator_def] >>
  `!D k. inst_seq_ptr D 0 ctx func PG G tn [i_store]
    (s with vs_inst_idx := k) G tn_store` by
    (rpt gen_tac >> simp[inst_seq_ptr_def,step_inst_inst_idx_indep,
       exec_result_map_def] >> simp[Abbr `i_store`] >>
     irule ptr_inst_ok_mstore >> simp[]) >>
  `!D k. inst_seq_ptr D 0 ctx func PG G tn_store [i_add]
    (t_store with vs_inst_idx := k) J tn_add` by
    (rpt gen_tac >> simp[inst_seq_ptr_def,step_inst_inst_idx_indep,
       exec_result_map_def,Abbr `J`] >> simp[Abbr `i_add`] >>
     irule ptr_inst_ok_copy_len_binop >>
     fs[Abbr `tn_store`,op_taint_def]) >>
  `!D k. inst_seq_ptr D 0 ctx func PG J tn_add [i_copy]
    (t_add with vs_inst_idx := k) J un` by
    (rpt gen_tac >> simp[inst_seq_ptr_def,step_inst_inst_idx_indep,
       exec_result_map_def,Abbr `un`] >> simp[Abbr `i_copy`,scalar_void_prov] >>
     irule ptr_inst_ok_mcopy >>
     gvs[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sb) s J un` by
    (gen_tac >>
     qpat_x_assum `!D k. inst_seq_ptr D 0 ctx func PG G tn [i_store] _ _ _`
       (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >>
     qpat_x_assum `!D k. inst_seq_ptr D 0 ctx func PG G tn_store [i_add] _ _ _`
       (qspecl_then [`D`,`SUC s.vs_inst_idx`] mp_tac) >>
     qpat_x_assum `!D k. inst_seq_ptr D 0 ctx func PG J tn_add [i_copy] _ _ _`
       (qspecl_then [`D`,`SUC (SUC s.vs_inst_idx)`] mp_tac) >>
     simp[inst_seq_ptr_def,step_inst_inst_idx_indep,exec_result_map_def] >>
     rpt strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[run_inst_seq_mem_ok_def] >>
     simp[Abbr `i_store`,Abbr `i_add`,Abbr `i_copy`,below_frontier_MSTORE,
       below_frontier_MCOPY,inst_dload_in_section_def,mk_inst_def,eval_operand_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       codegenRelTheory.sized_source_write_range_def,
       Abbr `t_store`,Abbr `t_add`,update_var_def,
       lookup_var_def,FLOOKUP_UPDATE,mstore_vars,wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac) >>
  suspend "representation"
QED

Resume raw_call_tuple_store_origin_ptr[representation]:
  qabbrev_tac `z = z_raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `z = (mcopy (w2n tw+32) (w2n w) (32+padded)
    (mstore (w2n tw) (bool_to_word success) s))
    with <|vs_vars := z.vs_vars;vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    simp[Abbr `z`,Abbr `z_raw`,Abbr `t_add`,mcopy_update_var,update_var_def] >>
  `un.t_mem =
    ((tn.t_mem DIFF {i | w2n tw <= i /\ i < w2n tw+32})
      DIFF {i | w2n tw+32 <= i /\ i < w2n tw+32+(32+padded)}) UNION
    {w2n tw+32+i | i | i < 32+padded /\
      w2n w+i IN (tn.t_mem DIFF {j | w2n tw <= j /\ j < w2n tw+32})} /\
   un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm` by
    simp[Abbr `tn_add`,Abbr `tn_store`] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dx` by simp[] >>
     simp[Abbr `z`,Abbr `z_raw`,Abbr `t_add`,Abbr `t_store`,lookup_var_def,
       mcopy_vars,mstore_vars,update_var_def,FLOOKUP_UPDATE,
       op_taint_def,Abbr `tn_add`,Abbr `tn_store`]) >>
  `ptr_covers J un dst z (64+padded)` by
    (simp[ptr_covers_def,op_taint_def,Abbr `tn_add`,Abbr `tn_store`,
       FLOOKUP_UPDATE] >> qexistsl_tac [`tw`,`b`,`sz`] >>
     simp[Abbr `z`,Abbr `z_raw`,Abbr `t_add`,Abbr `t_store`,lookup_var_def,
       mcopy_vars,mstore_vars,update_var_def,FLOOKUP_UPDATE]) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n rd))` by
    (qspec_then `n` mp_tac le_word_size_mul >>
     simp[val_wf_def,type_memory_size_def,LENGTH_TAKE_EQ] >> decide_tac) >>
  `val_to_w256 (BoolV success) = bool_to_word success` by
    (Cases_on `success` >> simp[val_to_w256_def,bool_to_word_def]) >>
  `z.vs_memory = (mcopy (w2n tw+32) (w2n w) (32+padded)
    (mstore (w2n tw) (bool_to_word success) s)).vs_memory` by
    (qpat_assum `z = _ with <|vs_vars := _;vs_inst_idx := _|>`
       (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!mem. mem_agree_outside un.t_mem z.vs_memory mem ==>
    val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success;BytesV (TAKE n rd)])) (w2n tw) mem` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`tt` |-> `BaseTV (BytesT (Dynamic n))`,
       `tv` |-> `BytesV (TAKE n rd)`,`n` |-> `32+padded`,
       `a` |-> `w2n (w:256 word)`,`b` |-> `w2n (tw:256 word)`,`dirty` |-> `tn.t_mem`,
       `s` |-> `s`,`flag` |-> `success`] bool_pair_mstore_mcopy_robust) >>
     impl_tac >- (simp[] >> fs[regions_disjoint_def] >> decide_tac) >>
     disch_then (qspec_then `mem` mp_tac) >> simp[] >>
     disch_then irule >>
     qpat_x_assum `mem_agree_outside un.t_mem z.vs_memory mem` mp_tac >>
     simp[Abbr `t_store`]) >>
  suspend "finish"
QED

Resume raw_call_tuple_store_origin_ptr[finish]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[Abbr `i_store`,Abbr `i_add`,Abbr `i_copy`,mk_inst_def,is_terminator_def] >>
  `z.vs_current_bb = sb.cs_current_bb` by
    (simp_tac (srw_ss()) [Abbr `z`,Abbr `z_raw`,Abbr `t_add`,Abbr `t_store`,
       mcopy_def,mstore_def,update_var_def,write_memory_with_expansion_def,LET_THM] >>
     asm_rewrite_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sa sb func`
       (strip_assume_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     rename1 `lookup_block sb.cs_current_bb func.fn_blocks = SOME bb0` >>
     qpat_assum `isPREFIX sb.cs_current_insts bb0.bb_instructions`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     rename1 `bb0.bb_instructions = sb.cs_current_insts ++ extra` >>
     qexists_tac `bb0` >> conj_tac
     >- (qpat_assum `s.vs_current_bb = sa.cs_current_bb`
           (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `sb.cs_current_bb = sa.cs_current_bb`
           (fn th => PURE_REWRITE_TAC [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
     simp[IS_PREFIX_APPEND] >>
     qexists_tac `extra` >>
     rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK z,J,un)` by
    (gen_tac >> simp_tac bool_ss [Abbr `z`] >>
     qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = _`
       (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     irule (cj 1 run_inst_seq_origin_ptr_lift) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `!D. inst_seq_ptr D 0 ctx func PG G tn _ s J un`
         (qspec_then `D` ACCEPT_TAC),
       qexists_tac `bb` >> conj_tac >> first_assum ACCEPT_TAC]) >>
  qexistsl_tac [`z_raw`,`z`,`J`,`un`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    simp_tac bool_ss [Abbr `t_store`] >> first_assum ACCEPT_TAC,
    simp_tac bool_ss [Abbr `z`]]
QED

Finalise raw_call_tuple_store_origin_ptr
