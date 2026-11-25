(* The four ECRecover input words, staged on one nonallocating path. *)
Theory bodyECRecoverInputStoresMods
Ancestors
  bodyPtrPrecompileBuiltinsRecoveryInput bodyPtrPrecompileBuiltinsCompilerStages
  bodyMemBiECRecoverMemory bodyFullUnwrapRun bodyFullUnwrapSlotFrame
  bodyFullShadowBodyInv freshWrites
  exprSimPrecompiles exprSimRawCallCalldata bodyMemoryDefs bodyPtrDefs
  fragGasCopySeqLiftProps fragGasSeqPtr logTopicScalarPtr ghostPcTransportPtr
  immutableMemoryFrame exprLoweringProps emitHelperProps emitHelper context compileEnv
  loweringStateRelDefs loweringPosts ptrDiscipline
  vyperStorageFootprint venomState venomInst words arithmetic finite_map pred_set list
Libs
  monadsyntax

Theorem input_stores_compile_cuts[local]:
  emit_void MSTORE [base_op;h] sa = ((),sb) /\
  (do dst <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [dst;v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [dst;r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [dst;sig] od) sd = ((),sp) ==>
  (do emit_void MSTORE [base_op;h];
      p1 <- emit_op ADD [base_op; Lit 32w]; emit_void MSTORE [p1;v];
      p2 <- emit_op ADD [base_op; Lit 64w]; emit_void MSTORE [p2;r];
      p3 <- emit_op ADD [base_op; Lit 96w]; emit_void MSTORE [p3;sig] od) sa = ((),sp) /\
  emitted_insts sa sp = emitted_insts sa sb ++ emitted_insts sb sc ++
                         emitted_insts sc sd ++ emitted_insts sd sp
Proof
  strip_tac >> conj_tac
  >- (Cases_on `emit_op ADD [base_op; Lit 32w] sb` >>
      Cases_on `emit_op ADD [base_op; Lit 64w] sc` >>
      Cases_on `emit_op ADD [base_op; Lit 96w] sd` >>
      fs[comp_ignore_bind_def,comp_bind_def]) >>
  imp_res_tac direct_store_compiler_shape >>
  imp_res_tac offset_store_compiler_shape >>
  imp_res_tac compiler_append_trans >>
  metis_tac[APPEND_ASSOC]
QED

Theorem input_stores_opcodes[local]:
  (do emit_void MSTORE [base_op;h];
      p1 <- emit_op ADD [base_op; Lit 32w]; emit_void MSTORE [p1;v];
      p2 <- emit_op ADD [base_op; Lit 64w]; emit_void MSTORE [p2;r];
      p3 <- emit_op ADD [base_op; Lit 96w]; emit_void MSTORE [p3;sig] od) sa = ((),sp) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE /\
    i.inst_opcode <> DALLOCA /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sp)
Proof
  simp[emit_op_def,emit_void_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def,DROP_APPEND1,mk_inst_def,is_terminator_def]
QED

Theorem input_stores_raw_post[local]:
  (do emit_void MSTORE [base_op;h];
      p1 <- emit_op ADD [base_op; Lit 32w]; emit_void MSTORE [p1;v];
      p2 <- emit_op ADD [base_op; Lit 64w]; emit_void MSTORE [p2;r];
      p3 <- emit_op ADD [base_op; Lit 96w]; emit_void MSTORE [p3;sig] od) sa = ((),sp) /\
  eval_operand base_op s = SOME wi /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n wi + 128 < dimword(:256) /\
  run_inst_seq (emitted_insts sa sp) s = OK raw ==>
  (raw with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  LENGTH s.vs_memory <= LENGTH raw.vs_memory /\
  mem_bytes_at (w2n wi) 128 raw.vs_memory =
    word_to_bytes wh T ++ word_to_bytes wv T ++
    word_to_bytes wr T ++ word_to_bytes ws T /\
  (!b len. regions_disjoint (w2n wi) 128 b len ==>
    mem_bytes_at b len raw.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  strip_tac >> drule_all ecrecover_input_stores_run >> strip_tac >>
  `t = raw` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> simp[]) >>
  gvs[] >> rpt conj_tac
  >- (simp[immutable_mstore_capacity] >> decide_tac)
  >- simp[scratch_four_word_stores]
  >- (rpt strip_tac >> fs[regions_disjoint_def] >>
      simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint])
QED

Theorem input_stores_path[local]:
  fn_has_code sa sp func /\
  sp.cs_current_bb = sa.cs_current_bb /\
  sp.cs_current_insts = sa.cs_current_insts ++ code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE /\
    i.inst_opcode <> DALLOCA /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq_mem_ok code s /\ allocas_from lo s /\
  run_inst_seq code s = OK raw /\
  (!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn') ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (raw with vs_inst_idx := LENGTH sp.cs_current_insts),G',tn')
Proof
  strip_tac >> gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`code`,`sa`] >> simp[] >> rpt conj_tac
  >- fs[EVERY_MEM]
  >- (fs[EVERY_MEM] >> metis_tac[MEM_APPEND,MEM,
        memSafeRunTheory.dalloca_no_wrap_non_dalloca])
  >- (irule inst_seq_ptr_lower_bound_transport >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code`
        by fs[EVERY_MEM] >>
      simp[] >> qexists_tac `0` >> simp[])
QED

Theorem input_stores_entry_zero[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at D 0 d cenv cx es G tn s /\ stor_taint_ok_at D tn s
Proof
  simp[ghost_inv_at_mods_def,ghost_inv_at_def,allocas_from_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem input_stores_zero_ghost[local]:
  ghost_inv_at D 0 d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    regions_disjoint start 128 b len) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!b len. regions_disjoint start 128 b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  tn'.t_mem SUBSET tn.t_mem /\ stor_taint_ok_at D tn' t ==>
  ghost_inv_at D 0 d cenv cx es G' tn' t
Proof
  strip_tac >> irule unwrap_slot_copy_ghost_inv_at_mono >>
  simp[allocas_from_def] >>
  qexistsl_tac [`G`,`func`,`128`,`s`,`sa`,`start`,`tn`] >>
  fs[regions_disjoint_def,SUBSET_DEF] >> metis_tac[]
QED

Theorem input_stores_state_post[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  (raw with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x raw = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  old.cs_next_var <= sa.cs_next_var /\ old.cs_next_id <= sa.cs_next_id /\
  (!b len. regions_disjoint (w2n wi) 128 b len ==>
    mem_bytes_at b len raw.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    regions_disjoint (w2n wi) 128 b len) /\
  (!aid b len. aid < old.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n wi) 128 b len) /\
  LENGTH s.vs_memory <= LENGTH raw.vs_memory /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wi) 128 off (type_memory_size tv)) ==>
  stmt_state_rel H ctx func cenv cx es (raw with vs_inst_idx := k) /\
  wb_frame cenv es es old s (raw with vs_inst_idx := k)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx,raw_call_wb_frame_inst_idx] >>
  drule_all (Q.INST [`scratch_len` |-> `128`] scratch_memory_frame) >> simp[]
QED

Theorem input_stores_lookup_idx[local]:
  lookup_var x (s with vs_inst_idx := k) = lookup_var x s
Proof
  simp[lookup_var_def]
QED

Theorem ecrecover_input_stores_physical_mods:
  emit_void MSTORE [Var root;h] sa = ((),sb) /\
  (do dst <- emit_op ADD [Var root; Lit 32w];
      emit_void MSTORE [dst;v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var root; Lit 64w];
      emit_void MSTORE [dst;r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [Var root; Lit 96w];
      emit_void MSTORE [dst;sig] od) sd = ((),sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\
  not_fresh_at sa root /\ ptr_covers G tn root s 128 /\
  lookup_var root s = SOME wi /\ w2n wi + 128 < dimword(:256) /\
  w2n wi + 128 <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas site = SOME (w2n wi,128) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sa p)) [h;v;r;sig] /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  old.cs_next_var <= sa.cs_next_var /\ old.cs_next_id <= sa.cs_next_id /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    regions_disjoint (w2n wi) 128 b len) /\
  (!aid b len. aid < old.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n wi) 128 b len) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wi) 128 off (type_memory_size tv)) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\ alloca_history func t /\
    local_ptrs_reserved cenv sp /\ return_buf_frame d cenv sp t /\
    not_fresh_at sp root /\ ptr_covers G' tn' root t 128 /\
    lookup_var root t = SOME wi /\ lo <= w2n wi /\ allocas_from lo t /\
    w2n wi + 128 <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas site = SOME (w2n wi,128) /\
    mem_bytes_at (w2n wi) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++ word_to_bytes wr T ++ word_to_bytes ws T /\
    (!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tn'.t_mem) /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!b len. regions_disjoint (w2n wi) 128 b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
    (!es0 sk s0 G0 tn0. sk.cs_next_var <= sa.cs_next_var /\
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G' tn') /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es es old s t /\
      ghost_inv_at (DF H) 0 d cenv cx es G' tn' t)
Proof
  strip_tac >> drule_all input_stores_compile_cuts >> strip_tac >>
  drule input_stores_opcodes >> strip_tac >>
  drule ecrecover_input_stores_shape >> strip_tac >>
  drule_all recovery_input_staging_checked >>
  disch_then (qspecl_then [`func`,`PG`] (mk_asm "staging")) >>
  asm "staging" (qspec_then `ARB` strip_assume_tac) >>
  rename1 `run_inst_seq _ s = OK raw` >>
  rename1 `ptr_covers Ga ta root raw 128` >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by simp[venom_state_component_equality] >>
  `inst_seq_ptr ARB 0 ctx func PG G tn (emitted_insts sa sp) s Ga ta` by
    (qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ Ga ta`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `s with vs_inst_idx := s.vs_inst_idx = s`
       (pure_rewrite_tac o single) >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sp) s Ga ta` by
    (qx_gen_tac `D` >>
     asm "staging" (qspec_then `D` (qx_choose_then `other`
        (qx_choose_then `Gb` (qx_choose_then `tb` strip_assume_tac)))) >>
     `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sp) s Gb tb` by
       (qpat_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ Gb tb`
          (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `s with vs_inst_idx := s.vs_inst_idx = s`
       (pure_rewrite_tac o single) >> simp[]) >>
     `Gb = Ga /\ tb = ta` by (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
     fs[]) >>
  `run_inst_seq (emitted_insts sa sp) s = OK raw` by simp[] >>
  `eval_operand (Var root) s = SOME wi /\
   (!x. MEM (Var x) [Var root;h;v;r;sig] ==> not_fresh_at sa x)` by
    (simp[eval_operand_def] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sp) s` by
    (drule_all ecrecover_input_stores_mem >> simp[]) >>
  drule_all input_stores_raw_post >> strip_tac >>
  suspend "landing"
QED

Resume ecrecover_input_stores_physical_mods[landing]:
  asm_x "staging" kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  `allocas_from lo s /\ alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >>
     fs[ghost_inv_at_mods_def,stmt_state_rel_def,state_rel_def]) >>
  `lo <= w2n wi` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`site`,`w2n (wi:256 word)`,`128`] mp_tac) >> simp[]) >>
  `sp.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `local_ptrs_reserved cenv sp /\ not_fresh_at sp root` by
    metis_tac[local_ptrs_reserved_next_var,freshWritesTheory.not_fresh_at_mono] >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sp.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,Ga,ta)` by
    (simp[Abbr `t`] >>
     drule_all input_stores_path >> simp[]) >>
  `alloca_history func t` by
    (qunabbrev_tac `t` >> irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`emitted_insts sa sp`,`s`,`sa`] >> fs[EVERY_MEM]) >>
  qpat_assum `raw with <|vs_vars := _; vs_memory := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `ta.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF] >>
  `ta.t_imm = tn.t_imm` by
    (`EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sp)` by fs[EVERY_MEM] >>
     drule_all inst_seq_ptr_immutable_taint_frame >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, input_stores_lookup_idx] >>
  `return_buf_frame d cenv sp t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >>
     simp[Abbr `t`,input_stores_lookup_idx] >> metis_tac[]) >>
  qexistsl_tac [`t`,`Ga`,`ta`] >>
  suspend "post"
QED

Resume ecrecover_input_stores_physical_mods[post]:
  `allocas_from lo t` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[Abbr `t`,allocas_from_def]) >>
  `!i. i < lo /\ i IN ta.t_mem ==> i IN tn.t_mem` by simp[] >>
  `!es0 sk s0 G0 tn0. sk.cs_next_var <= sa.cs_next_var /\
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 Ga ta` by
    (rpt gen_tac >> strip_tac >> irule ghost_kept_at_clean_suffix >>
     qexistsl_tac [`G`,`tn`] >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es es old s t /\
      ghost_inv_at (DF H) 0 d cenv cx es Ga ta t` suffices_by
    (simp[Abbr `t`,input_stores_lookup_idx] >> metis_tac[]) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es es old s t` by
    (`!x. not_fresh_at sa x ==> lookup_var x raw = lookup_var x s` by
       (rpt strip_tac >> fs[]) >>
     qunabbrev_tac `t` >> drule_all input_stores_state_post >> simp[]) >>
  simp[] >>
  drule_then strip_assume_tac input_stores_entry_zero >>
  `stor_taint_ok_at (DF H) ta t` by fs[stor_taint_ok_at_def,Abbr `t`] >>
  irule input_stores_zero_ghost >> simp[] >>
  qexistsl_tac [`G`,`func`,`s`,`sa`,`w2n (wi:256 word)`,`tn`] >>
  simp[Abbr `t`,input_stores_lookup_idx] >> first_assum ACCEPT_TAC
QED

Finalise ecrecover_input_stores_physical_mods
