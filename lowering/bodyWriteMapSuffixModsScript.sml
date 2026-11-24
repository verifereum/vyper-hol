(* Join the physical runs for a reached mapping key, at its original floor. *)
Theory bodyWriteMapSuffixMods
Ancestors
  bodyWriteMapScratchAllocMods bodyWriteMapScratchTailMods bodyWriteMapKeyPrefixMods
  bodyFullTargetMappingRun bodyFullTargetMappingScratch bodyFullTargetMappingKey
  targetSubscriptMapping bodyFullPostsMods bodyInvSplit
  exprSimMapKey exprSimWordArgs exprOperandVar exprLoweringProps
  bodyPtrDefs loweringPosts fragGasOriginPtrLoop fragGasOriginPtr
  loweringStateRelDefs bodyMemoryDefs allocaHistory venomMemDefs ptrDiscipline
  loweringHalt emitHelperProps emitHelper context compileEnv ASCIInumbers pair
  venomState venomInst venomExecSemantics fragExec finite_map words pred_set list

Theorem map_scratch_compile_shape[local]:
  compile_mapping_subscript bop key sa = (slot,sb) ==>
  ?buf sm q h code.
    compile_alloc_buffer 64 sa = (buf,sm) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    q = STRING #"%" (toString sm.cs_next_var) /\
    h = STRING #"%" (toString (sm.cs_next_var+1)) /\
    slot = Var h /\ sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ code /\
    code = [mk_inst sm.cs_next_id MSTORE [buf.buf_operand;bop] [];
            mk_inst (sm.cs_next_id+1) ADD [buf.buf_operand;Lit 32w] [q];
            mk_inst (sm.cs_next_id+2) MSTORE [Var q;key] [];
            mk_inst (sm.cs_next_id+3) SHA3 [buf.buf_operand;Lit 64w] [h]]
Proof
  strip_tac >> drule_then strip_assume_tac compile_mapping_subscript_parts >>
  rename1 `compile_alloc_buffer 64 sa = (buf,sm)` >>
  rename1 `emit_void MSTORE _ sm = ((),s1)` >>
  rename1 `emit_op ADD _ s1 = (_,s2)` >>
  rename1 `emit_void MSTORE _ s2 = ((),s3)` >>
  `ci_mono sa sm /\ ci_mono sm s1 /\ ci_mono s1 s2 /\
   ci_mono s2 s3 /\ ci_mono s3 sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_emit_op, SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_trans] >>
  qexistsl_tac [`buf`,`sm`] >> simp[] >>
  qpat_assum `emit_void MSTORE _ sm = _` mp_tac >>
  qpat_assum `emit_op ADD _ s1 = _` mp_tac >>
  qpat_assum `emit_void MSTORE _ s2 = _` mp_tac >>
  qpat_assum `emit_op SHA3 _ s3 = _` mp_tac >>
  simp_tac (srw_ss()) [emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem map_suffix_operand_frame[local]:
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ op_taint tt (Var x) = op_taint ts (Var x)) /\
  t.vs_labels = s.vs_labels ==>
  eval_operand op t = eval_operand op s /\ op_taint tt op = op_taint ts op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_taint_def] >> metis_tac[]
QED

Theorem map_slot_run_mods[local]:
  compile_mapping_subscript bop key sa = (slot,sb) /\
  (!x. bop = Var x \/ key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ (?H. P H) /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand slot t = SOME (hashmap_slot w0 w1) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sa s t /\ ghost_kept_at lo cenv es sa G tn s HG tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
       stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t /\
       ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >> drule_then strip_assume_tac map_scratch_compile_shape >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `?J. P J` suffices_by
    (disch_tac >> drule_all mapping_scratch_alloc_run_mods >>
     disch_then (qspecl_then [`explicit`,`PG`]
       (qx_choosel_then [`p`,`b`,`a`,`Ga`,`tna`,`raw`] strip_assume_tac)) >>
     suspend "scratch") >>
  qexists_tac `H` >> first_assum ACCEPT_TAC
QED

Resume map_slot_run_mods[scratch]:
  `!x. not_fresh_at sm x ==> x <> q /\ x <> h` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD,
                                    arithmeticTheory.LESS_EQ_REFL]) >>
  `ALL_DISTINCT [p;q;h]` by
    (simp[ALL_DISTINCT, toString_inj] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[] >>
  `a.vs_labels = s.vs_labels /\ a.vs_memory = s.vs_memory` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
          vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_labels,z.vs_memory)`) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x a = lookup_var x s /\ op_taint tna (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
         (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!x. key = Var x ==> x <> q` by metis_tac[] >>
  `eval_operand bop a = eval_operand bop s /\ op_taint tna bop = op_taint tn bop` by
    (irule map_suffix_operand_frame >> conj_tac >-
       (qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[]) >>
  `eval_operand key a = eval_operand key s /\ op_taint tna key = op_taint tn key` by
    (irule map_suffix_operand_frame >> conj_tac >-
       (qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[]) >>
  `eval_operand bop a = SOME w0 /\ eval_operand key a = SOME w1 /\
   op_taint tna bop = {} /\ op_taint tna key = {}` by simp[] >>
  `code = [mk_inst sm.cs_next_id MSTORE [Var p;bop] [];
           mk_inst (sm.cs_next_id+1) ADD [Var p;Lit 32w] [q];
           mk_inst (sm.cs_next_id+2) MSTORE [Var q;key] [];
           mk_inst (sm.cs_next_id+3) SHA3 [Var p;Lit 64w] [h]]` by simp[] >>
  `(mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]).inst_opcode = ALLOCA /\
   FLOOKUP a.vs_allocas (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]).inst_id = SOME (b,64)` by
    (simp_tac (srw_ss()) [mk_inst_def] >> first_assum ACCEPT_TAC) >>
  `b <= b /\ b+64 <= b+64` by simp[] >>
  drule_all mapping_scratch_tail_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`HG`,`tm`] strip_assume_tac)) >>
  suspend "tail_frames"
QED

Resume map_slot_run_mods[tail_frames]:
  `u with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory|> = a` by
    (drule_all_then ACCEPT_TAC mapping_scratch_runtime_restore) >>
  `~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o Q.AP_TERM `\r. (r.vs_halted,r.vs_current_bb)`) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
     FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ FLOOKUP _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!n off sz. local_region cenv es.scopes a n off sz <=>
     local_region cenv es.scopes s n off sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var z) k)` >>
     `not_fresh_at sa z` by
       (qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
        pure_rewrite_tac[local_ptrs_reserved_def] >> strip_tac >>
        qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP cenv.ce_vars n1 = _ ==> _`
          (drule_then (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL))) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!x. lookup_var x t = lookup_var x u` by simp[Abbr `t`, lookup_var_def] >>
  `t.vs_memory = u.vs_memory /\ t.vs_allocas = a.vs_allocas /\
   t.vs_alloca_next = a.vs_alloca_next /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[Abbr `t`] >>
  `eval_operand slot t = SOME (hashmap_slot w0 w1)` by
    (qpat_assum `slot = Var h` (fn th => rewrite_tac[th]) >>
     qpat_assum `eval_operand (Var h) u = _` mp_tac >>
     simp_tac (srw_ss()) [eval_operand_def, Abbr `t`, lookup_var_def]) >>
  `wb_frame cenv es es sa s t` by suspend "wb" >>
  `ghost_kept_at lo cenv es sa G tn s HG tm` by suspend "kept" >>
  `alloca_history func t` by suspend "history" >>
  `allocas_from lo t` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `op_taint tm slot = {} /\ op_prov HG slot = NONE` by
    (qpat_assum `slot = Var h` (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. lookup_var x t = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `t.vs_alloca_next = _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`HG`,`tm`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "counted"
QED

Resume map_slot_run_mods[wb]:
  rewrite_tac[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
        (drule_then strip_assume_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> _`
        (drule_then assume_tac) >>
      qpat_assum `t.vs_allocas = _` (fn th => rewrite_tac[th]) >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!aid a n. _ ==> regions_disjoint _ _ _ _`
        (drule_all_then mp_tac) >>
      simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM] >>
      disch_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
        (drule_then assume_tac) >> simp[]) >>
  irule exprSimPropsTheory.locals_kept_regions >> rpt strip_tac >>
  qpat_assum `!n off sz. local_region _ _ a _ _ _ <=> _`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  qpat_assum `!name a' n. local_region _ _ a _ _ _ ==> _` (drule_then assume_tac) >>
  qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
    (drule_then assume_tac) >> simp[]
QED
Resume map_slot_run_mods[kept]:
  `!i. i IN tm.t_mem /\ i < s.vs_alloca_next ==> i IN tn.t_mem` by
    (qpat_assum `tm = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [IN_DIFF] >>
     qpat_assum `!i. i IN tna.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> decide_tac) >>
  qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      off+sz <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
        (drule_then strip_assume_tac) >> conj_tac >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==> _`
        (drule_then assume_tac) >>
      `i < s.vs_alloca_next` by decide_tac >>
      qpat_assum `!i. i IN tm.t_mem /\ _ ==> _` (drule_all_then ACCEPT_TAC)) >>
  rpt strip_tac >> drule_all_then assume_tac body_local_region_frontier >>
  `i < s.vs_alloca_next` by decide_tac >>
  qpat_assum `!i. i IN tm.t_mem /\ _ ==> _` (drule_all_then ACCEPT_TAC)
QED
Resume map_slot_run_mods[history]:
  qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ a /\ _`
    (drule_then strip_assume_tac) >>
  `alloca_inv a` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ a` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by simp[mk_inst_def, is_terminator_def] >>
  simp_tac (srw_ss()) [Abbr `t`] >> irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`code`,`a`,`sm`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume map_slot_run_mods[counted]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ (a,Ga,tna) [] _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >-
    (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Ga`,`a`,`tna`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise map_slot_run_mods

Theorem map_key_compile_cut[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  (!x. key = Var x ==> not_fresh_at sn x) ==>
  ci_mono sn sp /\ sp.cs_current_bb = sn.cs_current_bb /\
  sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sp) /\
  (!x. hashed = Var x ==> not_fresh_at sp x)
Proof
  Cases_on `is_bytestring_type kt` >> simp[]
  >- (strip_tac >> drule_then strip_assume_tac
        (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
      conj_tac >- metis_tac[ci_mono_compile_keccak256_key, SND] >>
      fs[same_blocks_def, EVERY_MEM]) >>
  strip_tac >> gvs[ci_mono_def, cs_extends_def, emitted_insts_def]
QED

Theorem mapping_suffix_run_mods:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  (!x. key = Var x \/ bop = Var x ==> not_fresh_at sn x) /\
  (if is_bytestring_type kt then
     ?x b base cap bs.
       key = Var x /\ eval_operand key s = SOME (n2w b) /\
       FLOOKUP G x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= s.vs_alloca_next /\
       op_taint tn key = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
       mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand key s = SOME (encode_hashmap_key kt v) /\
        op_taint tn key = {} /\ op_prov G key = NONE) /\
  eval_operand bop s = SOME base_slot /\ op_taint tn bop = {} /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sn s t /\ ghost_kept_at lo cenv es sn G tn s HG tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t /\
      ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >>
  `!x. key = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  drule_all_then strip_assume_tac map_key_compile_cut >>
  `ci_mono sp sb` by metis_tac[ci_mono_compile_mapping_subscript, SND] >>
  `fn_has_code sn sp func /\ fn_has_code sp sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\
    immutable_frame_mods func cenv cx es s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all mapping_key_prefix_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  suspend "after_hash"
QED

Resume mapping_suffix_run_mods[after_hash]:
  `u.vs_labels = s.vs_labels /\ u.vs_memory = s.vs_memory /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   ~u.vs_halted /\ u.vs_current_bb = sp.cs_current_bb` by
    (qpat_assum `u with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\r. (r.vs_labels,r.vs_memory,r.vs_allocas,
                      r.vs_alloca_next,r.vs_halted,r.vs_current_bb)`) >> simp[]) >>
  qabbrev_tac `a = u with vs_inst_idx := LENGTH sp.cs_current_insts` >>
  `a.vs_labels = s.vs_labels /\ a.vs_memory = s.vs_memory /\
   a.vs_allocas = s.vs_allocas /\ a.vs_alloca_next = s.vs_alloca_next /\
   ~a.vs_halted /\ a.vs_current_bb = sp.cs_current_bb /\
   a.vs_inst_idx = LENGTH sp.cs_current_insts` by simp[Abbr `a`] >>
  `!x. lookup_var x a = lookup_var x u` by simp[Abbr `a`, lookup_var_def] >>
  `!x. not_fresh_at sn x ==> lookup_var x a = lookup_var x s /\
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x u = _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sn x ==> FLOOKUP Gu x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `eval_operand bop a = eval_operand bop s /\ op_taint tnu bop = op_taint tn bop` by
    (irule map_suffix_operand_frame >> conj_tac >-
       (qexists_tac `sn` >> simp[] >> metis_tac[]) >> first_assum ACCEPT_TAC) >>
  `eval_operand hashed a = SOME (encode_hashmap_key kt v)` by
    (qpat_assum `eval_operand hashed u = _` mp_tac >>
     Cases_on `hashed` >> simp_tac (srw_ss()) [eval_operand_def, Abbr `a`, lookup_var_def]) >>
  `eval_operand bop a = SOME base_slot /\ op_taint tnu bop = {}` by simp[] >>
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id` by
    fs[ci_mono_def, cs_extends_def] >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sn x ==> not_fresh_at sp x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC compiler_ci_mono_not_fresh) >>
  `(!x. bop = Var x \/ hashed = Var x ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    metis_tac[] >>
  `alloca_history func a` by suspend "prefix_history" >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es a /\
     immutable_frame_mods func cenv cx es a /\
     ghost_inv_at_mods (DF H) lo d cenv cx es Gu tnu a` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. P H ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?H. P H` suffices_by
    (disch_tac >> drule_all map_slot_run_mods >>
     disch_then (qspecl_then [`explicit`,`PG`]
       (qx_choosel_then [`t`,`HG`,`tm`] strip_assume_tac)) >>
     suspend "join") >>
  qexists_tac `H0` >> first_assum ACCEPT_TAC
QED

Resume mapping_suffix_run_mods[prefix_history]:
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [Abbr `a`] >> irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`emitted_insts sn sp`,`s`,`sn`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume mapping_suffix_run_mods[join]:
  `!x. slot = Var x ==> not_fresh_at sb x` by
    (drule_then strip_assume_tac target_mapping_suffix_shape >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> not_fresh_at sp x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sp x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `wb_frame cenv es es sn s a` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sn x ==> lookup_var x a = _ /\ _`
          (drule_then strip_assume_tac) >> simp[])
     >- simp[]
     >- simp[] >> irule exprSimPropsTheory.locals_kept_regions >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all_then strip_assume_tac mapping_suffix_frames_join >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `a.vs_alloca_next = s.vs_alloca_next` (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`HG`,`tm`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ (a,Gu,tnu) [] _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`a`,`tnu`] >>
               conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise mapping_suffix_run_mods
