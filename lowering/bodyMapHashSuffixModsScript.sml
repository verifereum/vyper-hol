(* Composition of the key prehash, slot allocation and slot hash. *)
Theory bodyMapHashSuffixMods
Ancestors
  bodyMapKeyPrefixMods bodyMapSlotAllocMods bodyMapScratchStoresMods
  bodyFullUnwrapRun bodyFullHashKeccakFixed bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrDefs bodyMemoryDefs loweringPosts loweringStateRelDefs exprLoweringProps
  stateRelProj exprOperandVar exprSimProps exprSimWordArgs exprSimMapKey targetSubscriptMapping loweringHalt
  compileEnv emitHelper freshWrites venomInst venomState ptrDiscipline
  fragExec fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath words pred_set finite_map rich_list list ASCIInumbers pair

Theorem slot_tail_code[local]:
  emit_void MSTORE [Var p;bop] sm = ((),sn) /\
  emit_op ADD [Var p;Lit 32w] sn = (tmp,sp) /\
  emit_void MSTORE [tmp;key] sp = ((),sq) /\
  emit_op SHA3 [Var p;Lit 64w] sq = (op,sb) ==>
  ?q h code.
    op = Var h /\
    code = [mk_inst sm.cs_next_id MSTORE [Var p;bop] [];
            mk_inst (sm.cs_next_id+1) ADD [Var p;Lit 32w] [q];
            mk_inst (sm.cs_next_id+2) MSTORE [Var q;key] [];
            mk_inst (sm.cs_next_id+3) SHA3 [Var p;Lit 64w] [h]] /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ code /\
    q <> h /\ (!x. not_fresh_at sm x ==> x <> q /\ x <> h)
Proof
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[APPEND_ASSOC] >>
  qexists_tac `STRING #"%" (toString sm.cs_next_var)` >>
  simp[not_fresh_at_def, toString_inj] >> qexists_tac `sm.cs_next_var` >> simp[]
QED

Theorem slot_tail_frames[local]:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
             FLOOKUP t.vs_allocas aid = SOME ent) /\
  (!a n. a+n <= b \/ b+64 <= a ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!name a n. local_region cenv es.scopes s name a n ==> a+n <= b \/ b+64 <= a) /\
  (!aid a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
             regions_disjoint b 64 a n) /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ sa.cs_next_id <= ai.inst_id /\
  FLOOKUP t.vs_allocas ai.inst_id = SOME (b,64) ==>
  wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t
Proof
  strip_tac >> simp[wb_frame_def, pure_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >>
      qpat_assum `!aid a n. aid < _ /\ FLOOKUP _ aid = _ ==> _`
        (drule_all_then mp_tac) >> simp[regions_disjoint_def, DISJ_COMM])
  >- (irule locals_kept_regions >> simp[] >> metis_tac[])
  >- metis_tac[] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[regions_disjoint_def]
QED

Theorem slot_kept_sub_mem[local]:
  ghost_kept_at lo cenv es sa G tn s Ga tna /\
  (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tm.t_mem ==> i IN tna.t_mem) ==>
  ghost_kept_at lo cenv es sa G tn s HG tm
Proof
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Theorem mapping_slot_hash_run_mods[local]:
  compile_mapping_subscript bop key sa = (slot,sb) /\
  (!x. bop = Var x \/ key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
      immutable_frame_mods func cenv cx es s /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand slot t = SOME (hashmap_slot w0 w1) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t /\
      ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >> drule_then strip_assume_tac compile_mapping_subscript_parts >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sm sb` by
    (irule ci_mono_trans >> qexists_tac `sp` >>
     metis_tac[ci_mono_emit_void, ci_mono_emit_op, ci_mono_trans, SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def, cs_extends_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all mapping_slot_alloc_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`w`,`a`,`Ga`,`tna`] strip_assume_tac)) >>
  gvs[] >> drule_all_then strip_assume_tac slot_tail_code >>
  suspend "tail"
QED

Resume mapping_slot_hash_run_mods[tail]:
  `ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q)` by
    (simp[ALL_DISTINCT] >> metis_tac[]) >>
  `a.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK a,Ga,tna)`
       (qspec_then `DF H0` (mp_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
     strip_tac >> drule gas_origin_path_erase >>
     disch_then (mp_tac o MATCH_MP gas_marked_path_exec) >>
     disch_then (mp_tac o MATCH_MP gas_path_labels) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
        eval_operand op a = eval_operand op s /\ op_taint tna op = op_taint tn op` by
    (Cases >> simp[eval_operand_def, op_taint_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
        (drule_then strip_assume_tac) >> fs[lookup_var_def, op_taint_def]) >>
  `eval_operand bop a = SOME w0 /\ eval_operand key a = SOME w1 /\
    op_taint tna bop = {} /\ op_taint tna key = {}` by
    (qpat_assum `!op. _ ==> eval_operand op a = _ /\ _`
       (fn th => mp_tac (Q.SPEC `bop` th) >> mp_tac (Q.SPEC `key` th)) >> simp[]) >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by metis_tac[] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by metis_tac[] >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]` >>
  `MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = sa.cs_next_id /\
    FLOOKUP a.vs_allocas ai.inst_id = SOME (w2n w,64)` by simp[Abbr `ai`, mk_inst_def] >>
  `key <> Var q` by metis_tac[] >>
  `lo <= a.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`is` |-> `sm.cs_next_id`, `ip` |-> `sm.cs_next_id+1`,
                  `ik` |-> `sm.cs_next_id+2`, `ih` |-> `sm.cs_next_id+3`,
                  `root` |-> `w2n (w:bytes32)`, `b` |-> `w2n (w:bytes32)`, `cap` |-> `64`,
                  `s` |-> `a`, `sa` |-> `sm`, `G` |-> `Ga`, `tn` |-> `tna`]
    mapping_scratch_tail_full_run_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`raw`,`HG`,`tm`] strip_assume_tac) >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "frames"
QED

Resume mapping_slot_hash_run_mods[frames]:
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by simp[] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x raw = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> fs[Abbr `t`, lookup_var_def]) >>
  `!name b n. local_region cenv es.scopes s name b n <=>
              local_region cenv es.scopes a name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t` by
    (irule slot_tail_frames >> simp[Abbr `t`] >>
     qexistsl_tac [`ai`,`w2n (w:bytes32)`] >> asm_rewrite_tac[] >> simp[] >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n raw.vs_memory = _` mp_tac >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s HG tm` by
    (`!i. i IN tm.t_mem ==> i IN tna.t_mem` by simp[pred_setTheory.IN_DIFF] >>
     irule slot_kept_sub_mem >> simp[] >>
     qexistsl_tac [`Ga`,`tna`] >> simp[]) >>
  `alloca_inv a` by
    (qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ a /\ _`
      (qspec_then `H0` mp_tac) >> simp[] >> metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by simp[mk_inst_def, is_terminator_def] >>
  `alloca_history func t` by
    (simp[NoAsms, Abbr `t`] >> irule emitted_alloca_history >>
     simp[] >> qexistsl_tac [`code`,`a`,`sm`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`,`HG`,`tm`] >>
  `raw.vs_current_bb = a.vs_current_bb` by
    (qpat_assum `raw with <|vs_vars := _; vs_memory := _|> = a`
      (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. slot = Var x ==> not_fresh_at sb x` by
    (drule target_mapping_suffix_shape >> simp[]) >>
  `eval_operand slot t = SOME (hashmap_slot w0 w1)` by
    fs[Abbr `t`, eval_operand_def, lookup_var_def] >>
  `allocas_from lo t` by
    (simp[Abbr `t`, allocas_from_def] >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s.vs_alloca_next <= t.vs_alloca_next` by simp[Abbr `t`] >>
  `!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t /\
      ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. P H ==> gas_origin_ptr_path _ (a,Ga,tna) _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >-
       (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
         (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
        disch_then (qspecl_then [`a`,`Ga`,`tna`,`[]`] mp_tac) >>
        simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `slot = Var h` SUBST_ALL_TAC >> asm_rewrite_tac[]
QED
Finalise mapping_slot_hash_run_mods

Theorem mapping_suffix_full_run_mods:
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
    wb_frame cenv es es sn s t /\ pure_frame cenv func es sn s t /\
    ghost_kept_at lo cenv es sn G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\
      immutable_frame_mods func cenv cx es t /\
      ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >>
  `ci_mono sn sp` by
    (Cases_on `is_bytestring_type kt`
     >- (gvs[] >> metis_tac[ci_mono_compile_keccak256_key, SND]) >>
     gvs[ci_mono_def, cs_extends_def]) >>
  `ci_mono sp sb` by metis_tac[ci_mono_compile_mapping_subscript, SND] >>
  `fn_has_code sn sp func /\ fn_has_code sp sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `!x. key = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  `!x. bop = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  `!x. not_fresh_at sn x ==> not_fresh_at sp x` by
    (rpt strip_tac >> drule_all compiler_ci_mono_not_fresh >> simp[]) >>
  `!x. bop = Var x \/ hashed = Var x ==> not_fresh_at sp x` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         strip_tac >> rpt strip_tac >> gvs[]) >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all mapping_key_prefix_full_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  suspend "slot"
QED

Resume mapping_suffix_full_run_mods[slot]:
  `sp.cs_current_bb = sn.cs_current_bb /\
   sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sp)` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         gvs[same_blocks_def, EVERY_MEM]) >> simp[emitted_insts_def]) >>
  qabbrev_tac `a = u with vs_inst_idx := LENGTH sp.cs_current_insts` >>
  `a.vs_current_bb = sp.cs_current_bb /\ a.vs_inst_idx = LENGTH sp.cs_current_insts /\
   a.vs_allocas = s.vs_allocas /\ a.vs_alloca_next = s.vs_alloca_next /\
   a.vs_memory = s.vs_memory /\ a.vs_labels = s.vs_labels /\ ~a.vs_halted` by
    (qpat_assum `u with vs_vars := _ = s` mp_tac >>
     simp[Abbr `a`, venom_state_component_equality]) >>
  `!x. not_fresh_at sn x ==> lookup_var x a = lookup_var x s` by
    (simp[NoAsms, Abbr `a`, lookup_var_def] >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x u = _`
       (ACCEPT_TAC o REWRITE_RULE[lookup_var_def])) >>
  `eval_operand bop a = SOME base_slot /\ op_taint tnu bop = {}` by
    (Cases_on `bop` >> fs[eval_operand_def, op_taint_def] >> metis_tac[lookup_var_def]) >>
  `eval_operand hashed a = SOME (encode_hashmap_key kt v)` by
    (Cases_on `hashed` >> fs[Abbr `a`, eval_operand_def, lookup_var_def]) >>
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id` by
    fs[ci_mono_def,cs_extends_def] >>
  `local_ptrs_reserved cenv sp` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sp x` by metis_tac[] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sp x` by metis_tac[] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history func a` by
    (simp[NoAsms, Abbr `a`] >> irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`emitted_insts sn sp`,`s`,`sn`] >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`sa` |-> `sp`, `key` |-> `hashed`, `s` |-> `a`,
                  `G` |-> `Gu`, `tn` |-> `tnu`,
                  `w0` |-> `base_slot:bytes32`, `w1` |-> `encode_hashmap_key kt v`]
    mapping_slot_hash_run_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. P H ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[])) >>
  disch_then (qx_choosel_then [`t`,`HG`,`tm`] strip_assume_tac) >>
  suspend "join"
QED

Resume mapping_suffix_full_run_mods[join]:
  `!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sp x` by simp[] >>
     qpat_assum `!x. not_fresh_at sp x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sn x ==> FLOOKUP Gu x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz <=> local_region cenv es.scopes a n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sn p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  `wb_frame cenv es es sn s a` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sn`,`s`] >> simp[wb_frame_refl]) >>
  `wb_frame cenv es es sn s t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`sp`,`a`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `pure_frame cenv func es sn s t` by
    (qpat_assum `pure_frame cenv func es sp a t` mp_tac >>
     pure_rewrite_tac[pure_frame_def] >> disch_then strip_assume_tac >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `a.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
       qpat_assum `!n b sz. local_region _ _ a n b sz ==> _` irule >> metis_tac[]) >>
     rpt strip_tac >>
     qpat_assum `a.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
     rpt strip_tac >> first_x_assum irule >> qexists_tac `inst` >> simp[] >> decide_tac) >>
  `ghost_kept_at lo cenv es sn G tn s HG tm` by
    (qpat_assum `ghost_kept_at lo cenv es sp Gu tnu a HG tm` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then strip_assume_tac >>
     rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sn x ==> lookup_var x t = _ /\ _`
           (drule_then strip_assume_tac) >> simp[])
     >- (rpt strip_tac >>
         qpat_assum `!aid off sz i. _ ==> i IN tnu.t_mem`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
         simp[] >> (impl_tac >- metis_tac[]) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!n b sz i. local_region _ _ a n b sz /\ _ ==> i IN tnu.t_mem`
       (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`t`,`HG`,`tm`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ (a,Gu,tnu) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
      (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`a`,`Gu`,`tnu`,`[]`] mp_tac) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise mapping_suffix_full_run_mods
