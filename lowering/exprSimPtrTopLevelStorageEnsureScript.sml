(* Actual compiler allocation followed by its counted storage-copy suffix. *)
Theory exprSimPtrTopLevelStorageEnsure
Ancestors
  exprSimPtrTopLevelStorageAlloc exprSimPtrTopLevelStoragePost
  exprSimPtrTopLevelStorageCopy exprSimCopy exprSimAlloc
  exprSimPtrTopLevelStorageFrame exprSimUnwrap loweringHalt fragExec
  ghostPcTransportPtr fragGasPathPtr exprSimStorageCopy
  compileEnv context exprLoweringProps venomInst venomState words ptrDiscipline

Theorem toplevel_copy_alloc_taint_bound:
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\
  tna.t_mem SUBSET tn.t_mem UNION toplevel_copy_region b n ==>
  toplevel_copy_taint_bound loc a b tna n SUBSET
    toplevel_copy_taint_bound loc a b tn n
Proof
  simp[toplevel_copy_taint_bound_def, toplevel_copy_translated_taint_def,
    toplevel_copy_source_taint_def] >> SET_TAC[]
QED

Theorem toplevel_storage_ensure_ptr_semantic_effects:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ?u w.
      stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      sa.cs_next_id < sb.cs_next_id /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = sa.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_ensure_in_memory (Lit a) loc nb n ctor imm =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [Lit a];
             emit_void MSTORE [buf.buf_operand;v] od
        else do compile_word_copy_loop (Lit a) buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand od` by
    (irule ensure_storage_memory_layout >> simp[]) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ sa = _` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `compile_alloc_buffer (32*n) sa` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  drule_all (SRULE[comp_ignore_bind_def] storage_copy_suffix_extends) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qpat_x_assum `q.buf_operand = op /\ _` strip_assume_tac >> gnvs[] >>
  `n < 2**256` by (fs[dimword_def] >> decide_tac) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH r.cs_current_insts` >>
  `eval_operand (Lit a) s1 = SOME a /\ op_taint tnf (Lit a) = {} /\
   lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n) /\
   w2n w+32*n < 2**256 /\ w2n w+32*n <= s1.vs_alloca_next /\
   ~s1.vs_halted /\ s1.vs_current_bb = r.cs_current_bb /\
   s1.vs_inst_idx = LENGTH r.cs_current_insts` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, op_taint_def, dimword_def] >>
  `w = n2w (w2n w)` by simp[] >>
  `lookup_var p s1 = SOME (n2w (w2n w))` by metis_tac[] >>
  `32*n <= 32*n /\ (!x. Lit a = Var x ==> not_fresh_at r x)` by simp[] >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] toplevel_copy_suffix_post_effects) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u` by
    (`copy_static s1 = copy_static u` by simp[Abbr `s1`, copy_static_def] >>
     `!z. copy_runtime_word loc s1 z = copy_runtime_word loc u z` by
       metis_tac[copy_runtime_word_static] >>
     qpat_x_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     simp[copy_prefix_def, Abbr `s1`] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at r x` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> drule storage_copy_alloc_layout >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `lookup_var p t = SOME w` by
    (qpat_x_assum `!x. not_fresh_at r x ==> _` drule >>
     simp[Abbr `s1`, lookup_var_def]) >>
  `toplevel_copy_taint_bound loc a (w2n w) tnf n SUBSET
    toplevel_copy_taint_bound loc a (w2n w) tn n` by
    (irule toplevel_copy_alloc_taint_bound >>
     simp[toplevel_copy_region_def]) >>
  `tnf'.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n` by
    metis_tac[pred_setTheory.SUBSET_TRANS] >>
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry)` by
    (drule_all toplevel_alloc_buffer_static_effects >> simp[]) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_allocas = u.vs_allocas` by
    metis_tac[copy_static_fields] >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory` by fs[Abbr `s1`] >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (drule_all buffer_alloc_code >> strip_tac >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `sa.cs_next_id < cs'.cs_next_id` by
    (`32*n < dimword (:256)` by decide_tac >>
     drule_all (REWRITE_RULE[comp_ignore_bind_def] storage_copy_suffix_ci_mono) >> strip_tac >>
     drule_all buffer_alloc_code >> strip_tac >>
     drule_all literal_alloc_buffer_run >> strip_tac >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `Gf'`, `tnf'`] >> simp[] >>
  qexists_tac `u` >>
  simp[] >>
  rpt conj_tac
  >- fs[eval_operand_def, lookup_var_def]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      fs[Abbr `s1`, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem toplevel_storage_ensure_ptr_effects:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ?u w.
      stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      sa.cs_next_id < sb.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_storage_ensure_ptr_semantic_effects >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[] >>
  qexists_tac `u` >> gvs[] >> metis_tac[]
QED

Theorem toplevel_storage_ensure_ptr_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ?u w.
      stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_storage_ensure_ptr_effects >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[] >>
  qexists_tac `u` >> gvs[] >> metis_tac[]
QED
