(* Operand-generic checked copies from memory into storage slots.
   store_copy_frame records the exact functional update, restoring only
   variables and control cursors; no semantic endpoint is chosen separately. *)
Theory bodyMemStorageCopyStage
Ancestors
  bodyMemAssignTopCopySuffix bodyMemAssignTopCopyPaths
  bodyMemAssignTopCopyCompiler stmtSimStoreCopy allocaHistory
  fragGasMode venomState venomInst allocaHistoryFragment rich_list

Theorem storage_copy_loop_stage_mem:
  !ctx func loc src dst n sa u sb s b k.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
    fn_has_code sa sb func /\ n < dimword (:256) /\
    w2n b + 32*n <= s.vs_alloca_next /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ alloca_history func s /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      t.vs_call_ctx = s.vs_call_ctx /\ alloca_history func t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_compile_loop_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (fs[store_copy_frame_def] >>
     drule topcopy_normalize_allocations >> simp[]) >>
  `sb.cs_current_insts = []` by
    (drule_all topcopy_code_certificate >> simp[] >> metis_tac[]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[topcopy_frame_memory, topcopy_frame_labels, topcopy_frame_call_ctx]
QED

Theorem storage_copy_singleton_stage_mem:
  !loc src dst s b k out id ctx func bb.
    (loc = LocStorage \/ loc = LocTransient) /\
    eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
    (!x. dst = Var x ==> x <> out) /\ ~s.vs_call_ctx.cc_static /\
    ~s.vs_halted /\ w2n b + 32 <= s.vs_alloca_next /\
    alloca_history func s /\ alloca_inv s /\ fn_inst_ids_distinct func /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst id MLOAD [src] [out];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [dst; Var out] []] (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        (if loc = LocStorage then sstore else tstore) k (mload (w2n b) s) s /\
      (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 2 /\ ~t.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `dst <> Var out` by metis_tac[] >>
  qspecl_then [`loc`, `src`, `dst`, `s`, `b`, `k`, `out`, `id`]
    mp_tac topcopy_singleton_run >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `run_inst_seq_mem_ok
      [mk_inst id MLOAD [src] [out];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [dst; Var out] []] s` by
    (irule bodyMemAssignTopCopyLoopTheory.body_mem_storage_singleton_mem_ok >>
     metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def])) >>
  strip_tac >>
  `alloca_history func (u with vs_inst_idx := s.vs_inst_idx + 2)` by
    (qpat_x_assum `isPREFIX _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     drule_at (Pat `run_inst_seq _ _ = _`) alloca_history_run_inst_seq >>
     disch_then (qspecl_then [`func`, `bb`] mp_tac) >>
     Cases_on `loc = LocStorage` >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `store_copy_normalize _ _ = _`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_allocas,z.vs_alloca_next)``) >>
     Cases_on `loc = LocStorage` >>
     simp[store_copy_normalize_def, sstore_def, tstore_def]) >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 2` >>
  gvs[lookup_var_def]
QED
