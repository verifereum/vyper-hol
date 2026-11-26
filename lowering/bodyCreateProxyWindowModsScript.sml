(* The allocation and writes land at a single registered proxy window. *)
Theory bodyCreateProxyWindowMods
Ancestors
  bodyCreateProxyAllocationCutMods bodyCreateProxyWritesMods
  bodyCreateProxyRegisteredFrameMods bodyFullPathHistory stateRelProj
  fragGasOriginPtrLoop stmtFragPtr builtinCreate emitHelper fragExec
  loweringStateRelDefs loweringPosts bodyPtrDefs ptrDiscipline
  venomInst venomState venomExecSemantics finite_map pred_set words list

Theorem create_proxy_window_mods:
  compile_create_proxy_buf target sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME word /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) ==>
  ?p w t Gf tf.
    buf = Var p /\ not_fresh_at sb p /\ sa.cs_next_id < sb.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    lo <= w2n w /\ w2n w + 96 < dimword (:256) /\ w2n w + 96 <= t.vs_alloca_next /\
    lookup_var p t = SOME w /\ ptr_covers Gf tf p t 96 /\
    FLOOKUP Gf p = SOME (w2n w,96) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,96) /\
    (!name b n. local_region cenv es.scopes t name b n ==> regions_disjoint (w2n w) 96 b n) /\
    read_memory (w2n w) 54 t = minimal_proxy_initcode (w2w word) /\
    (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tf.t_mem) /\
    (!H':(bool # bytes32 # type_value) list # num list.
       stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t) /\
    wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
    (!D d. ghost_inv_at_mods D lo d cenv cx es G tn s /\
           immutable_frame_mods func cenv cx es s ==>
           ghost_inv_at_mods D lo d cenv cx es Gf tf t /\
           immutable_frame_mods func cenv cx es t /\
           ghost_kept_at lo cenv es sa G tn s Gf tf) /\
    (!sk es0 G0 tn0 s0. sk.cs_next_var <= sa.cs_next_var /\
      (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sk.cs_next_id ==>
                   b + n <= s.vs_alloca_next) /\
      (!name b n. local_region cenv es0.scopes s0 name b n ==> b + n <= s.vs_alloca_next) /\
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gf tf) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_proxy_allocation_cut_mods >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`m1`,`m2`,`m3`,`m4`,`aligned`,`p`,`w`,`u`,`Ga`,`ta`] strip_assume_tac)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at m1 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
                         vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand target u = SOME word /\ op_taint ta target = {} /\
   (!x. target = Var x ==> not_fresh_at m1 x)` by
    (Cases_on `target` >> fs[eval_operand_def,op_taint_def] >>
     qpat_assum `!z. not_fresh_at sa z ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all create_proxy_writes_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`p`,`w`,`t`,`Gf`,`tf`] >>
  suspend "frame"
QED

Resume create_proxy_window_mods[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >> simp[]) >>
  `!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (simp[IN_DIFF] >> decide_tac) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by simp[] >>
  `!x. not_fresh_at m1 x ==> lookup_var x t = lookup_var x u` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Ga`,`u`,`ta`] >> simp[]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tf)`
      (qspec_then `ARB` assume_tac) >> drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  suspend "registered"
QED

Resume create_proxy_window_mods[registered]:
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit 96w] [p]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`,mk_inst_def] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,96)` by simp[] >>
  drule_all create_proxy_registered_frame_mods >> strip_tac >>
  suspend "pack"
QED

Resume create_proxy_window_mods[pack]:
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_fmp = u.vs_fmp /\ t.vs_initial_fmp = u.vs_initial_fmp` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
      (SUBST1_TAC o SYM) >> simp[]) >>
  `allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (pure_rewrite_tac[allocas_from_def,allocas_below_fmp_def] >>
     qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
       (mp_tac o REWRITE_RULE[allocas_below_fmp_def]) >>
     asm_rewrite_tac[] >> rpt disch_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `m1` >> simp[] >> decide_tac) >>
  `FLOOKUP Gf p = SOME (w2n w,96)` by
    (qpat_assum `!y. not_fresh_at m1 y ==> _ /\ FLOOKUP Gf y = _ /\ _`
      (qspec_then `p` mp_tac) >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tf.t_mem` by
    (simp[IN_DIFF] >> decide_tac) >>
  asm_rewrite_tac[] >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE (rpt gen_tac >> first_assum irule >> first_assum ACCEPT_TAC))
QED

Finalise create_proxy_window_mods
