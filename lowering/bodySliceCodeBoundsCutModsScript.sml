(* Successful scalar bounds cut after a linked code-size landing. *)
Theory bodySliceCodeBoundsCutMods
Ancestors
  bodyFullBuiltinBytestringBounds bodyPtrBytestringBuiltinsBounds
  bodyFullUnwrapRun exprSimProps exprLoweringProps bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrDefs fragExec ptrDiscipline venomState venomInst freshWrites list words

Theorem slice_code_bounds_cut_mods:
  compile_assert_slice_bounds start cnt limit sc = ((),sd) /\
  fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ alloca_history func zq /\ alloca_inv zq /\
  allocas_from lo zq /\ lo <= zq.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp zq) /\ ~zq.vs_halted /\
  zq.vs_current_bb = sc.cs_current_bb /\
  zq.vs_inst_idx = LENGTH sc.cs_current_insts /\
  zq = s with <|vs_vars := zq.vs_vars;
                  vs_inst_idx := LENGTH sc.cs_current_insts|> /\
  eval_operand start zq = SOME (n2w i) /\
  eval_operand cnt zq = SOME (n2w k) /\
  eval_operand limit zq = SOME (n2w (LENGTH code)) /\
  (!op. MEM op [start;cnt;limit] ==>
    op_prov Gq op = NONE /\ op_taint tq op = {} /\
    (!x. op = Var x ==> not_fresh_at sc x)) /\
  i < dimword (:256) /\ k < dimword (:256) /\
  LENGTH code < dimword (:256) /\ i+k <= LENGTH code /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  tq.t_mem = tn.t_mem /\ tq.t_stor = tn.t_stor /\
  tq.t_trans = tn.t_trans /\ tq.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x zq = lookup_var x s /\
    FLOOKUP Gq x = FLOOKUP G x /\
    op_taint tq (Var x) = op_taint tn (Var x)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK zq,Gq,tq)) ==>
  ?zb Gb tb.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK zb,Gb,tb)) /\
    zb = s with <|vs_vars := zb.vs_vars;
                    vs_inst_idx := LENGTH sd.cs_current_insts|> /\
    zb.vs_current_bb = sd.cs_current_bb /\
    zb.vs_inst_idx = LENGTH sd.cs_current_insts /\
    ~zb.vs_halted /\ alloca_history func zb /\
    allocas_from lo zb /\ lo <= zb.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp zb) /\
    (s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp ==>
      zb.vs_alloca_next + pending_alloca_size func zb <= w2n zb.vs_initial_fmp) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x zb = lookup_var x s /\
      FLOOKUP Gb x = FLOOKUP G x /\
      op_taint tb (Var x) = op_taint tn (Var x)) /\
    tb.t_mem = tn.t_mem /\ tb.t_stor = tn.t_stor /\
    tb.t_trans = tn.t_trans /\ tb.t_imm = tn.t_imm /\
    (!H:(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es zb) /\
    sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
    local_ptrs_reserved cenv sd /\
    (!x. not_fresh_at sa x ==> not_fresh_at sd x) /\
    (!op. MEM op [start;cnt;limit] ==>
      eval_operand op zb = eval_operand op zq /\
      op_prov Gb op = NONE /\ op_taint tb op = {}) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op zb = eval_operand op s /\ op_prov Gb op = op_prov G op /\
      op_taint tb op = op_taint tn op)
Proof
  strip_tac >>
  `!op x. MEM op [start;cnt;limit] /\ op = Var x ==>
    not_fresh_at sc x` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then strip_assume_tac slice_bounds_reserved_natural_runtime >>
  `i+k < dimword (:256)` by decide_tac >>
  `~(dimword (:256) <= i+k) /\ ~(LENGTH code < i+k)` by decide_tac >>
  `run_inst_seq (emitted_insts sc sd) zq = OK p` by simp[] >>
  drule_all bytestring_slice_bounds_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `Gb` (qx_choose_then `tb` strip_assume_tac))) >>
  qabbrev_tac `zb = p with vs_inst_idx := LENGTH sd.cs_current_insts` >>
  `p with vs_inst_idx := LENGTH sd.cs_current_insts =
      zq with <|vs_vars := p.vs_vars;
                  vs_inst_idx := LENGTH sd.cs_current_insts|>` by
    (qpat_assum `p = zq with vs_vars := p.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sd.cs_current_insts`) >>
     simp[]) >>
  `zq with <|vs_vars := p.vs_vars;
              vs_inst_idx := LENGTH sd.cs_current_insts|> =
      s with <|vs_vars := p.vs_vars;
                vs_inst_idx := LENGTH sd.cs_current_insts|>` by
    (qpat_assum `zq = s with <|vs_vars := zq.vs_vars;
        vs_inst_idx := LENGTH sc.cs_current_insts|>`
       (mp_tac o Q.AP_TERM
         `\st. st with <|vs_vars := p.vs_vars;
                          vs_inst_idx := LENGTH sd.cs_current_insts|>`) >>
     simp[]) >>
  `zb = s with <|vs_vars := zb.vs_vars;
      vs_inst_idx := LENGTH sd.cs_current_insts|>` by
    (qunabbrev_tac `zb` >>
     qpat_assum `p with vs_inst_idx := LENGTH sd.cs_current_insts =
       zq with <|vs_vars := p.vs_vars;
                    vs_inst_idx := LENGTH sd.cs_current_insts|>`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `zq with <|vs_vars := p.vs_vars;
                    vs_inst_idx := LENGTH sd.cs_current_insts|> =
       s with <|vs_vars := p.vs_vars;
                  vs_inst_idx := LENGTH sd.cs_current_insts|>`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK zb,Gb,tb)` by
    (gen_tac >> qunabbrev_tac `zb` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zq,Gq,tq) _ _`
       (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,
               listTheory.APPEND_NIL]) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x zb = lookup_var x s /\
      FLOOKUP Gb x = FLOOKUP G x /\
      op_taint tb (Var x) = op_taint tn (Var x)` by
    (qunabbrev_tac `zb` >>
     rpt strip_tac >>
     fs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `alloca_history func zb` by
    (simp[Abbr `zb`] >>
     qspecl_then [`emitted_insts sc sd`,`sc`,`sd`,`zq`,`p`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     (impl_tac >-
       (qpat_assum `compile_assert_slice_bounds _ _ _ sc = _`
          (mp_then Any strip_assume_tac
            bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >>
        qpat_assum `same_blocks sc sd`
          (strip_assume_tac o REWRITE_RULE[exprLoweringPropsTheory.same_blocks_def]) >>
        simp[venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def])) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x (s with vs_vars := zb.vs_vars) = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = lookup_var x s /\ _`
       (qspec_then `x` (mp_tac o REWRITE_RULE[venomStateTheory.lookup_var_def])) >>
     simp[venomStateTheory.lookup_var_def]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es zb` by
    (rpt strip_tac >>
     qpat_assum `zb = s with <|vs_vars := zb.vs_vars;
        vs_inst_idx := LENGTH sd.cs_current_insts|>` SUBST1_TAC >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==>
       lookup_var x (s with vs_vars := zb.vs_vars) = lookup_var x s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     fs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `allocas_from lo zb /\ lo <= zb.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp zb) /\ ~zb.vs_halted` by
    (qunabbrev_tac `zb` >>
     qpat_assum `p = zq with vs_vars := p.vs_vars` SUBST1_TAC >>
     qpat_assum `allocas_from lo zq` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp zq` mp_tac >>
     qpat_assum `lo <= zq.vs_alloca_next` mp_tac >>
     qpat_assum `~zq.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptrDisciplineTheory.allocas_from_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
     metis_tac[]) >>
  `s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp ==>
   zb.vs_alloca_next + pending_alloca_size func zb <= w2n zb.vs_initial_fmp` by
    (qpat_assum `zb = s with <|vs_vars := zb.vs_vars;
        vs_inst_idx := LENGTH sd.cs_current_insts|>` SUBST1_TAC >>
     simp[exprLoweringPropsTheory.pending_alloca_size_def]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    (qpat_assum `compile_assert_slice_bounds _ _ _ sc = _`
       (mp_then Any strip_assume_tac
         bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >>
     simp[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `zb.vs_current_bb = sd.cs_current_bb /\
   zb.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~zb.vs_halted` by
    simp[Abbr `zb`] >>
  `zb.vs_labels = s.vs_labels` by
    (qpat_assum `zb = s with <|vs_vars := zb.vs_vars;
        vs_inst_idx := LENGTH sd.cs_current_insts|>` SUBST1_TAC >> simp[]) >>
  `zb.vs_labels = zq.vs_labels` by
    (qpat_assum `zq = s with <|vs_vars := zq.vs_vars;
        vs_inst_idx := LENGTH sc.cs_current_insts|>` SUBST1_TAC >> simp[]) >>
  `!x. not_fresh_at sc x ==>
      lookup_var x zb = lookup_var x zq /\ FLOOKUP Gb x = FLOOKUP Gq x /\
      op_taint tb (Var x) = op_taint tq (Var x)` by
    (qunabbrev_tac `zb` >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x p = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venomStateTheory.lookup_var_def]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sc x) ==>
      eval_operand op zb = eval_operand op zq /\ op_prov Gb op = op_prov Gq op /\
      op_taint tb op = op_taint tq op` by
    (match_mp_tac reserved_operand_ghost_frame >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!op. MEM op [start;cnt;limit] ==>
      eval_operand op zb = eval_operand op zq /\
      op_prov Gb op = NONE /\ op_taint tb op = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _`
       (qspec_then `op` (drule_then strip_assume_tac)) >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sc x) ==>
       eval_operand op zb = eval_operand op zq /\ _`
       (qspec_then `op` (drule_then strip_assume_tac)) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op zb = eval_operand op s /\ op_prov Gb op = op_prov G op /\
      op_taint tb op = op_taint tn op` by
    (match_mp_tac reserved_operand_ghost_frame >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`zb`,`Gb`,`tb`] >> simp[]
QED
