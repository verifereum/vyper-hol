(* The allocation cut of a minimal proxy, before any writes to its buffer. *)
Theory bodyCreateProxyAllocationCutMods
Ancestors
  bodyFullAllocaFresh bodyFullHashKeccakFixed[qualified]
  builtinCreate emitHelper emitHelperProps fragExec abiBuiltinAllocation
  exprSimAlloc exprLoweringProps loweringStateRelDefs ptrDiscipline
  fragGasOriginPtr venomExecSemantics venomState venomInst finite_map
  words pred_set list compileEnv context

Theorem proxy_allocation_parts[local]:
  compile_create_proxy_buf target sa = (buf,sb) ==>
  ?allocation m1 m2 aligned m3 m4.
    compile_alloc_buffer 96 sa = (allocation,m1) /\
    buf = allocation.buf_operand /\
    emit_void MSTORE [buf;
      Lit 0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w]
      m1 = ((),m2) /\
    emit_op SHL [Lit 96w;target] m2 = (aligned,m3) /\
    (do dst <- emit_op ADD [buf;Lit 19w];
        emit_void MSTORE [dst;aligned] od) m3 = ((),m4) /\
    (do dst <- emit_op ADD [buf;Lit 39w];
        emit_void MSTORE [dst;
          Lit 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w]
     od) m4 = ((),sb) /\
    cs_extends sa m1 /\ cs_extends m1 m2 /\ cs_extends m2 m3 /\
    cs_extends m3 m4 /\ cs_extends m4 sb /\
    m1.cs_next_id = SUC sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sa.cs_next_var <= m1.cs_next_var /\ m1.cs_next_var <= m2.cs_next_var /\
    m2.cs_next_var <= m3.cs_next_var /\ m3.cs_next_var <= m4.cs_next_var /\
    m4.cs_next_var <= sb.cs_next_var
Proof
  simp[compile_create_proxy_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, cs_extends_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [compile_alloc_buffer_def, emit_op_def,
       emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM, pairTheory.UNCURRY]) >>
  gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.IS_PREFIX_APPENDS, compile_state_component_equality]
QED

Theorem proxy_allocation_subintervals[local]:
  cs_extends sa m1 /\ cs_extends m1 m2 /\ cs_extends m2 m3 /\
  cs_extends m3 m4 /\ cs_extends m4 sb /\ fn_has_code sa sb func ==>
  fn_has_code sa m1 func /\ fn_has_code m1 m2 func /\
  fn_has_code m2 m3 func /\ fn_has_code m3 m4 func /\ fn_has_code m4 sb func
Proof
  strip_tac >>
  `cs_extends m3 sb` by (irule cs_extends_trans >> qexists_tac `m4` >> simp[]) >>
  `cs_extends m2 sb` by (irule cs_extends_trans >> qexists_tac `m3` >> simp[]) >>
  `cs_extends m1 sb` by (irule cs_extends_trans >> qexists_tac `m2` >> simp[]) >>
  `fn_has_code sa m1 func /\ fn_has_code m1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code m1 m2 func /\ fn_has_code m2 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code m2 m3 func /\ fn_has_code m3 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code m3 m4 func /\ fn_has_code m4 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

Theorem proxy_alloca_old_or_above[local]:
  run_inst_seq [mk_inst id ALLOCA [Lit 96w] [p]] s = OK r ==>
  !aid a n. FLOOKUP r.vs_allocas aid = SOME (a,n) ==>
            FLOOKUP s.vs_allocas aid = SOME (a,n) \/ s.vs_alloca_next <= a
Proof
  simp[run_inst_seq_def, AllCaseEqs(), step_inst_base_opcode_eqs,
       mk_inst_def, eval_operand_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >>
  simp[AllCaseEqs(), update_var_def] >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem create_proxy_allocation_cut_mods:
  compile_create_proxy_buf target sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?m1 m2 m3 m4 aligned p w u Ga ta.
    buf = Var p /\ not_fresh_at m1 p /\
    emit_void MSTORE [Var p;
      Lit 0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w]
      m1 = ((),m2) /\
    emit_op SHL [Lit 96w;target] m2 = (aligned,m3) /\
    (do dst <- emit_op ADD [Var p;Lit 19w];
        emit_void MSTORE [dst;aligned] od) m3 = ((),m4) /\
    (do dst <- emit_op ADD [Var p;Lit 39w];
        emit_void MSTORE [dst;
          Lit 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w]
     od) m4 = ((),sb) /\
    fn_has_code sa m1 func /\ fn_has_code m1 m2 func /\
    fn_has_code m2 m3 func /\ fn_has_code m3 m4 func /\ fn_has_code m4 sb func /\
    m1.cs_next_id = SUC sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sa.cs_next_var <= m1.cs_next_var /\ m1.cs_next_var <= m2.cs_next_var /\
    m2.cs_next_var <= m3.cs_next_var /\ m3.cs_next_var <= m4.cs_next_var /\
    m4.cs_next_var <= sb.cs_next_var /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 96w] [p]) (fn_insts func) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Ga,ta)) /\
    ~u.vs_halted /\ u.vs_current_bb = m1.cs_current_bb /\
    u.vs_inst_idx = LENGTH m1.cs_current_insts /\
    u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H':(bool # bytes32 # type_value) list # num list.
          stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es u) /\
    alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ lo <= u.vs_alloca_next /\
    lookup_var p u = SOME w /\ ptr_covers Ga ta p u 96 /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,96) /\
    FLOOKUP Ga p = SOME (w2n w,96) /\
    lo <= w2n w /\ w2n w + 96 < dimword (:256) /\ w2n w + 96 <= u.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP u.vs_allocas aid = SOME e) /\
    (!aid a k. FLOOKUP u.vs_allocas aid = SOME (a,k) ==>
               FLOOKUP s.vs_allocas aid = SOME (a,k) \/ s.vs_alloca_next <= a) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) 96 b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
                  regions_disjoint (w2n w) 96 b len) /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + 96)) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
         op_taint ta (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule proxy_allocation_parts >> strip_tac >>
  drule_all proxy_allocation_subintervals >> strip_tac >>
  `96 < dimword (:256)` by simp[dimword_def, venomLayoutTheory.dimindex_256] >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choosel_then [`p`,`w`,`u`,`Ga`,`ta`,`r`] strip_assume_tac)) >>
  `buf = Var p` by simp[] >>
  qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_assum `Var p = allocation.buf_operand` mp_tac >>
     qpat_assum `allocation.buf_operand = Var (STRING _ _)`
       (fn th => pure_rewrite_tac [th, operand_11]) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 96w] [p]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `run_inst_seq [mk_inst sa.cs_next_id ALLOCA [Lit 96w] [p]] s = OK r` by
    fs[] >>
  `!aid a k. FLOOKUP u.vs_allocas aid = SOME (a,k) ==>
       FLOOKUP s.vs_allocas aid = SOME (a,k) \/ s.vs_alloca_next <= a` by
    (drule proxy_alloca_old_or_above >> simp[]) >>
  qpat_x_assum `u = _` kall_tac >>
  qpat_x_assum `Ga = _` kall_tac >>
  qpat_x_assum `ta = _` kall_tac >>
  `~u.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `u with <|vs_vars := _;vs_allocas := _;
                          vs_alloca_next := _;vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ s ==> _` drule >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ u`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >> disch_then drule >> simp[]) >>
  qexistsl_tac [`m1`,`m2`,`m3`,`m4`,`aligned`,`p`,`w`,`u`,`Ga`,`ta`] >>
  asm_rewrite_tac[arithmeticTheory.ADD1]
QED
