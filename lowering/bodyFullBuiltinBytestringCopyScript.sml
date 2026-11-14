(* External slice copies and their length words on the joint path. *)
Theory bodyFullBuiltinBytestringCopy
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice bodyFullUnwrapRun
  fragExec fragExecPtr fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport bodyPtrDefs
  instMemFrontier memSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs wordLoadStorePtr list finite_map

Theorem bytestring_external_copy_origin_edge:
  emit_void opc ops sa = ((),sb) /\ fn_has_code sa sb func /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;Var dst;start;cnt] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand (Var dst) s = SOME wd /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME wn /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  ptr_covers G tn dst s (w2n wn) /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = OK u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc ops []) u,
     step_taint (mk_inst sa.cs_next_id opc ops []) s u tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc ops []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY` by
    metis_tac[] >>
  `inst_mem_below_frontier (mk_inst sa.cs_next_id opc ops []) s` by
    (gvs[below_frontier_CALLDATACOPY, below_frontier_CODECOPY,
         below_frontier_EXTCODECOPY]) >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sa.cs_next_id opc ops []) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     irule ptr_inst_ok_external_copy >> metis_tac[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >>
  metis_tac[]
QED

Theorem bytestring_length_store_origin_edge:
  emit_void MSTORE [Var root;cnt] sa = ((),sb) /\
  fn_has_code sa sb func /\
  lookup_var root s = SOME b /\ eval_operand cnt s = SOME n /\
  ptr_covers G tn root s 32 /\ op_taint tn cnt = {} /\
  w2n b + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n b) n s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var root;cnt] [])
       (mstore (w2n b) n s),
     step_taint (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s
       (mstore (w2n b) n s) tn)
Proof
  strip_tac >> gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var root;cnt] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `inst_mem_below_frontier
     (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s` by
    simp[below_frontier_MSTORE, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  metis_tac[]
QED

(* Both instructions use the same physical states and ghosts for every
   horizon.  In particular, the copy does not pick a second allocation. *)
Theorem bytestring_external_copy_length_full_run:
  emit_void opc ops sa = ((),sm) /\ fn_has_code sa sm func /\
  emit_void MSTORE [Var root;cnt] sm = ((),sb) /\
  fn_has_code sm sb func /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;Var dst;start;cnt] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand (Var dst) s = SOME wd /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME wn /\
  lookup_var root s = SOME b /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  ptr_covers G tn dst s (w2n wn) /\
  32 <= N /\ ptr_covers G tn root s N /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  w2n b + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s =
    OK (write_memory_with_expansion (w2n wd) bytes s) ==>
  ?u t tf.
    u = (write_memory_with_expansion (w2n wd) bytes s)
      with vs_inst_idx := SUC s.vs_inst_idx /\
    t = (mstore (w2n b) wn u) with vs_inst_idx := SUC u.vs_inst_idx /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G,tf)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers G tf root t N /\ mem_word_at (w2n b) t.vs_memory = wn /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = (tn.t_mem DIFF
      range_bytes (source_memory_write_ranges
        (mk_inst sa.cs_next_id opc ops []) s))
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_copy_store_counted) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`ARB`,`PG`] strip_assume_tac) >>
  rename1 `tm.t_var = tn.t_var` >>
  rename1 `u = (write_memory_with_expansion _ _ s) with vs_inst_idx := _` >>
  `opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY` by
    metis_tac[] >>
  qabbrev_tac `tc = step_taint (mk_inst sa.cs_next_id opc ops []) s
    (write_memory_with_expansion (w2n wd) bytes s) tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id opc ops [])
       (write_memory_with_expansion (w2n wd) bytes s) = G /\
   tc.t_var = tn.t_var /\ tc.t_stor = tn.t_stor /\
   tc.t_trans = tn.t_trans /\ tc.t_imm = tn.t_imm` by
    (simp[Abbr `tc`] >> metis_tac[external_copy_ghost_frame]) >>
  `tc.t_mem = tn.t_mem DIFF
      range_bytes (source_memory_write_ranges
        (mk_inst sa.cs_next_id opc ops []) s)` by
    (simp[Abbr `tc`] >> irule external_copy_ghost_memory >>
     qpat_assum `((opc = CALLDATACOPY \/ opc = CODECOPY) /\ _) \/ _`
       strip_assume_tac >>
     gvs[write_memory_with_expansion_def]) >>
  `(!op. eval_operand op u = eval_operand op s /\
         op_taint tc op = op_taint tn op) /\
   allocas_from lo u /\ u.vs_alloca_next = s.vs_alloca_next /\
   lookup_var root u = SOME b /\ ~u.vs_halted` by
    (gvs[write_memory_with_expansion_def, write_memory_def,
         expand_memory_def, allocas_from_def, lookup_var_def] >>
     conj_tac
     >- (Cases >> simp[eval_operand_def, op_taint_def, lookup_var_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  `ptr_covers G tc root u 32` by
    (gvs[ptr_covers_def, op_taint_def, lookup_var_def,
         write_memory_with_expansion_def, write_memory_def,
         expand_memory_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `step_prov PG G (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
      (mstore (w2n b) wn u) = G /\
   step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) u
      (mstore (w2n b) wn u) tc = tm` by
    (qspecl_then [`PG`,`G`,`tc`,`u`,`sm.cs_next_id`,`root`,`cnt`,`b`,`wn`]
       mp_tac mstore_ghost_frame >>
     impl_tac >- simp[] >> strip_tac >>
     `(step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) u
        (mstore (w2n b) wn u) tc).t_imm = tc.t_imm` by
       simp[step_taint_def, imm_taint_def, mk_inst_def] >>
     simp_tac pure_ss [taint_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`u`,`t`,`tm`] >> asm_simp_tac bool_ss [] >> gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK u,G,tc)` by
    (mp_tac (bytestring_external_copy_origin_edge |> Q.INST
       [`sb` |-> `sm`,
        `u` |-> `write_memory_with_expansion (w2n wd) bytes s`]) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `D` mp_tac) >> simp[Abbr `tc`]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tc) []
     (OK t,G,tm)` by
    (mp_tac (bytestring_length_store_origin_edge |> Q.INST
       [`sa` |-> `sm`, `s` |-> `u`, `n` |-> `wn`, `tn` |-> `tc`]) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `D` mp_tac) >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tc) []
     (OK t,G,tm)` by
    (qpat_assum `gas_origin_ptr_edge _ (u,G,tc) [] (OK t,G,tm)` mp_tac >>
     qpat_assum `~t.vs_halted` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_origin_ptr_path_rules, APPEND]) >>
  qpat_assum `gas_origin_ptr_edge _ (s,G,tn) [] (OK u,G,tc)` mp_tac >>
  qpat_assum `gas_origin_ptr_path _ (u,G,tc) [] (OK t,G,tm)` mp_tac >>
  qpat_assum `u = _` mp_tac >> qpat_assum `t = _` mp_tac >>
  qpat_assum `s.vs_inst_idx = _` mp_tac >>
  qpat_assum `u.vs_inst_idx = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

