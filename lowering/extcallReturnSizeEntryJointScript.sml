(* The checked size prefix reaches one decoder entry for every horizon. *)
Theory extcallReturnSizeEntryJoint
Ancestors
  extcallReturnSizeJoint extcallReturnEntryBridge abiReturnPrefixTransport
  extcallReturnDefaultControlJoint exprSimAlloc
  abiMalformedRecursiveInterface bodyFullGhostFrame bodyFullUnwrapRun
  exprSimWordArgs abiReturnSize bodyPtrDefs ptrDiscipline
  loweringStateRelDefs exprLoweringProps compileEnv venomState
  finite_map list pred_set

Theorem return_prepared_joint_entry:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  low < dimword (:256) /\ cap < dimword (:256) /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ low <= LENGTH bs /\
  abi_return_decode_ready H0 ctx func cenv cx ee a sites dstid live base_op dst
    B cap bs dest n s /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tm)) /\
    (!H. abi_return_decode_ready H ctx func cenv cx ee a sites dstid live
       base_op dst B cap bs dest n s ==>
      abi_malformed_entry H ctx func cenv cx ee b sites dstid live base_op hi
        (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest n u) /\
    op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
    (!x. not_fresh_at a x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted /\
    (!D d. ghost_inv_at D lo d cenv cx ee G tn s /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
      ghost_inv_at D lo d cenv cx ee Gf tm u) /\
    (!es sa s0. wb_frame cenv es ee sa s0 s /\ sa.cs_next_var <= a.cs_next_var ==>
      wb_frame cenv es ee sa s0 u) /\
    (!es sa G0 tn0 s0. sa.cs_next_var <= a.cs_next_var /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm)
Proof
  strip_tac >>
  drule_all return_decode_ready_entry >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `!x. x IN {x | not_fresh_at a x} ==> not_fresh_at a x` by simp[] >>
  mp_tac (Q.INST [`R` |-> `{x | not_fresh_at a x}`]
    return_size_success_joint) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `u = v with vs_inst_idx := LENGTH b.cs_current_insts` >>
  `!x. not_fresh_at a x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)` by
    (fs[Abbr `u`, lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv a` by fs[abi_return_decode_ready_def] >>
  qpat_assum `v = s with vs_vars := _`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  qexistsl_tac [`u`, `H`, `tm`] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac >- suspend "entry" >>
  simp[] >>
  conj_tac >- simp[Abbr `u`, venom_state_component_equality] >>
  drule abi_return_size_code >> strip_tac >>
  `u.vs_current_bb = b.cs_current_bb /\
   u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted` by
    fs[Abbr `u`, same_blocks_def] >>
  simp[] >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "wb" >>
  rpt gen_tac >> strip_tac >>
  irule ghost_kept_at_clean_suffix >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at a x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  metis_tac[]
QED
Resume return_prepared_joint_entry[entry]:
  qx_gen_tac `horizon` >> strip_tac >>
  mp_tac (Q.INST [`H` |-> `horizon`, `lo` |-> `low`,
    `es` |-> `ee`, `d` |-> `dest`] return_decode_ready_entry) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[Abbr `u`]
QED
Resume return_prepared_joint_entry[ghost]:
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`D`, `lo`, `d`, `cenv`, `cx`, `ee`, `ee`,
    `G`, `H`, `tn`, `tm`, `s`, `u`, `a`] ghost_inv_at_exterior_frame) >>
  (impl_tac >- (simp[] >> simp[Abbr `u`])) >> simp[]
QED
Resume return_prepared_joint_entry[wb]:
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cenv`, `es`, `ee`, `sa`, `s0`, `s`, `a`, `u`]
    wb_frame_readonly_tail) >>
  (impl_tac >- (simp[] >> fs[Abbr `u`, lookup_var_def] >> metis_tac[])) >>
  simp[]
QED
Finalise return_prepared_joint_entry

Theorem return_allocated_short_joint:
  compile_alloc_buffer n a = (buf,m) /\
  compile_return_value_decode low cap m = (hi,b) /\
  fn_has_code a m func /\ fn_has_code m b func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H0 ctx func cenv cx ee s /\ local_ptrs_reserved cenv a /\
  n < dimword (:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  low < dimword (:256) /\ cap < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\ LENGTH s.vs_returndata < low ==>
  ?z Gf tm. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort z,Gf,tm)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts a m) s = OK r` >>
  drule_all return_default_alloc_run_step >> strip_tac >>
  drule_all return_default_alloc_control >> strip_tac >>
  qabbrev_tac `u = r with vs_inst_idx := LENGTH m.cs_current_insts` >>
  qabbrev_tac `AG = step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) r` >>
  qabbrev_tac `atn = step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) s r tn` >>
  `~u.vs_halted /\ allocas_from lo u /\
   u.vs_current_bb = m.cs_current_bb /\
   u.vs_inst_idx = LENGTH m.cs_current_insts /\
   LENGTH u.vs_returndata < dimword (:256) /\ LENGTH u.vs_returndata < low` by
    simp[Abbr `u`, allocas_from_def] >>
  mp_tac (Q.INST [`a` |-> `m`, `s` |-> `u`, `lo` |-> `low`]
    return_size_actual_run) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts m b) u = Abort Revert_abort v` >>
  mp_tac (Q.INST [`a` |-> `m`, `s` |-> `u`, `G` |-> `AG`,
    `tn` |-> `atn`, `err` |-> `Revert_abort`] return_size_abort_joint) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`v with vs_inst_idx := j`, `H`, `tm`] >> gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,AG,atn)` by
    (simp[Abbr `u`, Abbr `AG`, Abbr `atn`] >>
     irule return_default_alloc_joint >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> gvs[]
QED
