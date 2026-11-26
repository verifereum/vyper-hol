(* The decoder entry of a non-default external-call return. *)
Theory bodyExtReturnDecodeRouteMods
Ancestors
  extcallReturnDefaultRouting extcallReturnDefaultControlJoint
  bodyForRangeScalarFrameMods bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullPostsMods fragGasOriginPtr exprLoweringProps exprSimWordArgs
  compileEnv exprLowering abiEncoder emitHelperProps fragExec
  loweringStateRelDefs[qualified,ignore_grammar]
  bodyPtrDefs ptrDiscipline venomState words

Theorem decode_route_extcodesize_mono[local]:
  (if skip then comp_return () else compile_extcodesize_check addr) l = ((),r) ==>
  ci_mono l r
Proof
  Cases_on `skip` >- simp[comp_return_def,ci_mono_refl] >>
  simp[compile_extcodesize_check_def,comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> metis_tac[ci_mono_emit_op,ci_mono_emit_void,ci_mono_trans,pairTheory.SND]
QED

Theorem extcall_decode_route_mods:
  ret_type <> NoneT /\ ~(has_default /\ bs = []) /\
  compile_alloc_buffer (type_memory_bytes cenv ret_type) sr = (buf,ar) /\
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty buf_op
          r.buf_operand default_op addr_op skip (abi_static_size cenv.ce_struct_fields rt)
          cap (type_to_abi_dec_info cenv.ce_struct_fields cenv rt))
   else
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. comp_bind (compile_return_value_decode (abi_static_size cenv.ce_struct_fields rt) cap)
          (\hi. comp_ignore_bind
             (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi
               (type_to_abi_dec_info cenv.ce_struct_fields cenv rt))
             (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  fn_has_code ar sb func /\ buf.buf_operand = Var q /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK a,J,tm)) /\
  ~a.vs_halted /\ a.vs_current_bb = ar.cs_current_bb /\
  a.vs_inst_idx = LENGTH ar.cs_current_insts /\ a.vs_returndata = bs /\
  LENGTH bs < dimword (:256) /\
  alloca_history func a /\ allocas_from lo a /\
  local_ptrs_reserved cenv ar /\ sa.cs_next_var <= ar.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ar x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee a /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee J tm a) /\
  immutable_frame_mods func cenv cx ee a /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 J tm /\ wb_frame cenv es ee sa s0 a ==>
  result_op = Var q /\
  ?k hi hs de p Gp tp.
    compile_return_value_decode (abi_static_size cenv.ce_struct_fields rt) cap k = (hi,hs) /\
    compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD buf_op hi
      (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de) /\
    fn_has_code k hs func /\ fn_has_code hs de func /\ ci_mono ar k /\
    (de = sb \/ ?xl cj old. emit_inst JMP [Label xl] [] de = ((),cj) /\
       fn_has_code de cj func /\ new_block xl cj = (old,sb)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)) /\
    ~p.vs_halted /\ p.vs_current_bb = k.cs_current_bb /\
    p.vs_inst_idx = LENGTH k.cs_current_insts /\ p.vs_returndata = bs /\
    p.vs_allocas = a.vs_allocas /\ p.vs_alloca_next = a.vs_alloca_next /\
    p.vs_memory = a.vs_memory /\ alloca_history func p /\ allocas_from lo p /\
    tp.t_mem = tm.t_mem /\
    (!x. not_fresh_at ar x ==> lookup_var x p = lookup_var x a /\
      FLOOKUP Gp x = FLOOKUP J x /\ op_taint tp (Var x) = op_taint tm (Var x)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee p /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee Gp tp p) /\
    immutable_frame_mods func cenv cx ee p /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp /\ wb_frame cenv es ee sa s0 p
Proof
  strip_tac >> reverse (Cases_on `has_default`)
  >- suspend "direct" >>
  suspend "through_shell"
QED

Resume extcall_decode_route_mods[direct]:
  qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_return_value_decode _ _ ar = (hi,hs)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ hi _ hs = (u,de)` >>
  Cases_on `u` >>
  qpat_x_assum `de = sb` SUBST_ALL_TAC >>
  qpat_x_assum `Var q = result_op` (SUBST_ALL_TAC o SYM) >>
  `cs_extends ar hs` by
    (qpat_assum `compile_return_value_decode _ _ ar = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_compile_return_value_decode,ci_mono_def,pairTheory.SND]) >>
  `cs_extends hs sb` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ hs = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[cj 1 ci_mono_compile_abi_decode,ci_mono_def,pairTheory.SND]) >>
  `fn_has_code ar hs func /\ fn_has_code hs sb func` by
    (conj_tac >> irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`sb`,`ar`] >> simp[cs_extends_refl]) >>
  qexistsl_tac [`ar`,`hi`,`hs`,`sb`,`a`,`J`,`tm`] >> simp[ci_mono_refl]
QED

Resume extcall_decode_route_mods[through_shell]:
  `compile_default_return_path cenv ret_type default_ty buf_op buf.buf_operand
     default_op addr_op skip (abi_static_size cenv.ce_struct_fields rt) cap
     (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) ar = (result_op,sb)` by
    (qpat_x_assum `(if ret_type = NoneT then _ else _) sr = _` mp_tac >> simp[comp_bind_def]) >>
  drule_then strip_assume_tac return_default_path_intervals >>
  drule_all_then strip_assume_tac return_default_intervals_code >>
  conj_tac >- simp[] >>
  `ci_mono ar cs` by
    (map_every (fn (mid,eq,th) =>
       irule ci_mono_trans >> qexists_tac mid >> conj_tac >-
       (qpat_assum eq mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[th,pairTheory.SND]))
       [(`a1`,`emit_op RETURNDATASIZE _ ar = _`,ci_mono_emit_op),
        (`a2`,`emit_op ISZERO _ a1 = _`,ci_mono_emit_op),
        (`a3`,`fresh_label _ a2 = _`,ci_mono_fresh_label),
        (`a4`,`fresh_label _ a3 = _`,ci_mono_fresh_label),
        (`a5`,`fresh_label _ a4 = _`,ci_mono_fresh_label),
        (`a6`,`emit_inst JNZ _ _ a5 = _`,ci_mono_emit_inst),
        (`ds`,`new_block _ a6 = _`,ci_mono_new_block),
        (`de`,`compile_store_memory _ _ _ _ _ ds = _`,ci_mono_compile_store_memory),
        (`ck`,`(if skip then _ else _) de = ((),ck)`,decode_route_extcodesize_mono),
        (`dj`,`emit_inst JMP _ _ ck = _`,ci_mono_emit_inst)] >>
     qpat_assum `new_block cl dj = _` mp_tac >> rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_new_block,pairTheory.SND]) >>
  `a.vs_returndata <> [] /\ LENGTH a.vs_returndata < dimword (:256)` by fs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_at (Pat `emit_op RETURNDATASIZE _ ar = _`)
    (INST_TYPE [alpha |-> ``:256``] return_default_shell_joint) >>
  disch_then (drule_all_then (qspecl_then [`tm`,`explicit`,`PG`,`J`]
    (qx_choose_then `p` (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac))))) >>
  `ar.cs_next_var <= a1.cs_next_var` by
    (qpat_assum `emit_op RETURNDATASIZE _ ar = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[ci_mono_emit_op,ci_mono_def,pairTheory.SND]) >>
  drule_at (Pat `p = jump_to _ _`) return_default_shell_joint_frame >>
  disch_then (qspecl_then [`tm`,`tp`,`func`,`ar`,`Gp`,`J`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `p.vs_data_section = a.vs_data_section /\ p.vs_call_ctx = a.vs_call_ctx /\
   p.vs_transient = a.vs_transient /\ p.vs_immutables = a.vs_immutables` by
    (qpat_assum `p = jump_to _ _` SUBST1_TAC >> simp[jump_to_def,update_var_def]) >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==> stmt_state_rel h ctx func cenv cx ee p` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `p = jump_to _ _` SUBST1_TAC >>
     simp[stmt_state_rel_jump_to,stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> conj_tac
     >- (irule local_ptrs_reserved_fresh >> qexists_tac `ar` >> simp[]) >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `ar` >> simp[]) >>
  qpat_x_assum `p = jump_to _ _` kall_tac >>
  qpat_x_assum `Gp = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `tp = _ with t_var := _` kall_tac >>
  every_drule_then strip_assume_tac new_block_props >>
  `allocas_from lo p` by
    (qpat_assum `p.vs_allocas = a.vs_allocas`
       (fn th => pure_rewrite_tac [allocas_from_def,th]) >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK a,J,tm)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (a,J,tm) [] (OK p,Gp,tp)`
       (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append,listTheory.APPEND]) >>
  qexistsl_tac [`cs`,`hi`,`hs`,`he`,`p`,`Gp`,`tp`] >>
  simp[IgnAsm `result_op = buf.buf_operand`] >>
  conj_tac >- (disj2_tac >> qexistsl_tac [`xl`,`cj`,`old3`] >> simp[]) >>
  reverse conj_tac
  >- (irule immutable_frame_mods_exterior_frame >>
      qexistsl_tac [`ee`,`a`,`ar`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  irule ghost_inv_at_mods_exterior_frame >>
  qexistsl_tac [`J`,`ee`,`a`,`ar`,`tm`] >> simp[]
QED

Finalise extcall_decode_route_mods
