(* Read-only controls on either side of the selected default write. *)
Theory bodyExtReturnDefaultControlMods
Ancestors fragGasOriginPtrLoop[qualified,ignore_grammar]
  extcallReturnDefaultRouting extcallReturnDefaultControlJoint
  bodyForRangeScalarFrameMods bodyFullExtCallPrecheck decoderNavigationPtr
  typedCopyOriginPtrBase accountsRelProps stateRelProj vyperRuntimeAccounts
  typedMemoryCopy exprSafeOperand exprLoweringProps emitHelperProps
  fragGasOriginPtr bodyFullPostsMods loweringPosts bodyPtrDefs
  codegenRel compileEnv context venomState finite_map words ptrDiscipline
  fragExec emitHelper exprLowering

Theorem default_shell_linked[local]:
  emit_op RETURNDATASIZE [] ar = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] a5 = ((),a6) /\
  fn_has_code ar a2 func /\ fn_has_code a5 a6 func /\
  a.vs_returndata = [] /\ ~a.vs_halted /\ allocas_from lo a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  a.vs_current_bb = ar.cs_current_bb /\ a.vs_inst_idx = LENGTH ar.cs_current_insts /\
  local_ptrs_reserved cenv ar /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  immutable_frame_mods func cenv cx ee a ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,tm) [] (OK u,Gu,tu)) /\
    (!x. not_fresh_at ar x ==> lookup_var x u = lookup_var x a /\
          FLOOKUP Gu x = FLOOKUP J x /\ op_taint tu (Var x) = op_taint tm (Var x)) /\
    u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
    u.vs_memory = a.vs_memory /\ tu.t_mem = tm.t_mem /\ u.vs_accounts = a.vs_accounts /\
    ~u.vs_halted /\ u.vs_inst_idx = 0 /\ u.vs_current_bb = dl /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (alloca_history func a ==> alloca_history func u) /\
    immutable_frame_mods func cenv cx ee u /\
    (!H. stmt_state_rel H ctx func cenv cx ee a ==> stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx ee J tm a ==>
           ghost_inv_at_mods D lo d cenv cx ee Gu tu u) /\
    (!es s0 sa G0 tn0. sa.cs_next_var <= ar.cs_next_var ==>
       (ghost_kept_at lo cenv es sa G0 tn0 s0 J tm ==> ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu) /\
       (wb_frame cenv es ee sa s0 a ==> wb_frame cenv es ee sa s0 u))
Proof
  strip_tac >> `LENGTH a.vs_returndata < dimword (:256)` by simp[] >>
  drule_all return_default_shell_joint >>
  disch_then (qspecl_then [`tm`,`explicit`,`PG`,`J`]
    (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `ar.cs_next_var <= a1.cs_next_var` by
    (qpat_assum `emit_op RETURNDATASIZE _ ar = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  drule_at (Pat `u = jump_to _ _`) return_default_shell_joint_frame >>
  disch_then (qspecl_then [`tm`,`tu`,`func`,`ar`,`Gu`,`J`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `u.vs_data_section = a.vs_data_section /\ u.vs_call_ctx = a.vs_call_ctx /\
   u.vs_transient = a.vs_transient /\ u.vs_immutables = a.vs_immutables /\
   (allocas_below_fmp u <=> allocas_below_fmp a)` by
    simp[jump_to_def,update_var_def,allocas_below_fmp_def] >>
  `allocas_from lo u` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  qpat_x_assum `u = jump_to _ _` kall_tac >>
  qpat_x_assum `Gu = DRESTRICT _ _` kall_tac >>
  `tu.t_mem = tm.t_mem` by simp[] >>
  qpat_x_assum `tu = _ with t_var := _` kall_tac >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[] >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`ee`,`a`,`ar`] >> simp[]) >>
  rpt strip_tac >> irule ghost_inv_at_mods_exterior_frame >>
  qexistsl_tac [`J`,`ee`,`a`,`ar`,`tm`] >> simp[]
QED

Theorem default_shell_next_var[local]:
  emit_op RETURNDATASIZE [] ar = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] a5 = ((),a6) /\
  new_block dl a6 = (old,ds) ==> ar.cs_next_var <= ds.cs_next_var
Proof
  strip_tac >>
  `ar.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var` by
    metis_tac[ci_mono_emit_op,ci_mono_def,pairTheory.SND] >>
  `a2.cs_next_var = a3.cs_next_var /\ a3.cs_next_var = a4.cs_next_var /\
   a4.cs_next_var = a5.cs_next_var` by metis_tac[fresh_label_props] >>
  `a5.cs_next_var <= a6.cs_next_var` by
    metis_tac[ci_mono_emit_inst,ci_mono_def,pairTheory.SND] >>
  `ds.cs_next_var = a6.cs_next_var` by metis_tac[new_block_props] >>
  decide_tac
QED

Theorem extcall_default_entry_tmem_mods:
  compile_default_return_path cenv rt dt base_op (Var q) dop addr skip low cap info ar = (out,sb) /\
  fn_has_code ar sb func /\ rt <> NoneT /\ has_default /\ bs = [] /\ a.vs_returndata = bs /\
  ~a.vs_halted /\ a.vs_current_bb = ar.cs_current_bb /\ a.vs_inst_idx = LENGTH ar.cs_current_insts /\
  alloca_history func a /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  local_ptrs_reserved cenv ar /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  not_fresh_at ar q /\ lookup_var q a = SOME dw /\ FLOOKUP J q = SOME (w2n dw,n) /\
  ptr_covers J tm q a n /\ w2n dw + n <= a.vs_alloca_next /\
  safe_operand ar dop /\ eval_operand dop a = SOME w /\ op_taint tm dop = {} /\
  safe_operand ar addr /\ eval_operand addr a = SOME aw /\ op_taint tm addr = {} /\
  immutable_frame_mods func cenv cx ee a ==>
  ?ds de ck dj xl cj old3 u Gu tu.
    out = Var q /\ ar.cs_next_var <= ds.cs_next_var /\
    compile_store_memory cenv dop (Var q) rt dt ds = ((),de) /\
    (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
    emit_inst JMP [Label xl] [] ck = ((),dj) /\ new_block xl cj = (old3,sb) /\
    fn_has_code ds de func /\ fn_has_code de ck func /\ fn_has_code ck dj func /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,tm) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = ds.cs_current_bb /\ u.vs_inst_idx = LENGTH ds.cs_current_insts /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
    u.vs_memory = a.vs_memory /\ tu.t_mem = tm.t_mem /\ u.vs_accounts = a.vs_accounts /\
    (!x. not_fresh_at ar x ==> lookup_var x u = lookup_var x a /\
          FLOOKUP Gu x = FLOOKUP J x /\ op_taint tu (Var x) = op_taint tm (Var x)) /\
    lookup_var q u = SOME dw /\ FLOOKUP Gu q = SOME (w2n dw,n) /\
    ptr_covers Gu tu q u n /\ w2n dw + n <= u.vs_alloca_next /\ not_fresh_at ds q /\
    eval_operand dop u = SOME w /\ op_taint tu dop = {} /\ (!x. dop = Var x ==> not_fresh_at ds x) /\
    eval_operand addr u = SOME aw /\ op_taint tu addr = {} /\ (!x. addr = Var x ==> not_fresh_at ds x) /\
    local_ptrs_reserved cenv ds /\ immutable_frame_mods func cenv cx ee u /\
    (!H. stmt_state_rel H ctx func cenv cx ee a ==> stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx ee J tm a ==>
           ghost_inv_at_mods D lo d cenv cx ee Gu tu u) /\
    (!es s0 sa G0 tn0. sa.cs_next_var <= ar.cs_next_var ==>
       (ghost_kept_at lo cenv es sa G0 tn0 s0 J tm ==> ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu) /\
       (wb_frame cenv es ee sa s0 a ==> wb_frame cenv es ee sa s0 u))
Proof
  strip_tac >>
  drule_then strip_assume_tac return_default_path_intervals >>
  drule_all_then strip_assume_tac return_default_intervals_code >>
  drule_all_then assume_tac default_shell_next_var >>
  `a.vs_returndata = []` by simp[] >>
  drule_all default_shell_linked >>
  disch_then (qspecl_then [`tm`,`explicit`,`PG`,`J`]
    (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `ds.cs_current_bb = dl /\ ds.cs_current_insts = []` by
    (qpat_assum `new_block dl a6 = (_,ds)` (mp_tac o MATCH_MP new_block_props) >> simp[]) >>
  `!x. not_fresh_at ar x ==> not_fresh_at ds x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ar` >> simp[]) >>
  `local_ptrs_reserved cenv ds` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `ar` >> simp[]) >>
  `!op. safe_operand ar op ==> eval_operand op u = eval_operand op a /\
      op_taint tu op = op_taint tm op /\ (!x. op = Var x ==> not_fresh_at ds x)` by
    (Cases_on `op` >> simp[safe_operand_def,eval_operand_def,op_taint_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[op_taint_def]) >>
  `lookup_var q u = SOME dw /\ FLOOKUP Gu q = SOME (w2n dw,n) /\ ptr_covers Gu tu q u n` by
    (qpat_assum `!x. not_fresh_at ar x ==> lookup_var x u = _ /\ _`
       (qspec_then `q` assume_tac) >>
     qpat_assum `not_fresh_at ar q ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `ptr_covers J tm q a n` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> simp[]) >>
  `!x. dop = Var x ==> not_fresh_at ds x` by
    (qpat_assum `!op. safe_operand ar op ==> _`
       (qspec_then `dop` mp_tac) >> simp[]) >>
  `!x. addr = Var x ==> not_fresh_at ds x` by
    (qpat_assum `!op. safe_operand ar op ==> _`
       (qspec_then `addr` mp_tac) >> simp[]) >>
  qexistsl_tac [`ds`,`de`,`ck`,`dj`,`xl`,`cj`,`old3`,`u`,`Gu`,`tu`] >>
  simp[] >> rpt conj_tac >> first_assum (irule_at Any) >> first_assum ACCEPT_TAC
QED

Theorem extcall_default_entry_mods:
  compile_default_return_path cenv rt dt base_op (Var q) dop addr skip low cap info ar = (out,sb) /\
  fn_has_code ar sb func /\ rt <> NoneT /\ has_default /\ bs = [] /\ a.vs_returndata = bs /\
  ~a.vs_halted /\ a.vs_current_bb = ar.cs_current_bb /\ a.vs_inst_idx = LENGTH ar.cs_current_insts /\
  alloca_history func a /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  local_ptrs_reserved cenv ar /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ar x) /\
  not_fresh_at ar q /\ lookup_var q a = SOME dw /\ FLOOKUP J q = SOME (w2n dw,n) /\
  ptr_covers J tm q a n /\ w2n dw + n <= a.vs_alloca_next /\
  safe_operand ar dop /\ eval_operand dop a = SOME w /\ op_taint tm dop = {} /\
  safe_operand ar addr /\ eval_operand addr a = SOME aw /\ op_taint tm addr = {} /\
  immutable_frame_mods func cenv cx ee a ==>
  ?ds de ck dj xl cj old3 u Gu tu.
    out = Var q /\ ar.cs_next_var <= ds.cs_next_var /\
    compile_store_memory cenv dop (Var q) rt dt ds = ((),de) /\
    (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
    emit_inst JMP [Label xl] [] ck = ((),dj) /\ new_block xl cj = (old3,sb) /\
    fn_has_code ds de func /\ fn_has_code de ck func /\ fn_has_code ck dj func /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,tm) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = ds.cs_current_bb /\ u.vs_inst_idx = LENGTH ds.cs_current_insts /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
    u.vs_memory = a.vs_memory /\ u.vs_accounts = a.vs_accounts /\
    (!x. not_fresh_at ar x ==> lookup_var x u = lookup_var x a /\
          FLOOKUP Gu x = FLOOKUP J x /\ op_taint tu (Var x) = op_taint tm (Var x)) /\
    lookup_var q u = SOME dw /\ FLOOKUP Gu q = SOME (w2n dw,n) /\
    ptr_covers Gu tu q u n /\ w2n dw + n <= u.vs_alloca_next /\ not_fresh_at ds q /\
    eval_operand dop u = SOME w /\ op_taint tu dop = {} /\ (!x. dop = Var x ==> not_fresh_at ds x) /\
    eval_operand addr u = SOME aw /\ op_taint tu addr = {} /\ (!x. addr = Var x ==> not_fresh_at ds x) /\
    local_ptrs_reserved cenv ds /\ immutable_frame_mods func cenv cx ee u /\
    (!H. stmt_state_rel H ctx func cenv cx ee a ==> stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx ee J tm a ==>
           ghost_inv_at_mods D lo d cenv cx ee Gu tu u) /\
    (!es s0 sa G0 tn0. sa.cs_next_var <= ar.cs_next_var ==>
       (ghost_kept_at lo cenv es sa G0 tn0 s0 J tm ==> ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu) /\
       (wb_frame cenv es ee sa s0 a ==> wb_frame cenv es ee sa s0 u))
Proof
  strip_tac >>
  drule_all extcall_default_entry_tmem_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`ds`,`de`,`ck`,`dj`,`xl`,`cj`,`old3`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  qexistsl_tac [`ds`,`de`,`ck`,`dj`,`xl`,`cj`,`old3`,`u`,`Gu`,`tu`] >>
  simp[]
QED

Theorem default_shell_code_agrees[local]:
  stmt_state_rel H ctx func cenv cx ee u /\
  accounts_runtime_well_typed ee.accounts /\ p.vs_accounts = u.vs_accounts /\
  w2w (aw:bytes32) = target ==>
  ((n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_has_code target ee.accounts)
Proof
  strip_tac >>
  `accounts_agree H cx.txn.target ee.accounts u.vs_accounts` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_accounts) >> simp[]) >>
  drule accounts_agree_lookup >> disch_then (qspec_then `target` strip_assume_tac) >>
  `LENGTH (lookup_account target ee.accounts).code <= 24576` by
    fs[accounts_runtime_well_typed_def,account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target ee.accounts).code < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  simp[vyperInterpreterTheory.ext_call_has_code_def, listTheory.NULL_EQ,
       wordsTheory.n2w_11, listTheory.LENGTH_NIL]
QED

Theorem default_shell_join[local]:
  emit_inst JMP [Label xl] [] ck = ((),dj) /\ fn_has_code ck dj func /\
  ~v.vs_halted /\ v.vs_current_bb = ck.cs_current_bb /\
  v.vs_inst_idx = LENGTH ck.cs_current_insts /\ allocas_from lo v /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp v) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gc,tc) []
        (OK (jump_to xl v),Gc,tc)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_assum `!i. i < _ ==> get_instruction bb _ = _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  irule decoderNavigationPtrTheory.jump_origin_ptr_path >> simp[] >>
  qexists_tac `ck.cs_next_id` >>
  qpat_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >> simp[]
  >> (bossLib.gvs [])
QED

Theorem default_shell_checked[local]:
  compile_extcodesize_check addr de = ((),ck) /\ fn_has_code de ck func /\
  ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
  p.vs_inst_idx = LENGTH de.cs_current_insts /\
  eval_operand addr p = SOME aw /\ op_taint tp addr = {} /\ allocas_from lo p /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp p) ==>
  let w = (n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) : bytes32);
      x = STRING #"%" (toString de.cs_next_var);
      z = update_var x w p;
      J = Gp \\ x;
      tm = tp with t_var := tp.t_var |+ (x,{})
  in
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) []
        ((if w = 0w then Abort Revert_abort (revert_state (set_returndata []
                (z with vs_inst_idx := SUC p.vs_inst_idx)))
          else OK (z with vs_inst_idx := LENGTH ck.cs_current_insts)),J,tm)
Proof
  strip_tac >> drule_all extcall_codesize_checked_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gp`] mp_tac) >>
  simp[LET_THM]
QED

Theorem default_shell_checked_landing[local]:
  (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
  ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
  p.vs_inst_idx = LENGTH de.cs_current_insts /\
  allocas_from lo p /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p) ==>
  let v = if skip then p else
    update_var (STRING #"%" (toString de.cs_next_var)) w p with
      vs_inst_idx := LENGTH ck.cs_current_insts in
  ~v.vs_halted /\ v.vs_current_bb = ck.cs_current_bb /\
  v.vs_inst_idx = LENGTH ck.cs_current_insts /\ allocas_from lo v /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp v)
Proof
  Cases_on `skip` >- simp[comp_return_def] >>
  simp[LET_THM,update_var_def,allocas_from_def,allocas_below_fmp_def] >> strip_tac >>
  qpat_x_assum `compile_extcodesize_check addr de = _` mp_tac >>
  simp[compile_extcodesize_check_def,emit_op_def,emit_void_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,fresh_var_def,fresh_id_def,emit_def,
       listTheory.APPEND_ASSOC, arithmeticTheory.ADD1] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[Once (GSYM listTheory.APPEND_ASSOC), allocas_from_def,
       allocas_below_fmp_def] >>
  conj_tac >- first_assum ACCEPT_TAC >- metis_tac[]
QED

Theorem extcall_default_exit_mods:
  compile_store_memory cenv dop (Var q) rt dt ds = ((),de) /\
  (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
  fn_has_code de ck func /\ emit_inst JMP [Label xl] [] ck = ((),dj) /\
  fn_has_code ck dj func /\ new_block xl cj = (old3,sb) /\
  stmt_state_rel H ctx func cenv cx ee u /\ accounts_runtime_well_typed ee.accounts /\
  w2w (aw:bytes32) = target /\ eval_operand addr u = SOME aw /\ op_taint tu addr = {} /\
  (!x. addr = Var x ==> not_fresh_at ds x) /\
  alloca_history func u /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
  typed_copy_state_frame ds off (type_memory_size rtv) u p /\
  (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==> val_in_memory rtv dv off mem) /\
  (!x. not_fresh_at ds x ==> FLOOKUP Gp x = FLOOKUP Gu x /\
       op_taint tp (Var x) = op_taint tu (Var x)) /\
  (!i. ~(off <= i /\ i < off + type_memory_size rtv) ==> (i IN tp.t_mem <=> i IN tu.t_mem)) /\
  tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
  ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\ p.vs_inst_idx = LENGTH de.cs_current_insts ==>
  if skip \/ ext_call_has_code target ee.accounts then
    ?z Gz tz.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      typed_copy_state_frame ds off (type_memory_size rtv) u z /\
      (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory rtv dv off mem) /\
      (!x. not_fresh_at ds x ==> FLOOKUP Gz x = FLOOKUP Gu x /\
           op_taint tz (Var x) = op_taint tu (Var x)) /\
      (!i. ~(off <= i /\ i < off + type_memory_size rtv) ==> (i IN tz.t_mem <=> i IN tu.t_mem)) /\
      tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
      z.vs_memory = p.vs_memory /\ z.vs_allocas = u.vs_allocas /\
      z.vs_alloca_next = u.vs_alloca_next /\ alloca_history func z /\
      allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts
  else
    ?r Gz tz.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (r,Gz,tz)) /\
      exit_result r /\ expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r
Proof
  strip_tac >>
  `eval_operand addr p = SOME aw` by
    (drule_all typed_copy_state_frame_operand >> simp[]) >>
  `op_taint tp addr = {}` by (Cases_on `addr` >> fs[op_taint_def]) >>
  `p.vs_accounts = u.vs_accounts /\ p.vs_allocas = u.vs_allocas /\
   p.vs_alloca_next = u.vs_alloca_next` by
    ((qpat_assum `typed_copy_state_frame ds _ _ u p` mp_tac >>
     simp[typed_copy_state_frame_def,venom_state_component_equality] >> (gvs[typed_copy_state_frame_def, venom_state_component_equality]))) >>
  `allocas_from lo p` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp p` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  drule_all_then assume_tac default_shell_code_agrees >>
  Cases_on `skip \/ ext_call_has_code target ee.accounts` >> simp[]
  >- suspend "success" >>
  suspend "abort"
QED

Resume extcall_default_exit_mods[abort]:
  `~skip /\ ~ext_call_has_code target ee.accounts` by fs[] >>
  `compile_extcodesize_check addr de = ((),ck)` by fs[] >>
  `(n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) : bytes32) = 0w` by fs[] >>
  drule_all default_shell_checked >> simp[LET_THM] >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gp`] assume_tac) >>
  `LENGTH (lookup_account target u.vs_accounts).code MOD dimword (:256) = 0` by
    (qpat_assum `n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code) = 0w`
       mp_tac >> simp[wordsTheory.n2w_11]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) []
      (Abort Revert_abort
        (revert_state
          (set_returndata []
            (update_var (STRING #"%" (toString de.cs_next_var)) 0w p with
             vs_inst_idx := SUC (LENGTH de.cs_current_insts)))),
       Gp \\ STRING #"%" (toString de.cs_next_var),
       tp with t_var := tp.t_var |+ (STRING #"%" (toString de.cs_next_var),{}))` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] _`
       (qspec_then `D` mp_tac) >>
     gvs[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
         wordsTheory.n2w_11]) >>
  qexistsl_tac [`Abort Revert_abort
        (revert_state
          (set_returndata []
            (update_var (STRING #"%" (toString de.cs_next_var)) 0w p with
             vs_inst_idx := SUC (LENGTH de.cs_current_insts))))`,
       `Gp \\ STRING #"%" (toString de.cs_next_var)`,
       `tp with t_var := tp.t_var |+ (STRING #"%" (toString de.cs_next_var),{})`] >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def] >>
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK p,Gp,tp)`
    (qspec_then `D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] _`
    (qspec_then `D` mp_tac) >>
  rpt (pop_assum kall_tac) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND]
QED

Resume extcall_default_exit_mods[success]:
  qabbrev_tac `out = STRING #"%" (toString de.cs_next_var)` >>
  qabbrev_tac `w:bytes32 = n2w (LENGTH (lookup_account (w2w aw) p.vs_accounts).code)` >>
  qabbrev_tac `v = if skip then p else update_var out w p with
                     vs_inst_idx := LENGTH ck.cs_current_insts` >>
  qabbrev_tac `Gc = if skip then Gp else Gp \\ out` >>
  qabbrev_tac `tc = if skip then tp else tp with t_var := tp.t_var |+ (out,{})` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) [] (OK v,Gc,tc)` by
    (Cases_on `skip`
     >- (simp[Abbr `v`,Abbr `Gc`,Abbr `tc`] >> metis_tac[gas_origin_ptr_path_rules]) >>
     `compile_extcodesize_check addr de = ((),ck)` by fs[] >>
     `w <> 0w` by fs[] >>
     drule_all default_shell_checked >>
     disch_then (qspecl_then [`explicit`,`PG`,`Gp`] mp_tac) >>
     qpat_assum `Abbrev (w = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     simp[LET_THM,Abbr `v`,Abbr `Gc`,Abbr `tc`,Abbr `out`]) >>
  `~v.vs_halted /\ v.vs_current_bb = ck.cs_current_bb /\
   v.vs_inst_idx = LENGTH ck.cs_current_insts /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (drule_all default_shell_checked_landing >>
     disch_then (qspec_then `w` mp_tac) >> simp[LET_THM,Abbr `v`,Abbr `out`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gc,tc) []
        (OK (jump_to xl v),Gc,tc)` by
    (gen_tac >> irule default_shell_join >> simp[] >> metis_tac[]) >>
  suspend "join_post"
QED

Resume extcall_default_exit_mods[join_post]:
  qabbrev_tac `z = jump_to xl v` >>
  `ds.cs_next_var <= de.cs_next_var` by
    (qpat_assum `compile_store_memory _ _ _ _ _ ds = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND]) >>
  `!x. not_fresh_at ds x ==> x <> out` by
    (rpt strip_tac >> `not_fresh_at de x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[Abbr `out`,loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `typed_copy_state_frame ds off (type_memory_size rtv) p v` by
    (Cases_on `skip` >> simp[Abbr `v`,typed_copy_state_frame_def,venom_state_component_equality,
       update_var_def,lookup_var_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  `typed_copy_state_frame ds off (type_memory_size rtv) u z` by
    (simp[Abbr `z`] >> irule typed_copy_state_frame_jump >>
     irule typed_copy_state_frame_trans >> qexists_tac `p` >> simp[]) >>
  `!x. not_fresh_at ds x ==> FLOOKUP Gc x = FLOOKUP Gu x /\
     op_taint tc (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >>
     `x <> out /\ out <> x` by metis_tac[] >>
     `op_taint tp (Var x) = op_taint tu (Var x)` by
       (qpat_assum `!x. not_fresh_at ds x ==> _ /\ _`
          (qspec_then `x` mp_tac) >> simp[]) >>
     Cases_on `skip` >>
     simp[Abbr `Gc`,Abbr `tc`,DOMSUB_FLOOKUP_THM,op_taint_def,FLOOKUP_UPDATE] >>
     qpat_x_assum `op_taint tp (Var x) = op_taint tu (Var x)` mp_tac >>
     gvs[ptrDisciplineTheory.op_taint_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gc,tc)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] (OK v,Gc,tc)`
       (qspec_then `D` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,Gc,tc) [] _`
       (qspec_then `D` assume_tac) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) []
          (OK z,Gc,tc)` by
       (qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] (OK v,Gc,tc)`
          (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (v,Gc,tc) [] _`
          (qspec_then `D` mp_tac) >>
        simp[] >> (metis_tac [fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans])) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK p,Gp,tp)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `gas_origin_ptr_path _ (p,Gp,tp) [] (OK z,Gc,tc)` mp_tac >>
     simp[] >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  suspend "join_fields"
QED

Resume extcall_default_exit_mods[join_fields]:
  `z.vs_memory = p.vs_memory /\ z.vs_allocas = u.vs_allocas /\
   z.vs_alloca_next = u.vs_alloca_next /\ ~z.vs_halted /\
   (allocas_below_fmp z <=> allocas_below_fmp p)` by
    (Cases_on `skip` >> simp[Abbr `z`,Abbr `v`,jump_to_def,update_var_def,allocas_below_fmp_def]) >>
  `tc.t_mem = tp.t_mem /\ tc.t_stor = tp.t_stor /\ tc.t_trans = tp.t_trans /\ tc.t_imm = tp.t_imm` by
    (Cases_on `skip` >> simp[Abbr `tc`]) >>
  `z.vs_inst_idx = 0 /\ z.vs_current_bb = xl` by simp[Abbr `z`,jump_to_def] >>
  `sb.cs_current_bb = xl /\ sb.cs_current_insts = []` by
    (drule new_block_props >> simp[]) >>
  `alloca_history func z` by metis_tac[allocaHistoryTheory.alloca_history_jump] >>
  `allocas_from lo z` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  qpat_x_assum `Abbrev (z = _)` kall_tac >> qpat_x_assum `Abbrev (tc = _)` kall_tac >>
  qpat_x_assum `Abbrev (Gc = _)` kall_tac >>
  qexistsl_tac [`z`,`Gc`,`tc`] >> simp[]
QED

Finalise extcall_default_exit_mods
