(* Joint endpoint frames for operational unwrap runs. *)
Theory exprExtRequestJointUnwrap
Ancestors
  exprExtRequestStoragePath exprExtRequestMaterialize exprExtRequestAllocationEndpoint
  exprExtRequestUnwrapAdapter exprExtRequestHistory exprExtRequestReadProbe
  exprSimMemoryRead exprSimMemorySource exprSimUnwrapProps
  loweringPosts exprLoweringProps compileEnv freshWrites exprLowering
  gasSummary fragGasMode fragGasPath exprSimMemoryPath exprSimProps
  venomState venomExecSemantics valueEncodingProps emitHelperProps emitHelper
  exprSimUnwrap exprSimStorageCopy exprSimCopy vyperInterpreter vyperState venomInst

Theorem extrequest_unchanged_memory_history:
  sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sb /\
  (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
  u.vs_allocas = t.vs_allocas /\ u.vs_memory = t.vs_memory ==>
  extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  simp[extrequest_history_frame_def, extrequest_read_frame_def]
QED

Theorem extrequest_stack_joint_read:
  unwrap_value cenv (StackValue ty a) sn = (op,sb) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (StackValue ty a) t /\
  local_ptrs_reserved cenv sn /\ ~t.vs_halted /\
  t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `?v. read_result cx r ee = (INL v,ee) /\
       expr_val_rel cx (expr_type e) v a t` by
    gvs[vv_post_def, vv_holds_def] >>
  qexistsl_tac [`v`, `t`] >>
  gvs[unwrap_value_def, comp_return_def] >> conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- metis_tac[read_result_gas_obs] >>
      simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]) >>
  conj_tac
  >- (gvs[expr_post_def, vv_post_def, vv_at_def]) >>
  irule extrequest_history_frame_refl >> simp[]
QED

Theorem extrequest_memory_joint_read:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `?w v. eval_operand p.ptr_operand t = SOME w /\
     read_result cx r ee = (INL v,ee) /\
     (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
       val_in_memory tv v (w2n w) t.vs_memory /\
       (is_word_type (expr_type e) ==>
        mem_word_at (w2n w) t.vs_memory = typed_val_to_w256 tv v))` by
    gvs[vv_post_def, vv_holds_def] >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `!u. gas_marked_path F ctx func t 0 (OK u) ==>
       gas_marked_exec F (ctx,func) (read_result cx r) (ee,t) [] (INL v) ee (OK u)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  Cases_on `is_word_type ty`
  >- (`ty = expr_type e` by
        (gvs[vv_post_def, vv_holds_def] >>
         Cases_on `ty` >> gvs[is_bytestring_type_def, is_word_type_def] >>
         Cases_on `b` >> gvs[is_bytestring_type_def, is_word_type_def] >>
         Cases_on `b'` >> gvs[is_bytestring_type_def, is_word_type_def]) >>
      qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_memory_compile] >> strip_tac >>
      qabbrev_tac `u = (update_var (STRING #"%" (toString sn.cs_next_var))
         (mload (w2n w) t) t) with vs_inst_idx := SUC t.vs_inst_idx` >>
      `eval_operand op u = SOME (mload (w2n w) t) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       (!x w'. not_fresh_at sn x /\ lookup_var x t = SOME w' ==>
          lookup_var x u = SOME w') /\
       u.vs_allocas = t.vs_allocas /\ u.vs_memory = t.vs_memory` by
        (qunabbrev_tac `u` >> irule emit_mload_endpoint >>
         simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
      qexistsl_tac [`v`, `u`] >> conj_tac
      >- (first_x_assum irule >> drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
      reverse conj_tac
      >- suspend "word_history" >>
      simp[] >> irule expr_post_of_vv_post_load >>
      `is_word_type (expr_type e)` by metis_tac[] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >>
          `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
          simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sn` >> simp[]) >>
      qexistsl_tac [`p`, `t`, `sn`, `ty`] >> simp[]) >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  qexistsl_tac [`v`, `t`] >> simp[] >> conj_tac
  >- (first_x_assum irule >> simp[gas_marked_path_def] >>
      irule (cj 1 gas_path_rules) >> simp[]) >>
  reverse conj_tac >- (irule extrequest_history_frame_refl >> simp[]) >>
  irule expr_post_of_vv_post_memory >> goal_assum drule >> simp[] >>
  qexists_tac `ty` >> simp[]
QED
Resume extrequest_memory_joint_read[word_history]:
  simp[] >> irule extrequest_unchanged_memory_history >> simp[] >>
  `sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`MLOAD`, `[p.ptr_operand]`, `sn`] ci_mono_emit_op) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  simp[Abbr `u`, lookup_var_def, update_var_def, not_fresh_at_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED
Finalise extrequest_memory_joint_read

(* A copy may overwrite the newly allocated destination, never an old capture. *)
Theorem extrequest_copy_history:
  extrequest_history_frame cenv cx ee sn t ee sm u /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sb /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
  z.vs_allocas = u.vs_allocas /\
  (!off len. regions_disjoint dest cap off len ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
  (!name b sz. local_region cenv ee.scopes t name b sz ==>
     regions_disjoint dest cap b sz) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < sn.cs_next_id ==>
     regions_disjoint dest cap b sz) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
       name = SOME (tv,v) ==>
     regions_disjoint dest cap off (type_memory_size tv)) ==>
  extrequest_history_frame cenv cx ee sn t ee sb z
Proof
  strip_tac >>
  rewrite_tac[extrequest_history_frame_def] >> rpt conj_tac
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- simp[]
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (gvs[extrequest_history_frame_def] >> metis_tac[not_fresh_at_mono]) >>
      gvs[extrequest_history_frame_def] >> metis_tac[])
  >- (gvs[extrequest_history_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `regions_disjoint dest cap b sz` by metis_tac[] >>
      `mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory` by metis_tac[] >>
      gvs[extrequest_history_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `regions_disjoint dest cap b sz` by metis_tac[] >>
      `mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory` by metis_tac[] >>
      gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint dest cap off (type_memory_size tv)` by metis_tac[] >>
  `mem_bytes_at off (type_memory_size tv) z.vs_memory =
   mem_bytes_at off (type_memory_size tv) u.vs_memory` by metis_tac[] >>
  gvs[extrequest_history_frame_def] >> metis_tac[]
QED

(* Any single read-only instruction supplies its post and frame together. *)
Theorem extrequest_emit_read_joint:
  emit_op opc args sn = (op,sb) /\ fn_has_code sn sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  (!out. step_inst_base (mk_inst sn.cs_next_id opc args [out]) t =
     OK (update_var out w t)) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t /\
  is_word_type (expr_type e) /\ sa.cs_next_var <= sn.cs_next_var /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     w = typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv sn /\ ~t.vs_halted /\
  t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?u. gas_marked_path F ctx func t 0 (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sn.cs_next_var)) w t)
                    with vs_inst_idx := SUC t.vs_inst_idx` >>
  `gas_marked_path F ctx func t 0 (OK u)` by
    (pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
     qunabbrev_tac `u` >> irule emit_op_zero_path >>
     simp[] >> qexistsl_tac [`args`, `op`, `opc`, `sb`] >> simp[]) >>
  `eval_operand op u = SOME w /\
   u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
   u.vs_allocas = t.vs_allocas /\ u.vs_memory = t.vs_memory` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >>
     strip_tac >> gvs[Abbr `u`, eval_operand_def, update_var_def,
       lookup_var_def, not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`opc`, `args`, `sn`] ci_mono_emit_op) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule expr_post_of_vv_post_load >> simp[] >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >>
          `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
          simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sn` >> simp[]) >>
      qexistsl_tac [`p`, `t`, `sn`, `ty`] >> simp[]) >>
  irule extrequest_unchanged_memory_history >> simp[]
QED

Theorem extrequest_storage_joint_word:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type ty /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a v. eval_operand p.ptr_operand t = SOME a /\
    read_result cx r ee = (INL v,ee) /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a ee t` by
    (Cases_on `p.ptr_location = LocStorage` >>
     gvs[vv_post_def, vv_holds_def, storage_holds_def,
         read_result_def, return_def]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
     [p.ptr_operand] sn = (op,sb)` by
    (Cases_on `p.ptr_location = LocStorage` >>
     gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u` by
    (irule extrequest_emit_read_joint >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac
     >- (qexistsl_tac [`p`, `ty`] >> simp[]) >>
     qexistsl_tac [`[p.ptr_operand]`,
       `if p.ptr_location = LocStorage then SLOAD else TLOAD`,
       `copy_runtime_word p.ptr_location t a`] >>
     `!out. step_inst_base
        (mk_inst sn.cs_next_id
          (if p.ptr_location = LocStorage then SLOAD else TLOAD)
          [p.ptr_operand] [out]) t =
        OK (update_var out (copy_runtime_word p.ptr_location t a) t)` by
       (Cases_on `p.ptr_location = LocStorage` >>
        gvs[copy_runtime_word_def, step_SLOAD] >>
        pure_once_rewrite_tac[step_inst_base_def] >>
        simp[venomInstTheory.mk_inst_def, exec_read1_def]) >>
     simp[is_terminator_def] >>
     rpt strip_tac >> simp[copy_runtime_word_def] >>
     gvs[] >> drule_all storage_holds_load >> simp[]) >>
  qexistsl_tac [`v`, `u`] >> simp[gas_marked_exec_def] >>
  metis_tac[read_result_gas_obs]
QED

Theorem extrequest_runtime_joint_word:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  is_word_type ty /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a v. eval_operand p.ptr_operand t = SOME a /\
    read_result cx r ee = (INL v,ee) /\
    immutable_holds cenv cx ty (Value v) a ee t` by
    (gvs[vv_post_def, vv_holds_def, immutable_holds_def,
         read_result_def, return_def] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `emit_op DLOAD [p.ptr_operand] sn = (op,sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
        contextTheory.compile_imm_load_word_def] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  drule_all immutable_holds_dload >> strip_tac >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u` by
    (irule extrequest_emit_read_joint >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- (qexistsl_tac [`p`, `ty`] >> simp[]) >>
     qexistsl_tac [`[p.ptr_operand]`, `DLOAD`,
       `word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) t.vs_data_section ++ REPLICATE 32 0w))`] >>
     simp[step_DLOAD, is_terminator_def] >> gvs[] >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`v`, `u`] >> simp[gas_marked_exec_def] >>
  metis_tac[read_result_gas_obs]
QED

Theorem extrequest_ctor_joint_word:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  p.ptr_location = LocCode /\ cenv.ce_is_ctor /\
  is_word_type ty /\ fn_has_code sn sb func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `?v. read_result cx r ee = (INL v,ee)` by
    (gvs[vv_post_def, vv_holds_def, immutable_holds_def] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `ty = expr_type e /\ ?a. eval_operand p.ptr_operand t = SOME a /\
    immutable_holds cenv cx ty (Value v) a ee t` by
    gvs[vv_post_def, vv_holds_def] >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sn = (op,sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  drule_all immutable_holds_iload >> strip_tac >>
  drule_all compile_imm_load_word_ctor_path >> strip_tac >>
  `sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`cenv`, `LocatedValue ty p`, `sn`]
       ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`v`, `s`] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
      metis_tac[read_result_gas_obs]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_load >> simp[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (gvs[] >> rpt strip_tac >> gvs[]) >>
      qexistsl_tac [`p`, `t`, `sn`, `ty`] >> simp[]) >>
  simp[extrequest_history_frame_def, extrequest_read_frame_def]
QED

Theorem extrequest_storage_suffix_joint:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if type_slot_size tv = 1 then
     comp_bind (emit_op (if loc = LocStorage then SLOAD else TLOAD) [src])
       (\v. emit_void MSTORE [dst; v])
   else comp_ignore_bind
     (compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F)
     (comp_return ())) sm = (result,sb) /\
  fn_has_code sm sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x) /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME (n2w b) /\
  type_slot_size tv < 2**256 /\ b + type_memory_size tv < 2**256 /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee u /\
  storage_holds cx (loc = LocTransient) ty (Value v) a ee u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  extrequest_history_frame cenv cx ee sn t ee sm u /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sb /\
  (!name off len. local_region cenv ee.scopes t name off len ==>
     regions_disjoint b (type_memory_size tv) off len) /\
  (!aid off len. FLOOKUP t.vs_allocas aid = SOME (off,len) /\ aid < sn.cs_next_id ==>
     regions_disjoint b (type_memory_size tv) off len) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint b (type_memory_size tv) off (type_memory_size itv)) ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\ copy_static z = copy_static u /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
    (!off len. regions_disjoint b (type_memory_size tv) off len ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee sb z
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `b + 32 * type_slot_size tv < 2**256` by fs[type_memory_size_slots] >>
  drule_all extrequest_storage_suffix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a b (type_slot_size tv) u (type_slot_size tv) t'` by
    (Cases_on `loc = LocStorage` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `!off len. regions_disjoint b (type_memory_size tv) off len ==>
       mem_bytes_at off len t'.vs_memory = mem_bytes_at off len u.vs_memory` by
    (gvs[copy_prefix_def, regions_disjoint_def, type_memory_size_slots] >> metis_tac[]) >>
  `t'.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
  qexists_tac `t'` >> simp[] >>
  irule extrequest_copy_history >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `b`, `sm`, `u`] >> simp[] >> metis_tac[]
QED

Theorem extrequest_storage_joint_copy:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type ty /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sn x) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a tv v. eval_operand p.ptr_operand t = SOME a /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx r ee = (INL v,ee) /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a ee t` by
    (Cases_on `p.ptr_location = LocStorage` >>
     gvs[vv_post_def, vv_holds_def, storage_holds_def, read_result_def, return_def] >>
     metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    metis_tac[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  Cases_on `p.ptr_location = LocStorage` >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  fs[] >>
  qpat_x_assum `cs'' = sb` (assume_tac o SYM) >> gvs[] >>
  rename1 `compile_alloc_buffer _ sn = (buf,mid)` >>
  `((type_memory_size tv + 31) DIV 32) = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  fs[contextTheory.compile_storage_to_memory_def,
     contextTheory.compile_transient_to_memory_def] >>
  rename1 `fn_has_code sn se func` >>
  `(if type_slot_size tv = 1 then
      comp_bind (emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD) [p.ptr_operand])
        (\v. emit_void MSTORE [buf.buf_operand; v])
    else comp_ignore_bind
      (compile_word_copy_loop p.ptr_operand buf.buf_operand (type_slot_size tv)
         p.ptr_location LocMemory F) (comp_return ())) mid = ((),se)` by
      gvs[comp_ignore_bind_def, comp_bind_def] >>
  `cs_extends mid se` by
    (irule storage_copy_suffix_extends >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sn mid` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sn mid func /\ fn_has_code mid se func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  `type_memory_size tv < dimword (:256)` by (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
      (Value v) a ee u` by
    gvs[storage_holds_def, contract_storage_def, contract_transient_def] >>
  `eval_operand p.ptr_operand u = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `ci_mono mid se` by
    (irule storage_copy_suffix_ci_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv se` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sn` >>
     gvs[ci_mono_def] >> decide_tac) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> not_fresh_at mid x` by
    (rpt strip_tac >> gvs[ci_mono_def] >>
     irule not_fresh_at_mono >> qexists_tac `sn` >> simp[]) >>
  `type_slot_size tv < 2**256` by (fs[type_memory_size_slots] >> decide_tac) >>
  `eval_operand buf.buf_operand u = SOME (n2w (w2n w))` by simp[] >>
  `?z. gas_marked_path F ctx func u 0 (OK z) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\ copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    (!off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    z.vs_current_bb = se.cs_current_bb /\
    z.vs_inst_idx = LENGTH se.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee se z` by
    (irule extrequest_storage_suffix_joint >>
     goal_assum (drule_at Any) >> fs[ci_mono_def, wordsTheory.dimword_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!name b len. local_region cenv ee.scopes t name b len ==> _` irule >>
       qexists_tac `name` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `cenv.ce_is_ctor ==> _` mp_tac >> simp[] >>
       disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
     qexistsl_tac [`a`, `buf.buf_operand`, `p.ptr_location`, `p.ptr_operand`, `expr_type e`] >>
     gvs[comp_ignore_bind_def] >> metis_tac[]) >>
  `eval_operand buf.buf_operand z = SOME w` by
    (gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `sn.cs_next_id < se.cs_next_id` by
    (`mid.cs_next_id = sn.cs_next_id + 1` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[contextTheory.compile_alloc_buffer_def, emit_op_def, fresh_id_def, fresh_var_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        strip_tac >> gvs[]) >>
     gvs[ci_mono_def] >> decide_tac) >>
  `expr_post ctx func cenv cx e ee sa se t ee v buf.buf_operand z` by
    (irule copy_buffer_post_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`mk_inst sn.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
        [STRING #"%" (toString sn.cs_next_var)]`, `mid`, `t`, `sn`,
        `type_memory_size tv`, `u`, `LocatedValue (expr_type e) p`] >>
     simp[ci_mono_def, venomInstTheory.mk_inst_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
       qexists_tac `name` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!off len. regions_disjoint _ _ off len ==> _` mp_tac >>
       disch_then (qspecl_then [`off`, `len`] mp_tac) >>
       simp[regions_disjoint_def]) >>
     conj_tac >- fs[ci_mono_def] >>
     drule_all exprSimAllocTheory.buffer_alloc_code >>
     simp[venomInstTheory.mk_inst_def]) >>
  `gas_marked_path F ctx func t (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  `!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
     mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `compileEnv$regions_disjoint (w2n w) (type_memory_size tv) old_base old_size` by metis_tac[] >>
     metis_tac[]) >>
  qexistsl_tac [`v`, `z`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  `!tail. read_result cx r (ee with gas_obs := tail) =
      (INL v,ee with gas_obs := tail)` by
    (irule read_result_gas_obs >> simp[]) >>
  qpat_x_assum `gas_marked_path F ctx func t (0 + 0) (OK z)` mp_tac >>
  simp[] >> metis_tac[]
QED

Theorem extrequest_runtime_copy_envelope:
  w2n (a:bytes32) + 32*n < dimword (:256) /\
  w2n (w:bytes32) + 32*n < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F a w n 0 u).vs_memory ==>
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  !off len. regions_disjoint (w2n w) (32*n) off len ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory
Proof
  strip_tac >> Cases_on `n = 0`
  >- gvs[immutableCopyExecutionTheory.immutable_transfers_def] >>
  `immutable_transfers F F a w n 0 u =
    write_memory_with_expansion (w2n w)
      (TAKE (32*n) (DROP (w2n a) u.vs_data_section ++ REPLICATE (32*n) 0w)) u` by
    (qspecl_then [`n`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
      immutableCopyExecutionTheory.immutable_runtime_transfers_snapshot >>
     simp[]) >>
  gvs[] >> conj_tac
  >- simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion] >>
  rpt strip_tac >> irule write_memory_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def, listTheory.LENGTH_TAKE_EQ]
QED

(* Own the allocation witness and finalize one actual copying suffix. *)
Theorem extrequest_allocated_copy_joint:
  compile_alloc_buffer sz sn = (buf,mid) /\
  fn_has_code sn mid func /\ fn_inst_ids_distinct func /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee (Value v) vv t /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ sz < dimword (:256) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\ ci_mono mid sb /\
  (!u w. stmt_state_rel ctx func cenv cx ee u /\
    extrequest_history_frame cenv cx ee sn t ee mid u /\
    ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels /\
    FLOOKUP u.vs_allocas sn.cs_next_id = SOME (w2n w,sz) /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
    local_ptrs_reserved cenv mid /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
    (cenv.ce_is_ctor ==> !name tv' v' off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv',v') ==>
      regions_disjoint (w2n w) sz off (type_memory_size tv')) ==>
    ?z. gas_marked_path F ctx func u 0 (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_static z = copy_static u /\
      (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
      LENGTH u.vs_memory <= LENGTH z.vs_memory /\
      (!off len. regions_disjoint (w2n w) sz off len ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= sz /\ eval_operand buf.buf_operand z = SOME w) ==>
  ?z. gas_marked_path F ctx func t 0 (OK z) /\
    expr_post ctx func cenv cx e ee sa sb t ee v buf.buf_operand z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee sb z /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  qpat_x_assum `!u w. _` (qspecl_then [`u`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `cenv.ce_is_ctor ==> _` mp_tac >> simp[])) >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `mid` >> fs[ci_mono_def]) >>
  `sn.cs_next_id < sb.cs_next_id` by
    (`mid.cs_next_id = sn.cs_next_id + 1` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[contextTheory.compile_alloc_buffer_def, emit_op_def, fresh_id_def, fresh_var_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        strip_tac >> gvs[]) >>
     fs[ci_mono_def] >> decide_tac) >>
  `expr_post ctx func cenv cx e ee sa sb t ee v buf.buf_operand z` by
    (irule copy_buffer_post_transport >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`mk_inst sn.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sn.cs_next_var)]`, `mid`, `t`, `sn`, `sz`, `u`, `vv`] >>
     simp[ci_mono_def, venomInstTheory.mk_inst_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
       qexists_tac `name` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!off len. regions_disjoint _ _ off len ==> _` mp_tac >>
       disch_then (qspecl_then [`off`, `len`] mp_tac) >>
       simp[regions_disjoint_def]) >>
     conj_tac >- fs[ci_mono_def] >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> simp[venomInstTheory.mk_inst_def]) >>
  `extrequest_history_frame cenv cx ee sn t ee sb z` by
    (irule extrequest_copy_history >> goal_assum (drule_at Any) >>
     qexistsl_tac [`sz`, `w2n w`, `mid`, `u`] >> fs[ci_mono_def] >>
     conj_tac >- fs[copy_static_def] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` irule >>
       qexists_tac `aid` >> simp[]) >>
     `z.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
     simp[] >> qpat_x_assum `cenv.ce_is_ctor ==> _` ACCEPT_TAC) >>
  `!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
     mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `compileEnv$regions_disjoint (w2n w) sz old_base old_size` by metis_tac[] >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[] >>
  `gas_marked_path F ctx func t (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  pop_assum mp_tac >> simp[] >> metis_tac[]
QED

Theorem extrequest_copy_frame_path:
  copy_runtime_frame mid u sb z /\ fn_has_code mid sb func /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts mid sb) /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  gas_marked_path F ctx func u 0
    (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  z.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> conj_tac
  >- (irule extrequest_straight_run_path >> simp[] >> qexists_tac `mid` >>
      fs[copy_runtime_frame_def]) >>
  `z.vs_current_bb = u.vs_current_bb` suffices_by fs[copy_runtime_frame_def, same_blocks_def] >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts mid sb` >> fs[copy_runtime_frame_def] >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]
QED

Theorem extrequest_runtime_code_suffix:
  compile_imm_copy_to_memory F imm src dst (type_slot_size tv) 0 mid = ((),sb) /\
  fn_has_code mid sb func /\ copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  stmt_state_rel ctx func cenv cx ee u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx ty (Value v) a ee u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  strip_tac >> drule_all copy_runtime_run >> strip_tac >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    metis_tac[immutable_holds_bounds] >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) s'.vs_memory /\
    val_footprint tv v <= type_memory_size tv` by
    (irule copy_runtime_contents >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `LENGTH u.vs_memory <= LENGTH s'.vs_memory /\
    !off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
      mem_bytes_at off len s'.vs_memory = mem_bytes_at off len u.vs_memory` by
    (simp[type_memory_size_slots] >> irule extrequest_runtime_copy_envelope >>
     fs[type_memory_size_slots] >> qexists_tac `a` >> simp[]) >>
  `eval_operand dst s' = SOME w` by metis_tac[copy_runtime_frame_operand] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
    (drule code_copy_insts >> strip_tac >>
     gvs[emitted_insts_def, listTheory.DROP_APPEND] >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[venomInstTheory.is_terminator_def]) >>
  drule_all extrequest_copy_frame_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `s' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_runtime_frame_def, same_blocks_def, copy_static_def, lookup_var_def,
     eval_operand_def] >> gvs[]
QED

Theorem extrequest_ctor_code_suffix:
  compile_imm_copy_to_memory T imm src dst (type_slot_size tv) 0 mid = ((),sb) /\
  fn_has_code mid sb func /\ copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  (!region. imm = SOME region ==> eval_operand region u = SOME 0w /\
    copy_old_operand mid region) /\
  stmt_state_rel ctx func cenv cx ee u /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx ty (Value v) a ee u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size tv) (w2n w) (type_memory_size tv) /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  strip_tac >> drule_all copy_ctor_run >> strip_tac >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) zz.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    LENGTH u.vs_memory <= LENGTH zz.vs_memory /\
    (!off len. regions_disjoint (w2n w) (type_memory_size tv) off len ==>
      mem_bytes_at off len zz.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (drule_all copy_ctor_contents >> simp[regions_disjoint_def] >> metis_tac[]) >>
  `eval_operand dst zz = SOME w` by metis_tac[copy_runtime_frame_operand] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
    (drule code_ctor_copy_insts >> strip_tac >>
     gvs[emitted_insts_def, listTheory.DROP_APPEND] >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[venomInstTheory.is_terminator_def]) >>
  drule_all extrequest_copy_frame_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `zz with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_runtime_frame_def, same_blocks_def, copy_static_def, lookup_var_def,
     eval_operand_def] >> gvs[]
QED

Theorem extrequest_code_joint_copy:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type ty /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sn x) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r (LocatedValue ty p) t /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `?v. read_result cx r ee = (INL v,ee)` by
    (gvs[vv_post_def, vv_holds_def, immutable_holds_def] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t` by
    metis_tac[vv_post_read_result] >>
  `ty = expr_type e /\ ?a. eval_operand p.ptr_operand t = SOME a /\
    immutable_holds cenv cx ty (Value v) a ee t` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (fs[immutable_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    metis_tac[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> fs[] >>
  qpat_x_assum `cs'' = sb` (assume_tac o SYM) >> gvs[] >>
  rename1 `compile_alloc_buffer _ sn = (buf,mid)` >>
  `((type_memory_size tv + 31) DIV 32) = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  fs[contextTheory.compile_code_to_memory_def] >>
  rename1 `fn_has_code sn se func` >>
  `ci_mono mid se` by metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `cs_extends sn mid` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sn mid func /\ fn_has_code mid se func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `type_memory_size tv < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `?z. gas_marked_path F ctx func t 0 (OK z) /\
    expr_post ctx func cenv cx e ee sa se t ee v buf.buf_operand z /\
    z.vs_current_bb = se.cs_current_bb /\ z.vs_inst_idx = LENGTH se.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee se z /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k z.vs_memory = mem_bytes_at p k t.vs_memory)` by
    (irule extrequest_allocated_copy_joint >> goal_assum (drule_at Any) >> simp[] >>
     (reverse conj_tac >- (qexists_tac `LocatedValue (expr_type e) p` >> simp[])) >>
     qexistsl_tac [`mid`, `type_memory_size tv`] >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `ci_mono sn mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
     `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
       (fs[copy_old_operand_def] >> rpt strip_tac >> irule not_fresh_at_mono >>
        qexists_tac `sn` >> fs[ci_mono_def]) >>
     `u.vs_labels = t.vs_labels` by fs[extrequest_history_frame_def] >>
     `eval_operand p.ptr_operand u = SOME a` by
       (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
     `immutable_holds cenv cx (expr_type e) (Value v) a ee u` by
       (qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
        simp[immutable_holds_def]) >>
     Cases_on `cenv.ce_is_ctor`
     >- (`!region. cenv.ce_imm_alloca = SOME region ==>
            eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
           (gen_tac >> disch_tac >> conj_tac
            >- fs[stmt_state_rel_def, immutable_base_zero_def] >>
            fs[copy_old_operand_def, local_ptrs_reserved_def] >> metis_tac[]) >>
         `regions_disjoint (w2n a) (type_memory_size tv)
            (w2n w) (type_memory_size tv)` by
           (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
            drule_at (Pat `MEM _ _`) immutable_holds_alloca_disjoint >>
            simp[venomInstTheory.mk_inst_def] >>
            disch_then drule_all >> simp[]) >>
         `w2n w + type_memory_size tv < dimword (:256)` by decide_tac >>
         gvs[] >> drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
           extrequest_ctor_code_suffix >>
         simp[] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
         simp[] >> disch_then drule_all >>
         strip_tac >> qexists_tac `z` >> gvs[]) >>
     gvs[] >> drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
       extrequest_runtime_code_suffix >>
     simp[] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     simp[] >> disch_then drule_all >>
     strip_tac >> qexists_tac `z` >> gvs[]) >>
  qexistsl_tac [`v`, `z`] >> simp[gas_marked_exec_def] >>
  conj_tac >- (irule read_result_gas_obs >> simp[]) >>
  metis_tac[]
QED

Theorem extrequest_joint_unwrap_read:
  unwrap_value cenv vv sn = (op,sb) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e ee sa sn t ee r vv t` by
    (drule_all extrequest_endpoint_post >> simp[]) >>
  `local_ptrs_reserved cenv sn /\
   sc.cs_next_var <= sn.cs_next_var /\ sc.cs_next_id <= sn.cs_next_id` by
    fs[extrequest_history_frame_def] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  Cases_on `vv`
  >- (drule_all extrequest_stack_joint_read >> simp[]) >>
  rename1 `LocatedValue ty p` >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    (fs[exprSafeOperandTheory.safe_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_all extrequest_memory_joint_read >> simp[]) >>
  `ty = expr_type e` by fs[vv_post_def, vv_holds_def] >>
  Cases_on `is_word_type ty`
  >- (Cases_on `p.ptr_location = LocCode`
      >- (Cases_on `cenv.ce_is_ctor`
          >- (drule_all extrequest_ctor_joint_word >> simp[]) >>
          drule_all extrequest_runtime_joint_word >> simp[]) >>
      `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
        (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
      irule extrequest_storage_joint_word >> goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`p`, `ty`] >> simp[]) >>
  `!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    metis_tac[] >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule_all extrequest_code_joint_copy >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  irule extrequest_storage_joint_copy >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`p`, `ty`] >> gvs[] >> metis_tac[]
QED
