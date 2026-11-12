(* Read-only unwrap endpoints with history and exact memory equality. *)
Theory extcallProtFrameUnwrapRead
Ancestors
  exprExtRequestJointUnwrap exprExtRequestHistory bodyIntCallWordLanding
  bodyIntCallForcingReadOnly exprSimUnwrap exprSimUnwrapProps exprSimHash
  exprLoweringProps loweringPosts compileEnv venomState venomExecSemantics
  valueEncodingProps vyperInterpreter vyperState exprLowering freshWrites
  fragGasMode fragGasPath gasSummary emitHelperProps
  valueCopyBytes valueEncoding exprSimMemorySource loweringStateRelDefs valueEncodingDefs

Theorem extcall_readonly_word_finalize:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue ty p) t /\
  is_word_type (expr_type e) /\ sa.cs_next_var <= sn.cs_next_var /\
  local_ptrs_reserved cenv sn /\
  sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id /\
  u = t with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
  (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
  eval_operand op u = SOME w /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    w = typed_val_to_w256 tv v) ==>
  expr_post ctx func cenv cx e ee sa sb t ee v op u /\
  extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sn` >> simp[]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_load >> simp[] >>
      `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
      `stmt_state_rel ctx func cenv cx ee u` by
        (irule forcing_readonly_state_rel >>
         qexistsl_tac [`LENGTH sb.cs_current_insts`, `t`, `sn`] >> simp[]) >>
      simp[] >> qexistsl_tac [`p`, `t`, `sn`, `ty`] >> simp[]) >>
  irule extrequest_unchanged_memory_history >> simp[]
QED

Theorem extcall_word_joint_read:
  unwrap_value cenv (LocatedValue ty p) sn = (op,sb) /\
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
    (!aid b k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       mem_bytes_at b k u.vs_memory = mem_bytes_at b k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u /\
    u.vs_memory = t.vs_memory
Proof
  strip_tac >>
  `ty = expr_type e` by
    (fs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >> gvs[] >>
  `?a v. eval_operand p.ptr_operand t = SOME a /\ read_result cx r ee = (INL v,ee)` by
    (Cases_on `p.ptr_location` >>
     gvs[vv_post_def, vv_holds_def, storage_holds_def, immutable_holds_def]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) (LocatedValue (expr_type e) p) t` by
    metis_tac[vv_post_read_result] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> simp[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value v) _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def]) >>
  `cenv.ce_is_ctor ==> !region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region t = SOME 0w` by fs[stmt_state_rel_def, immutable_base_zero_def] >>
  `?b. (p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
      eval_operand (THE cenv.ce_imm_alloca) t = SOME b) /\
    !tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    (case p.ptr_location of
       LocStorage => sload a t | LocTransient => tload a t
     | LocCode => if cenv.ce_is_ctor then
         mload (w2n (if cenv.ce_imm_alloca = NONE then a else a+b)) t
       else word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) t.vs_data_section ++ REPLICATE 32 0w))
     | _ => mload (w2n a) t) = typed_val_to_w256 tv v` by
    (qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ r _ _` kall_tac >>
     qexists_tac `0w` >> Cases_on `p.ptr_location` >>
     gvs[vv_post_def, vv_holds_def, read_result_def, return_def, mload_def, mem_word_at_def] >>
     Cases_on `cenv.ce_is_ctor` >> fs[]
     >~ [`immutable_holds _ _ _ _ _ _ _`, `~cenv.ce_is_ctor`]
       >- (drule_all immutable_holds_dload >> strip_tac >> gvs[]) 
     >~ [`immutable_holds _ _ _ _ _ _ _`, `cenv.ce_is_ctor`]
       >- (Cases_on `cenv.ce_imm_alloca` >> fs[] >>
           drule_all immutable_holds_iload >> strip_tac >>
           gvs[mload_def, mem_word_at_def, wordsTheory.WORD_ADD_0]) >>
     metis_tac[storage_holds_load]) >>
  drule (Q.INST
    [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sn x`]
    (SPEC_ALL protected_word_unwrap_landing)) >> simp[] >>
  disch_then (qspec_then `sn` mp_tac) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`ee.scopes`, `ctx`] strip_assume_tac) >>
  `!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t` by
    (rpt strip_tac >>
     qpat_x_assum `!q. _ ==> eval_operand q u = eval_operand q t`
       (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  `sn.cs_next_var <= sb.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`cenv`, `LocatedValue (expr_type e) p`, `sn`]
       ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    extrequest_history_frame cenv cx ee sn t ee sb u` by
    (irule extcall_readonly_word_finalize >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`p`, `expr_type e`] >> simp[]) >>
  `u.vs_memory = t.vs_memory` by
    (qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  qexistsl_tac [`v`, `u`] >> simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[read_result_gas_obs]
QED

Theorem extcall_identity_joint_read:
  unwrap_value cenv vv sn = (op,sb) /\
  (case vv of StackValue _ _ => T
   | LocatedValue ty p => p.ptr_location = LocMemory /\ ~is_word_type ty) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e ee sa sn t ee r vv t /\
  local_ptrs_reserved cenv sn /\ ~t.vs_halted /\
  t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid b k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       mem_bytes_at b k u.vs_memory = mem_bytes_at b k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u /\
    u.vs_memory = t.vs_memory
Proof
  strip_tac >>
  `?v. read_result cx r ee = (INL v,ee)` by
    (Cases_on `vv` >> gvs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e ee sa sn t ee (Value v) vv t` by
    metis_tac[vv_post_read_result] >>
  `sb = sn` by
    (Cases_on `vv` >> gvs[unwrap_value_def, comp_return_def]) >> gvs[] >>
  qexistsl_tac [`v`, `t`] >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
      conj_tac >- metis_tac[read_result_gas_obs] >>
      irule (cj 1 gas_path_rules) >> simp[]) >>
  reverse conj_tac >- (irule extrequest_history_frame_refl >> simp[]) >>
  Cases_on `vv` >> gvs[unwrap_value_def, comp_return_def]
  >- (metis_tac[expr_post_of_vv_post_stack]) >>
  metis_tac[expr_post_of_vv_post_memory]
QED
