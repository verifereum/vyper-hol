Theory extcallProtFrameJointUnwrap
Ancestors
  extcallProtFrameUnwrapRead extcallProtFrameUnwrapStorage
  extcallProtFrameUnwrapCode extcallProtFrameKwargUnwrap
  exprExtRequestJointUnwrap exprExtRequestHistory exprExtRequestUnwrapAdapter exprSafeOperand
  loweringPosts exprLoweringProps compileEnv freshWrites
  gasSummary fragGasMode fragGasPath venomState exprLowering
  valueEncodingProps vyperInterpreter vyperState exprSimMemorySource loweringStateRelDefs valueEncodingDefs

Theorem extcall_joint_unwrap_read_protected:
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
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u /\
    (!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e ee sa sn t ee r vv t` by
    (drule_all extrequest_endpoint_post >> simp[]) >>
  `local_ptrs_reserved cenv sn /\
   sc.cs_next_var <= sn.cs_next_var /\ sc.cs_next_id <= sn.cs_next_id` by
    fs[extrequest_history_frame_def] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  Cases_on `vv`
  >- (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) extcall_identity_joint_read >> simp[] >> strip_tac >>
      `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
        mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
        !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n` by
        (rpt gen_tac >> disch_tac >> irule extcall_protframe_readonly_path >>
         fs[gas_marked_exec_def] >>
         goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
         qexists_tac `prot` >> simp[] >> metis_tac[]) >>
      qexistsl_tac [`v`, `u`] >> simp[] >> metis_tac[]) >>
  rename1 `LocatedValue ty p` >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    (fs[safe_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  Cases_on `is_word_type ty`
  >- (drule_all extcall_word_joint_read >> strip_tac >>
      `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
        mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
        !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n` by
        (rpt gen_tac >> disch_tac >> irule extcall_protframe_readonly_path >>
         fs[gas_marked_exec_def] >>
         goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
         qexists_tac `prot` >> simp[] >> metis_tac[]) >>
      qexistsl_tac [`v`, `u`] >> simp[] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) extcall_identity_joint_read >> simp[] >> strip_tac >>
      `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
        mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
        !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n` by
        (rpt gen_tac >> disch_tac >> irule extcall_protframe_readonly_path >>
         fs[gas_marked_exec_def] >>
         goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
         qexists_tac `prot` >> simp[] >> metis_tac[]) >>
      qexistsl_tac [`v`, `u`] >> simp[] >> metis_tac[]) >>
  `ty = expr_type e` by fs[vv_post_def, vv_holds_def] >>
  `!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64` by
    metis_tac[] >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule_all extcall_protframe_code_joint_copy >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  irule extcall_protframe_storage_joint_copy >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`p`, `ty`] >> gvs[]
QED
