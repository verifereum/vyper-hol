(* Count and initialize the actual semantic/resource prologue landing. *)
Theory bodyIntCallJointEntry
Ancestors
  bodyIntCallRootFrame bodyIntCallJointContract fragGasSeq intCallCallee emitHelperProps
  fragExec exprLoweringProps entrySinkExtraction list rich_list
  loweringPosts intCallFrame compileEnv loweringStateRelDefs venomState arithmetic

Theorem internal_prologue_counted_landing:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ ~s.vs_halted /\
  s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts /\
  run_inst_seq (emitted_insts st0 st1) s = OK u ==>
  gas_path ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st0 st1)))
    (OK (u with vs_inst_idx := LENGTH st1.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb
Proof
  strip_tac >> drule compile_internal_prologue_shape >> strip_tac >>
  `emitted_insts st0 st1 = new` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st1.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st0 st1) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st1.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  metis_tac[run_inst_seq_preserves_entry_control]
QED

Theorem internal_root_joint_res_init:
  intcall_frame_ok fp /\
  stmt_state_rel fp.jc_ctx fp.jc_func fp.jc_root_ce fp.jc_cx es fp.jc_oorig /\
  expr_sim_inv fp.jc_root_ce fp.jc_cx env es /\
  ce_locals_declared fp.jc_root_ce env /\
  locals_alloc_ok fp.jc_root_ce env /\
  local_ptrs_reserved fp.jc_root_ce sa /\
  allocas_above fp.jc_lo fp.jc_oorig /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k fp.jc_oorig.vs_memory =
    mem_bytes_at a k fp.jc_morig.vs_memory) /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  (!n p k. local_region fp.jc_root_ce es.scopes fp.jc_oorig n p k ==>
    fp.jc_lo <= p \/
    ?b z. fp.jc_staged b z /\ b <= p /\ p + k <= b + z) /\
  return_buf_frame fp.jc_rb fp.jc_root_ce sa fp.jc_oorig /\
  (!bw cap. fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_is_ctor ==>
    !nm tv iv io.
    FLOOKUP fp.jc_root_ce.ce_module_vars (fp.jc_root_ce.ce_module,nm) =
      SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables fp.jc_root_ce.ce_module imms)
      nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) ==>
  intcall_joint_res fp fp.jc_root_ce env es sa
    (fp.jc_oorig with vs_inst_idx := LENGTH sa.cs_current_insts)
Proof
  strip_tac >>
  `ret_pc_ok fp.jc_root_ce sa fp.jc_oorig` by
    (fs[ret_pc_ok_def, intcall_frame_ok_def] >>
     gen_tac >> strip_tac >> gvs[] >>
     qpat_x_assum `!op. fp.jc_reserved op ==> _` drule >>
     strip_tac >> gvs[]) >>
  `eval_operand fp.jc_rpc fp.jc_oorig = SOME fp.jc_pc` by
    fs[intcall_frame_ok_def] >>
  Cases_on `fp.jc_rb`
  >- (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_inst_idx,
         allocas_above_def, local_region_def, ret_pc_ok_def,
         return_buf_frame_def, lookup_var_def, ADD_COMM] >> metis_tac[]) >>
  rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
  fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_inst_idx,
     allocas_above_def, local_region_def, ret_pc_ok_def,
     return_buf_frame_def, lookup_var_def, ADD_COMM] >>
  metis_tac[]
QED
