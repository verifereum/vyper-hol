Theory bodyFullForArrayDynamicStart
Ancestors
  bodyFullForArrayDynamicScalar bodyPtrBopInMemoryContents
  exprPtrCtorImmStore reasonCopySourcePtr valueEncoding valueEncodingProps
  memoryValueEncoding loweringStateRelDefs bodyPtrDefs exprLoweringProps
  bodyFullGhostFrame bodyMemoryDefs bodyPtrMakeArrayEmission emitHelperProps
  bodyFullUnwrapRun fragExecMem memSafeRun instMemFrontier
  exprSimHypsDefs vyperTypeStatePreservation vyperTyping vyperValueOperation exprSimOperands
  abiBuiltinAllocation fragExec rich_list bodyFullAllocaFresh
  bodyFullForArrayInit bodyFullForArrayFixedStart forPtrCheckedScalar
  instSeqPtrLo fragGasSeqPtr ptrDiscipline ptrSafeRun venomExecSemantics
  venomState venomInst finite_map pred_set words list codegenRel contextCodegenRel

(* The checked dynamic bound has one scalar ghost endpoint for every mask. *)
Theorem for_array_dynamic_scalar_sequence_full:
  ALL_DISTINCT [lv;idx;g;vld] /\
  lookup_var lv s = SOME (n2w len) /\ len <= c /\ c < dimword (:256) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?Gf tf. (!D. inst_seq_ptr D lo ctx func PG G tn
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] s Gf tf) /\
    FLOOKUP Gf idx = NONE /\ FLOOKUP Gf lv = NONE /\
    op_taint tf (Var idx) = {} /\ op_taint tf (Var lv) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. ~MEM x [idx;g;vld] ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> `len < dimword (:256)` by decide_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {g})) (COMPL {vld})`,
    `tn with t_var := tn.t_var |+ (idx,{}) |+ (g,{}) |+ (vld,{})`] >>
  reverse conj_tac
  >- gvs[ALL_DISTINCT,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
  gen_tac >> irule inst_seq_ptr_zero_to_lo >>
  simp[] >> qexists_tac `D` >> simp[] >>
  simp[Once (for_checked_scalar_seq_cons |> Q.INST [`w` |-> `0w`]),
       step_inst_base_opcode_eqs,mk_inst_def,exec_pure1_def,
       eval_operand_def,op_taint_def,op_prov_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_bound_gt_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_iszero_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  dep_rewrite.DEP_REWRITE_TAC[for_array_assert_one_cons] >>
  conj_tac
  >- gvs[lookup_var_def,update_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def,ALL_DISTINCT] >>
  simp[inst_seq_ptr_def,INTER_ASSOC]
QED

(* The local relation supplies the length; the robust ghost relation, not
   allocation identity, supplies the clean header bytes. *)
Theorem for_array_dynamic_header_full[local]:
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv (Dynamic c) /\
  ent.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
  value_has_type ent.type ent.value /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ?base. lookup_var ap s = SOME base /\
    mload (w2n base) s = n2w (LENGTH vs) /\
    ptr_covers G tn ap s 32 /\
    mem_word_taint tn.t_mem (w2n base) = {}
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >>
  `32 <= az` by
    (qpat_x_assum `type_memory_size _ <= az` mp_tac >>
     simp[type_memory_size_def]) >>
  `mload (w2n w) s = n2w (LENGTH vs)` by
    (drule memory_value_rel_val_in_memory >>
     simp[val_in_memory_dynarray,GSYM mem_word_at_eq_mload] >>
     gvs[val_in_memory_dynarray,GSYM mem_word_at_eq_mload,
         memory_value_rel_val_in_memory]) >>
  `ptr_covers G tn ap s az /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Dynamic c)) (ArrayV (DynArrayV vs))
       (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule ptr_covers_mono >> qexists_tac `az` >> simp[]) >>
  irule dynarray_memory_header_clean >> goal_assum (drule_at Any)
QED

(* Uniform MLOAD ghosts are chosen once; only their certificate depends on D. *)
Theorem for_array_dynamic_load_sequence_full[local]:
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv (Dynamic c) /\
  ent.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
  value_has_type ent.type ent.value /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D0 lo d cenv cx es G tn s /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tf.
    (!D k. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst mi MLOAD [Var ap] [lv]] (s with vs_inst_idx := k) Gf tf) /\
    FLOOKUP Gf lv = NONE /\ op_taint tf (Var lv) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> lv ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    run_inst_seq [mk_inst mi MLOAD [Var ap] [lv]] s =
      OK (update_var lv (n2w (LENGTH vs)) s)
Proof
  strip_tac >> drule_all for_array_dynamic_header_full >> strip_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `run_inst_seq [mk_inst mi MLOAD [Var ap] [lv]] s =
    OK (update_var lv (n2w (LENGTH vs)) s)` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         exec_read1_def,eval_operand_def] >>
  qabbrev_tac `u = update_var lv (n2w (LENGTH vs)) s` >>
  qabbrev_tac `ins = mk_inst mi MLOAD [Var ap] [lv]` >>
  qexistsl_tac [`step_prov PG G ins u`,`step_taint ins s u tn`] >>
  `!D. ?Gf tf.
    (!k. inst_seq_ptr D lo ctx func PG G tn [ins]
      (s with vs_inst_idx := k) Gf tf) /\
    op_taint tf (Var lv) = {} /\ op_prov Gf (Var lv) = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> lv ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` by
    (gen_tac >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
     simp[Abbr `ins`] >>
     drule_all (SRULE [] (Q.INST
       [`P` |-> `\x:string. x <> lv`, `out` |-> `lv`] ctor_mload_segment)) >>
     disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     qexistsl_tac [`Gf`,`tnf`] >> simp[]) >>
  `!D Gf tf. (!k. inst_seq_ptr D lo ctx func PG G tn [ins]
      (s with vs_inst_idx := k) Gf tf) ==>
    Gf = step_prov PG G ins u /\ tf = step_taint ins s u tn` by
    (rpt gen_tac >> disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
     simp[inst_seq_ptr_def] >>
     `step_inst_base ins s = OK u` by
       simp[Abbr `ins`,Abbr `u`,step_inst_base_opcode_eqs,mk_inst_def,
            exec_read1_def,eval_operand_def] >> simp[]) >>
  `?Gf tf. (!k. inst_seq_ptr D0 lo ctx func PG G tn [ins]
      (s with vs_inst_idx := k) Gf tf) /\
    op_taint tf (Var lv) = {} /\ op_prov Gf (Var lv) = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> lv ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` by metis_tac[] >>
  `Gf = step_prov PG G ins u /\ tf = step_taint ins s u tn` by metis_tac[] >>
  qpat_x_assum `Gf = step_prov PG G ins u` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `tf = step_taint ins s u tn` (SUBST_ALL_TAC o SYM) >>
  fs[op_prov_def] >> metis_tac[]
QED

Theorem for_array_dynamic_prefix_full:
  emit_op MLOAD [Var ap] st = (Var lv,sa) /\
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  sz < dimword (:256) /\ c < dimword (:256) /\
  local_ptrs_reserved cenv st /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv (Dynamic c) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\ LENGTH vs <= c /\
  return_buf_frame d cenv st s /\ alloca_history func s /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dst t Gp tp.
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gp lv = NONE /\ op_taint tp (Var lv) = {} /\
    lookup_var p t = SOME dst /\ ptr_covers Gp tp p t sz /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= t.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes t nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d cenv sb t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\ allocas_from lo t /\
      ghost_inv_at (DF H) lo d cenv cx es Gp tp t) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)) /\
    (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==>
      FLOOKUP t.vs_allocas aid = SOME bl) /\
    (?base. lookup_var ap s = SOME base /\
      mload (w2n base) s = n2w (LENGTH vs) /\
      ptr_covers G tn ap s 32 /\ mem_word_taint tn.t_mem (w2n base) = {}) /\
    exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p])
      ((update_var lv (n2w (LENGTH vs)) s) with
        vs_inst_idx := LENGTH sa.cs_current_insts) (n2w sz : bytes32) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts) /\
    (!D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst st.cs_next_id MLOAD [Var ap] [lv];
       mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] s Gp tp) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gp,tp))
Proof
  strip_tac >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by metis_tac[] >>
  `stmt_state_rel H0 ctx func cenv cx es s /\
   ghost_inv_at (DF H0) lo d cenv cx es G tn s` by metis_tac[] >>
  `value_has_type ent.type ent.value` by
    (irule lookup_scopes_state_well_typed_value_has_type >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `av = DynArrayV vs` by
    (Cases_on `av` >> gvs[value_has_type_def,array_elements_def]) >>
  `ent.value = ArrayV (DynArrayV vs)` by metis_tac[] >>
  qpat_x_assum `vs = array_elements _ _` kall_tac >>
  drule_all for_array_dynamic_header_full >> strip_tac >>
  drule_all for_array_dynamic_load_sequence_full >>
  disch_then (qspecl_then [`st.cs_next_id`,`lv`,`PG`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `lv = STRING #"%" (toString st.cs_next_var)` by metis_tac[operand_11] >>
  `!x. not_fresh_at st x ==> x <> lv /\ not_fresh_at sa x` by
    simp[not_fresh_at_def] >>
  `not_fresh_at sa lv` by simp[not_fresh_at_def] >>
  `local_ptrs_reserved cenv sa` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by metis_tac[] >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by metis_tac[] >>
  qabbrev_tac `u = (update_var lv (n2w (LENGTH vs)) s) with
    vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> `x <> lv` by metis_tac[] >>
     conj_tac
     >- (simp[NoAsms,Abbr `u`,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
         metis_tac[]) >> metis_tac[]) >>
  `!HH. valid_horizon cx st0 HH es.storage_trace ==>
    stmt_state_rel HH ctx func cenv cx es u /\
    ghost_inv_at (DF HH) lo d cenv cx es Gf tf u` by
    (qx_gen_tac `HH` >> disch_tac >> conj_tac
     >- (simp[Abbr `u`,stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >> reverse conj_tac >- metis_tac[] >>
         irule fresh_not_local_ptr >> qexists_tac `st` >> simp[not_fresh_at_def]) >>
     irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`es`,`s`,`st`,`tn`] >>
     simp[Abbr `u`,update_var_def] >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx es u /\
   ghost_inv_at (DF H0) lo d cenv cx es Gf tf u` by metis_tac[] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
   u.vs_inst_idx = LENGTH sa.cs_current_insts` by
    fs[Abbr `u`,update_var_def,same_blocks_def] >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `sa.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id MLOAD [Var ap] [lv]]` by metis_tac[] >>
  `same_blocks sa sb` by metis_tac[emit_op_extends] >>
  `fn_has_code st sa func` by
    (drule emitted_insts_emit_op >> strip_tac >>
     fs[fn_has_code_def,emitted_blocks_def,same_blocks_def,IS_PREFIX_APPEND] >>
     metis_tac[APPEND_ASSOC]) >>
  `alloca_history func u` by
    (simp[NoAsms,Abbr `u`] >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`[mk_inst st.cs_next_id MLOAD [Var ap] [lv]]`,`s`,`st`] >>
     simp[mk_inst_def,is_terminator_def] >>
     fs[stmt_state_rel_def,same_blocks_def]) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tf`,`explicit`,`PG`,`Gf`] strip_assume_tac) >>
  `q = p` by metis_tac[operand_11] >>
  qpat_x_assum `q = p` SUBST_ALL_TAC >>
  `!HH. valid_horizon cx st0 HH es.storage_trace ==>
    ghost_inv_at (DF HH) lo d cenv cx es G' tn' t` by
    (gen_tac >> disch_tac >> irule (INST_TYPE [``:'a`` |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gf`,`HH`,`ctx`,`w2n w + sz`,`func`,`u`,`sa`,`tf`] >>
     metis_tac[]) >>
  `t.vs_memory = u.vs_memory /\ t.vs_halted = u.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
   s.vs_alloca_next <= t.vs_alloca_next` by
    (fs[Abbr `u`,update_var_def]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `lookup_var lv u = SOME (n2w (LENGTH vs))` by
    simp[NoAsms,Abbr `u`,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `lookup_var lv t = SOME (n2w (LENGTH vs)) /\ FLOOKUP G' lv = NONE /\
    op_taint tn' (Var lv) = {}` by metis_tac[] >>
  `st.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `emit_op ALLOCA _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> simp[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`st`] >>
     metis_tac[]) >>
  qexistsl_tac [`w`,`t`,`G'`,`tn'`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid e. FLOOKUP u.vs_allocas aid = SOME e ==> _` irule >>
    simp[Abbr `u`,update_var_def]) >>
  cheat
QED
