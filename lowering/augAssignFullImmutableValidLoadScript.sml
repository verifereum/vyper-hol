(* Immutable loads retain one framed endpoint on the actual valid domain. *)
Theory augAssignFullImmutableValidLoad
Ancestors
  augAssignFullImmutableSetup augAssignFullLoadImmutableResources
  augAssignFullLoadMemoryStep augAssignFullLoadFrame bodyImmutableAugAssignFacts
  bodyFullTargetDefs vyperTypeCallStackSoundness bodyPtrDefs exprSimHypsDefs
  stmtSimAugAssignPlace gasOutcomeFull emitHelperProps exprLoweringProps
  freshWrites ptrDiscipline venomExecSemantics venomInst venomState
  stateFrame compileEnv finite_map words list arithmetic loweringShapeRules
  context exprPtrCtorCodeLoad exprSimCopy immutableWordExecution immutableCopyExecution
  exprSimBopRestWordLoadSafety bodyFullUnwrapRun fragGasOriginPtrDead rich_list

Theorem augassign_immutable_load_valid_framed_joint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  call_evaluation_safe cx
    (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    dead_lo_ok H (DF H) lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    ghost_kept_at lo cenv es entry G0 tn0 s0 G tn) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ alloca_history func s
  ==>
  ?off tv cur.
    cx.in_deploy /\ src = cenv.ce_module /\ cenv.ce_is_ctor /\ ty = ity /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es) /\
    (!sa old sb.
      emit_op MLOAD [Lit (n2w off)] sa = (old,sb) /\
      fn_has_code sa sb func /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      local_ptrs_reserved cenv sa /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      entry.cs_next_var <= sa.cs_next_var /\ return_buf_frame d cenv sa s
      ==>
      ?u G1 tn1.
        !H. valid_horizon cx st0 H es.storage_trace ==>
          off + 32 <= lo /\ w2n ((n2w off):bytes32) = off /\
          mload off s = typed_val_to_w256 tv cur /\
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) [] (OK u,G1,tn1) /\
          eval_operand old u = SOME (typed_val_to_w256 tv cur) /\
          eval_operand (Lit (n2w off)) u = SOME (n2w off) /\
          op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
          (!x. old = Var x ==> not_fresh_at sb x) /\
          local_ptrs_reserved cenv sb /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
          stmt_state_rel H ctx func cenv cx es u /\
          ghost_inv_at (DF H) lo d cenv cx es G1 tn1 u /\
          target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
            (Lit (n2w off),SOME LocMemory,SOME (ValPT ty)) G1 tn1 u /\
          ghost_kept_at lo cenv es entry G0 tn0 s0 G1 tn1 /\
          return_buf_frame d cenv sb u /\ alloca_history func u /\
          u.vs_alloca_next = s.vs_alloca_next /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts /\
          state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
          (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s))
Proof
  strip_tac >>
  `cx.in_deploy` by metis_tac[augassign_immutable_in_deploy] >>
  `call_evaluation_safe cx []` by
    (irule call_evaluation_safe_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  qexistsl_tac [`off`, `tv`, `v`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MLOAD [Lit (n2w off)] [x]` >>
  qabbrev_tac `raw = update_var x (mload off s) s` >>
  qabbrev_tac `u = (raw with vs_inst_idx := SUC s.vs_inst_idx)` >>
  qabbrev_tac `G1 = step_prov PG G i raw` >>
  qabbrev_tac `tn1 = step_taint i s raw tn` >>
  qexistsl_tac [`u`, `G1`, `tn1`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all augassign_immutable_load_resources >> strip_tac >>
  gvs[] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK u,G1,tn1) /\
   eval_operand old u = SOME (mload off s) /\
   eval_operand (Lit (n2w off)) u = SOME (n2w off) /\
   op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s /\
     FLOOKUP G1 q = FLOOKUP G q /\
     op_taint tn1 (Var q) = op_taint tn (Var q))` by suspend "step" >>
  suspend "frame"
QED

Resume augassign_immutable_load_valid_framed_joint[step]:
  qpat_assum `!iid out. ptr_inst_ok _ _ _ _ _ _ _ _ _`
    (qspecl_then [`sa.cs_next_id`, `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >>
  qspecl_then [`\h. T`, `\h. DF H`] (mp_tac o SRULE [])
    augassign_mload_joint_step >>
  disch_then (drule_at (Pos last)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (qspecl_then [`explicit`, `PG`, `n2w off`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[Abbr `x`, Abbr `i`, Abbr `raw`, Abbr `u`, Abbr `G1`, Abbr `tn1`,
    update_var_def]
QED

Resume augassign_immutable_load_valid_framed_joint[frame]:
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by simp[] >>
  qmatch_goalsub_abbrev_tac `target_ptr_ok cenv (PlaceR place) target G1 tn1 u` >>
  `target_ptr_ok cenv (PlaceR place) target G tn s` by
    simp[Abbr `place`, Abbr `target`, target_ptr_ok_def, op_taint_def] >>
  drule_at (Pos hd) augassign_load_endpoint_frame >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `target_ptr_ok _ _ _ _ _ _`)) >>
  disch_then drule >>
  disch_then (drule_at (Pat `state_frame _ = _`)) >>
  disch_then (drule_at (Pos (el 11))) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspec_then `n2w off` mp_tac) >>
  (impl_tac >- simp[Abbr `target`, eval_operand_def, mk_inst_def]) >> strip_tac >>
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s` by
    (qx_gen_tac `q` >> disch_tac >>
     qpat_assum `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sa` >> simp[]
QED

Finalise augassign_immutable_load_valid_framed_joint

(* The immutable load may emit an ADD before ILOAD. Use the constructor word
   load facts for its endpoint and lift the sequence at every horizon. *)
Theorem augassign_ctor_word_load_at:
  compile_imm_load_word T imm arg sa = (op,sb) /\
  copy_old_operand sa arg /\ eval_operand arg s = SOME a /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE) /\
  mem_word_taint tn.t_mem (w2n a) = {} ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  ?u G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    eval_operand op u = SOME (mload (w2n a) s) /\
    op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule rest_word_ptr_load_mem_ok >>
     qexistsl [`a`,`arg`,`T`,`imm`,`LocCode`,`op`] >>
     simp[contextTheory.compile_ptr_load_def] >>
     Cases_on `imm` >> fs[] >> rpt strip_tac >> decide_tac) >>
  drule copy_ctor_load_shape >>
  simp[same_blocks_def] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)`
       (assume_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i (emitted_insts sa sb) ==> _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  qabbrev_tac `emptyDead = <|d_stor := K (K {}); d_trans := K (K {});
                            d_imm := K {}; d_ret := K {}|>` >>
  drule_all code_copy_ctor_load >>
  disch_then (qspecl_then [`func`,`PG`,`emptyDead`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sb raw` >>
  `run_inst_seq (emitted_insts sa sb) s = OK raw /\
    sb.cs_current_bb = sa.cs_current_bb` by fs[copy_runtime_frame_def, same_blocks_def] >>
  `inst_seq_ptr emptyDead lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx`
         (ACCEPT_TAC o REWRITE_RULE [venom_state_fupdselfid]))) >>
  `gas_origin_ptr_path (emptyDead,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     simp[] >> qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
     simp[]) >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tnf`] >>
  simp[IgnAsm `sb.cs_current_insts = _`] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
      fs[Abbr `emptyDead`, IgnAsm `sb.cs_current_insts = _`]) >>
  `state_frame (raw with vs_inst_idx := LENGTH sb.cs_current_insts) =
   state_frame (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~raw.vs_halted /\ raw.vs_current_bb = sb.cs_current_bb` by
    (Cases_on `imm`
     >- (gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >>
         strip_tac >> fs[copy_runtime_frame_def, run_inst_seq_def,
                         step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
         gvs[state_frame_def, update_var_def]) >>
     rename1 `compile_imm_load_word T (SOME region) arg sa = (op,sb)` >>
     `eval_operand region s = SOME 0w` by fs[] >>
     drule_all compile_imm_load_word_ctor_execution >>
     strip_tac >> gvs[state_frame_def, update_var_def]) >>
  fs[immutable_copy_read_def, eval_operand_def, lookup_var_def,
     copy_old_operand_def, copy_runtime_frame_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem augassign_ctor_word_load:
  compile_imm_load_word T imm (Lit a) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE) /\
  mem_word_taint tn.t_mem (w2n a) = {} ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  ?u G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    eval_operand op u = SOME (mload (w2n a) s) /\
    op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `copy_old_operand sa (Lit a) /\ eval_operand (Lit a) s = SOME a /\
   op_taint tn (Lit a) = {} /\ op_prov G (Lit a) = NONE` by
    simp[copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (Q.INST [`arg` |-> `Lit a`] augassign_ctor_word_load_at) >>
  disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)
QED
