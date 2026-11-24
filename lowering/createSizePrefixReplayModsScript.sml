Theory createSizePrefixReplayMods
Ancestors
  createSizePrefixReplay createExprSizeExitDefsMods
  abiEncoderProps exprSimFullBundleProps fragExec fragGasOrigin fragGasPath gasExplicitSites
  s1PrefixDefs venomExecSemantics venomInst venomState vyperState relation list words
  createMarkedPath pair createResultTail bodyFullIfExpReach builtinCreate arithmetic
  exprLowering vfmConstants compileEnv rich_list exprSimHypsDefs bodyPtrDefs loweringPosts
  context vyperValue integer_word valueEncoding createSizeEdgePC exprSimMemDefs
  ptrDiscipline bodySim createExprSizeExitDefs

Theorem create_size_replay_value_cut_mods:
  !mods exps src cx e DF lo d (PG : (num # num) option list) tops
    ctx shadow_ctx func shadow_func cenv env ty es
    st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    expr_body_pre_mods mods cenv cx env e es /\
    expr_sim_full_pre_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
    create_operand_completed_ok_mods mods exps cx e ==>
    gas_completed_operand_mods
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      mods cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
      (es,s0,G0,tn0)
      (expr_sim_full_post_mods (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s0,op,G0,tn0))
Proof
  strip_tac >> metis_tac[create_operand_completed_ok_mods_def]
QED

Theorem create_size_replay_vv_cut_mods:
  !mods exps src cx e DF lo d (PG : (num # num) option list) tops
    ctx shadow_ctx func shadow_func cenv env ty es
    st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    expr_body_pre_mods mods cenv cx env e es /\
    expr_vv_sim_full_pre_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es
      (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
    create_operand_completed_ok_mods mods exps cx e ==>
    gas_completed_operand_mods
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      mods cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G tn t. ?tv. res = INL tv /\
        vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
        vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
          ee tv vv t /\
        alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem)) /\
        (!t' op. vv = StackValue t' op /\
           ~is_word_type (post_value_type cenv e) ==>
             ptr_buf_ok cenv e op G t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok cenv e p.ptr_operand G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
Proof
  strip_tac >> metis_tac[create_operand_completed_ok_mods_def]
QED

Theorem create_dispatch_no_return_mods:
  cs_extends sa sc /\ emit_op opc ops sc = (created,sd) /\
  MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s marks t /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (t.vs_current_bb <> sb.cs_current_bb \/ t.vs_inst_idx <> LENGTH sb.cs_current_insts) ==>
  t = s /\ marks = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_result_tail_dispatch_code >> strip_tac >>
  `~is_terminator i.inst_opcode` by
    fs[is_terminator_def] >>
  qpat_x_assum `MEM opc _` kall_tac >>
  `~(t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)`
    by metis_tac[] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  strip_tac
  >- (fs[] >> metis_tac[]) >>
  rename1 `RTC _ mid (t,marks)` >>
  PairCases_on `mid` >> gvs[create_marked_edge_def] >>
  rename1 `RTC _ (mid0,mid1) (t,marks)` >>
  `gas_origin_edge F explicit ctx func s mid1 (OK mid0)` by
    fs[create_prefix_step_def] >>
  `mid0.vs_current_bb = sd.cs_current_bb /\ mid0.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME cb /\
      get_instruction cb s.vs_inst_idx = SOME i` by simp[] >>
     drule_all createSizeEdgePCTheory.create_ok_edge_pc >> simp[]) >>
  reverse (Cases_on `rof`)
  >- (gvs[compile_check_create_result_def, compileEnvTheory.comp_return_def] >>
      qpat_x_assum `RTC _ (mid0,mid1) _` mp_tac >>
      once_rewrite_tac[RTC_CASES1] >> simp[] >>
      simp[EXISTS_PROD, create_marked_edge_def, create_prefix_step_def] >> strip_tac >> gvs[]) >>
  drule_all create_result_check_layout >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi_mods] >>
  rename1 `j.inst_operands = [created; Label sb.cs_current_bb; Label fail_lab]` >>
  `fail_lab <> sd.cs_current_bb` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LAST : opcode list -> opcode``) >>
     simp[]) >>
  `get_instruction cb (LENGTH sd.cs_current_insts) = SOME j` by
    gvs[get_instruction_def, EL_APPEND_EQN] >>
  qabbrev_tac `region = \u:venom_state.
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = 0 \/
    u.vs_current_bb = fail_lab /\ u.vs_inst_idx < 4 \/
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts` >>
  `!u ms v. region u /\ create_prefix_step sa sb explicit ctx func u ms v ==>
     region v` by
    (simp[Abbr `region`] >> rpt gen_tac >> strip_tac >>
     fs[create_prefix_step_def] >> gvs[]
     >- (drule_all create_result_tail_fail_step >> simp[]) >>
     `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst'` by simp[] >>
     drule_all create_result_tail_branch >> strip_tac >> simp[]) >>
  `region t` by
    (`region mid0` by simp[Abbr `region`] >>
     drule_all create_result_marked_invariant >> simp[]) >>
  gvs[Abbr `region`]
QED
