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
  cheat
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
  cheat
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
  cheat
QED
