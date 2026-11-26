(* Covered, untainted memory Len load at a linked VV landing. *)
Theory bodyLenMemoryRunMods
Ancestors
  bodyFullPostsMods bodyFullGhostFrame decoderNavigationPtr wordLoadStorePtr
  decoderGhostFramePtr instMemFrontier memSafeRun allocaHistory fragExec
  representationCleanPtr exprPtrCtorImmStore bodyPtrDefs exprSimLen
  emitHelperProps emitHelper
  loweringStateRelDefs builtinSimple context compileEnv
  venomState venomInst fragGasOriginPtr ptrDiscipline
  vyperStorageFootprint valueEncodingDefs vyperTypeSystem vyperTyping
  list finite_map words arithmetic pred_set bodyLenMemoryRunCoreMods

Theorem len_memory_run_mods:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op n pvt tvt a w.
    (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory /\
    a = vv_operand vv /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\
    is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca a LocMemory sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    eval_operand a t = SOME w /\
    mload (w2n w) t = n2w n /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       mem_word_at (w2n w) m = n2w n) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?z G2 tn2.
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2)) /\
      eval_operand op z = SOME (n2w n) /\
      op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (alloca_history func t ==> alloca_history func z) /\
      z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
        FLOOKUP G2 x = FLOOKUP G x /\
        op_taint tn2 (Var x) = op_taint tn (Var x)) /\
      tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
      tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  irule len_memory_run_core_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G0`,`a`,`cenv`,`d`,`e`,`env`,`es`,`pvt`,`s0`,`sa`,
               `tn0`,`tv`,`tvt`,`vv`,`w`] >>
  asm_rewrite_tac[]
QED
