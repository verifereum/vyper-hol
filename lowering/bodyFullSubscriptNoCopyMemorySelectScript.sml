(* Selection from the represented memory place after the no-copy index cut. *)
Theory bodyFullSubscriptNoCopyMemorySelect
Ancestors bodyFullSubscriptLocalCutOrigin[qualified,ignore_grammar] abiEncodeArgsSim[qualified,ignore_grammar] vyperPlaceResultTyping[qualified,ignore_grammar]
  option[qualified,ignore_grammar] vyperTypeValues[qualified,ignore_grammar]
  vyperTyping[qualified,ignore_grammar] vyperValueOperation[qualified,ignore_grammar]
  bodyFullSubscriptLiveLocalView bodyFullSubscriptCapturedEndpoint
  bodyFullSubscriptNoCopyMemoryInput
  bodyFullSubscriptDynamicChildRow bodyFullSubscriptFixedSelect bodyFullSubscriptDynamicSelect
  bodyFullPreds bodySimFull exprSimSubscriptArraySuffix exprSimExtract32Post
  exprSimSubscriptArraySource exprSimProps exprSimSource exprSimHypsDefs
  exprOperandVar exprLoweringProps exprSimUnwrap exprSimVVFrame
  gasShadowCompile gasShadowState gasShadow gasExemptCert stateRelProj
  vyperStorageTrace vyperStorageFootprint bodyPtrDefs loweringPosts compileEnv
  vyperInterpreter vyperState vyperAST context exprSimWordArgs wordArgsPtr
  exprReasonOperand exprSimHyps bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem subscript_nocopy_memory_place_select_full:
  body_inv tops ctx cenv cx /\
  ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et bd /\ place_type cenv e1 = ValPT (ArrayT et bd) /\
  post_value_type cenv e1 = expr_type e1 /\
  ~(?n i p. bd = Fixed n /\ PlaceR (MemoryPlace id path) = PlaceR (MemoryPlace i p) /\ base_from_pop e1) /\
  compile_expr cenv ty e1 sa = (bvv,sm) /\
  lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
  loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type e2))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
  fn_has_code sa sb func /\ fn_has_code st2 sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_expr cx e1 (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ mid.gas_obs = [] /\ fin.gas_obs = [] /\
  ~s.vs_halted /\ ~it.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
  alloca_history func s /\ alloca_history func it /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
  vv_store_bound cx (post_value_type cenv e1) (lowered_value_type cenv e1)
    mid (PlaceR (MemoryPlace id path)) bvv s /\
  ptr_vv_ok cx (post_value_type cenv e1) (PlaceR (MemoryPlace id path)) bvv mid G1 tn1 s /\
  (!v. PlaceR (MemoryPlace id path) = Value v /\ ~is_word_type (post_value_type cenv e1) /\
       ~is_bytestring_type (post_value_type cenv e1) ==>
       vv_own cenv cx (post_value_type cenv e1) sa sm mid (PlaceR (MemoryPlace id path)) bvv s /\
       (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
   ?v. read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e1) = SOME rt /\
              eval_operand (vv_operand bvv) s = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)) /\
  (!t op. bvv = StackValue t op /\ ~is_word_type (post_value_type cenv e1) ==>
          ptr_buf_ok cenv e1 op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e1 p.ptr_operand G1 s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  expr_store_bound cx (post_value_type cenv e2) key iop it /\
  ptr_val_ok cx (post_value_type cenv e2) key iop Gi tni it /\
  (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 iop Gi it) /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
    vv_post H ctx func cenv cx e1 es sa sm s0 mid (PlaceR (MemoryPlace id path)) bvv s /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
    expr_post H ctx func cenv cx e2 mid sm st2 s fin key iop it /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni it) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et bd) (PlaceR (MemoryPlace id path)) (ValueSubscript key)) (fin,it,Gi,tni)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      vv_store_bound cx (post_value_type cenv (Subscript ann e1 e2))
        (lowered_value_type cenv (Subscript ann e1 e2)) ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann e1 e2)) tv (LocatedValue ann (mk_ptr dst loc)) ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) /\
           ~is_bytestring_type (post_value_type cenv (Subscript ann e1 e2)) ==>
           vv_own cenv cx (post_value_type cenv (Subscript ann e1 e2)) sa sb ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
           (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr dst loc)) = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann e1 e2)) =
                    SOME rt /\ eval_operand (vv_operand (LocatedValue ann (mk_ptr dst loc))) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. (LocatedValue ann (mk_ptr dst loc)) = StackValue t' op /\
               ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) ==>
               ptr_buf_ok cenv (Subscript ann e1 e2) op G t) /\
      (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv (Subscript ann e1 e2) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fixed_select_scalar_intro lo (gas_explicit_sites ctx shadow_ctx) ctx func PG
      (\sa sc sb s r. T)` by
    (simp[fixed_select_scalar_intro_def, fixed_select_cuts_def] >>
     rpt gen_tac >> strip_tac >>
     drule_all bodyFullTargetArraySuffixTheory.array_tail_scalar_uniform >>
     disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >> simp[]) >>
  assume_tac bodyFullSubscriptCapturedDynamicRunTheory.captured_dynamic_scalar_rule_trivial >>
  drule_all_then strip_assume_tac nocopy_memory_select_observed >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
  qexistsl [`Gz`,`fin`,`[]`,`r`,`res`,`tnz`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[bodyFullSubscriptDynamicSelectTheory.subscript_dynamic_select_post_def]
QED
