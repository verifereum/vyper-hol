(* The two full expression outcomes at one operand's compiler cursors. *)
Theory entryCreateOperandReplay
Ancestors
  bodyFullPreds bodySim bodySimFull s1PrefixDefs exprSimFullBundleProps
  gasContext gasOutcomeFull createSizeOperandCode createExprSizeExitDefs
  createSizeCutRegion createSizePrefixReplay bodyFullIfExpReach fragGasOrigin

Theorem entry_create_operand_full_judgments[local]:
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es ==>
  expr_sim_full (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx ty e es /\
  expr_vv_sim_full (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx ty e es
Proof
  simp[Once body_expr_full_ok_def] >> metis_tac[]
QED

Theorem body_operand_value_outcome:
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
    tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e
       (es,sa,sb,s0,op,G0,tn0))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `cx_tops cx = tops` by fs[body_inv_def, cx_tops_def] >>
  `expr_sim_full (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx ty e es` by
    (drule_all entry_create_operand_full_judgments >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_via_bundle, expr_sim_full_hypotheses_def,
       expr_sim_full_code_def] >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_full_pre_def]) >>
  metis_tac[]
QED

Theorem body_operand_vv_outcome:
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
    ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
    tops cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. ?tv. res = INL tv /\
       vv_post H ctx fnc ce cx e es sa sb s0 ee tv vv t /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history fnc t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee G tn t /\
       ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
       (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
            ~is_bytestring_type (post_value_type ce e) ==>
            vv_own ce cx (post_value_type ce e) sa sb ee tv vv t /\
            (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                     eval_operand (vv_operand vv) t = SOME w ==>
                     w2n w + type_memory_size rt <= lo /\
                     (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                            val_in_memory rt val (w2n w) mem)) /\
       (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==>
                ptr_buf_ok ce e op G t) /\
       (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
               ptr_buf_ok ce e p.ptr_operand G t) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `cx_tops cx = tops` by fs[body_inv_def, cx_tops_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx ty e es` by
    (drule_all entry_create_operand_full_judgments >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_eq] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem operand_value_cut_code:
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
    ce cx ty e es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  create_cut_code {} sa sb
Proof
  simp[expr_sim_full_pre_def] >> strip_tac >>
  metis_tac[create_operand_cut_code, pairTheory.SND]
QED

Theorem operand_vv_cut_code:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
    ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  create_cut_code {} sa sb
Proof
  simp[expr_vv_sim_full_pre_def] >> strip_tac >>
  metis_tac[create_operand_cut_code, pairTheory.SND]
QED

(* An executing caller edge is confined only while it is before the cut. *)
Theorem operand_cut_region_edge:
  body_inv tops ctx ce cx /\ MEM fnc ctx.ctx_functions /\
  create_cut_code {} sa sb /\ fn_has_code sa sb fnc /\
  create_cut_region sa sb s /\
  (s.vs_current_bb <> sb.cs_current_bb \/
    s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  gas_origin_edge mem explicit ctx fnc s marks (OK t) ==>
  create_prefix_step sa sb explicit ctx fnc s marks t /\
  create_cut_region sa sb t
Proof
  strip_tac >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  drule_all create_cut_region_rules >> strip_tac >>
  `gas_origin_edge F explicit ctx fnc s marks (OK t)` by
    (qpat_assum `gas_origin_edge mem _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_origin_edge_def] >> metis_tac[]) >>
  `?bb i. lookup_block s.vs_current_bb fnc.fn_blocks = SOME bb /\
          get_instruction bb s.vs_inst_idx = SOME i` by
    (qpat_assum `gas_origin_edge F _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[gas_origin_edge_def]) >> metis_tac[]) >>
  `!bb. lookup_block sb.cs_current_bb fnc.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  simp[create_prefix_step_def] >> metis_tac[arithmeticTheory.ZERO_LESS_EQ]
QED
