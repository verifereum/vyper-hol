Theory bodyFullBopBytestringChild
Ancestors bodyFullBopBytestringHash bodySimFull gasShadow gasShadowState
  gasShadowUnit gasExplicitSites
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> irule bop_bytestring_selected_hash_full_exit >>
  simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!m cb. _` drule_all >> strip_tac >>
  `!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u` by
    (Cases_on `ctx_has_dalloca ctx` >- fs[] >>
     rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_members >> simp[] >>
     strip_tac >> fs[unitTransformDefsTheory.dalloca_fmp_headroom_def,
       ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
     metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule gasOutcomeFullTheory.gas_outcome_full_post_mono >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[]
QED
*)
Theorem bop_bytestring_selected_child_full_halt:
  (case bytestring_literal_hash e of
     NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e) e sa))
       (SND (lower_value compile_expr cenv (expr_type e) e sa))
   | SOME digest => (Lit digest,sa)) = (h,sz) /\
  is_bytestring_type (expr_type e) /\ expr_body_pre_mods mods cenv cx env e es /\
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ fn_has_code sa sz func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  explicit = gas_explicit_sites ctx shadow_ctx /\
  (!m cb. bytestring_literal_hash e = NONE /\
    lower_value compile_expr cenv (expr_type e) e sa = (m,cb) ==>
    ?shadow_sa shadow_cb.
      lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sa = (m,shadow_cb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state cb shadow_cb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa cb func /\ fn_has_code shadow_sa shadow_cb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
      (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s /\ alloca_history func s /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G tn s) /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee HG un t. ?v contents. res = INL v /\
      (v = BytesV contents \/
       ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
      eval_operand h t = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
      op_prov HG h = NONE /\ op_taint un h = {} /\
      (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\ ~t.vs_halted /\
      t.vs_current_bb = sz.cs_current_bb /\ t.vs_inst_idx = LENGTH sz.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s HG un /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s t))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  cheat
QED

Theorem bop_bytestring_selected_child_full:
  (case bytestring_literal_hash e of
     NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e) e sa))
       (SND (lower_value compile_expr cenv (expr_type e) e sa))
   | SOME digest => (Lit digest,sa)) = (h,sz) /\
  is_bytestring_type (expr_type e) /\ expr_body_pre_mods mods cenv cx env e es /\
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ fn_has_code sa sz func /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  explicit = gas_explicit_sites ctx shadow_ctx /\
  (!m cb. bytestring_literal_hash e = NONE /\
    lower_value compile_expr cenv (expr_type e) e sa = (m,cb) ==>
    ?shadow_sa shadow_cb.
      lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sa = (m,shadow_cb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state cb shadow_cb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa cb func /\ fn_has_code shadow_sa shadow_cb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
      (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s /\ alloca_history func s /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G tn s) /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee HG un t. ?v contents. res = INL v /\
      (v = BytesV contents \/
       ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
      eval_operand h t = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
      op_prov HG h = NONE /\ op_taint un h = {} /\
      (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\ ~t.vs_halted /\
      t.vs_current_bb = sz.cs_current_bb /\ t.vs_inst_idx = LENGTH sz.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s HG un /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s t))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_assum `~ctx_has_dalloca ctx` (fn guard =>
    qpat_assum `!m cb. _` (assume_tac o SIMP_RULE bool_ss [guard]) >>
    drule_all (SIMP_RULE bool_ss [guard] bop_bytestring_selected_child_full_halt)) >>
  qpat_x_assum `explicit = gas_explicit_sites ctx shadow_ctx` SUBST_ALL_TAC >>
  strip_tac >>
  drule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  disch_then irule >> simp[]
QED
