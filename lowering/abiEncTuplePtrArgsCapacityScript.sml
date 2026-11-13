(* Conditional capacity-retaining argument execution. *)
Theory abiEncTuplePtrArgsCapacity
Ancestors
  abiEncTuplePtrCapturedCapacity abiEncTuplePtrUncapturedCapacity
  abiEncTuplePtrArgsCompose abiEncodeArgsSim list

Theorem compile_abi_encode_args_capacity_ptr_from_steps:
  !args ctx func ce cx Inv env es sa ops sb s0 d PG G0 tn0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY (\e. !s. Inv s ==> expr_body_pre ce cx env e s) args /\
    EVERY (\e. !s. Inv s ==>
      expr_sim_ptr d ctx PG func ce cx (expr_type e) e s /\
      expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e s) args /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!e es sa mid sm s0 vv op G0 tn0 es_pre tvv v ee tv G tn r.
      compile_expr ce (expr_type e) e sa = (vv,mid) /\
      compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
      ~is_word_type (expr_type e) /\
      expr_body_pre ce cx env e es_pre /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
        ~is_word_type (post_value_type ce e) ==>
        type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
        type_memory_size tvt < 2 ** 64) /\
      fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
      stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
      ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      vv_post ctx func ce cx e es sa mid s0 ee tvv vv r /\
      read_result cx tvv ee = (INL v,ee) /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64 /\
      type_memory_size tv + 64 < dimword (:256) /\
      ghost_inv d ce cx ee G tn r /\
      ptr_vv_ok cx (post_value_type ce e) tvv vv ee G tn r /\
      (!t' a. vv = StackValue t' a /\ ~is_word_type (post_value_type ce e) ==>
        ptr_buf_ok ce e a G r) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G r) /\
      ghost_kept ce es sa G0 tn0 s0 G tn /\
      ~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
      r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
      ?H tm t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn r 0 H tm (OK t) /\
        materialize_owned_post ctx func ce cx e es sa mid sm s0 ee v op tv t /\
        ptr_val_ok cx (lowered_value_type ce e) v op H tm t /\
        ptr_buf_ok ce e op H t /\
        ghost_inv d ce cx ee H tm t /\ ghost_kept ce es sa G0 tn0 s0 H tm /\
        ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
        t.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\rr ee G tn t. ?vs. rr = INL vs /\
        abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
        LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
          (SND ev) op G tn t) ops (ZIP (args,vs)) /\
        LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
          ptr_buf_ok ce e op G t) ops args /\
        EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d ce cx ee G tn t /\ ghost_kept ce es sa G0 tn0 s0 G tn)
      (\rr ee ghosts r. wb_args_exit rr r)
Proof
  Induct_on `args`
  >- (rpt strip_tac >>
      gvs[exprLoweringTheory.compile_abi_encode_args_def, compileEnvTheory.comp_return_def] >>
      irule (SRULE [] abi_args_nil_ptr) >> simp[]) >>
  pop_assum (mk_asm "ih") >> rpt gen_tac >> strip_tac >>
  rename1 `abi_args_ready ctx func ce cx Inv (e::args)` >>
  gvs[abi_args_compile_cons, EVERY_DEF] >>
  Cases_on `~is_word_type (expr_type e) /\ exprs_can_mutate ce args`
  >- (gnvs[] >> irule (SRULE [] abi_args_captured_rec_capacity_ptr) >> simp[] >>
      conj_tac
      >- (qexists `env` >> simp[] >> rpt gen_tac >> strip_tac >>
          first_assum irule >> simp[] >> conj_tac
          >- (qexists `es_pre` >> simp[]) >> qexists `tvv` >> simp[]) >>
      qexists `Inv` >> simp[] >> rpt gen_tac >> strip_tac >>
      asm "ih" irule >> simp[] >>
      qexistsl [`Inv`, `env`] >> simp[] >>
      rpt gen_tac >> strip_tac >> first_assum irule >> simp[] >>
      conj_tac >- (qexists `es_pre` >> simp[]) >> qexists `tvv` >> simp[]) >>
  gnvs[] >> irule (SRULE [] abi_args_uncaptured_rec_capacity_ptr) >> simp[] >>
  qexistsl [`Inv`, `env`] >> simp[] >> rpt gen_tac >> strip_tac >>
  asm "ih" irule >> simp[] >>
  qexistsl [`Inv`, `env`] >> simp[] >>
      rpt gen_tac >> strip_tac >> first_assum irule >> simp[] >>
      conj_tac >- (qexists `es_pre` >> simp[]) >> qexists `tvv` >> simp[]
QED
