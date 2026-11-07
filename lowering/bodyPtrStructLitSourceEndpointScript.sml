(* Source runtime typing belongs to the normalized counted endpoint. *)
Theory bodyPtrStructLitSourceEndpoint
Ancestors fragGasPathPtr exprSimSource bodyPtrDefs vyperState
  bodyPtrStructLitRawChild exprSimHyps exprSimHypsDefs exprSimAggregateSource

Theorem gas_outcome_ptr_expr_runtime_typed:
  expr_body_pre ce cx env e es /\
  gas_outcome_ptr D tops (ctx,fn) PG (eval_expr cx e) (es,s,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG (eval_expr cx e) (es,s,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\
      (!tv. res = INL tv ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
          (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v))) R
Proof
  rw[gas_outcome_ptr_def] >> qexists `marks`
  >- (disj1_tac >> gvs[gas_summary_ptr_at_def]
      >- (qexistsl [`res`, `es_end`, `G`, `tn`, `OK t`] >> simp[] >> disj1_tac >>
          rpt strip_tac >> gvs[] >>
          qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
          `expr_body_pre ce cx env e
             (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
          drule_all expr_body_pre_runtime_typed >> simp[]) >>
      qexistsl [`res`, `es_end`, `G`, `tn`, `r`] >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem structlit_alloc_first_child_typed_outcome:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  body_exprs_ptr_ok cx (MAP SND ((fname,e)::rest)) /\
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G0 tn0 s /\
  local_ptrs_reserved ce sa /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?u t G1 tn1 p w.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    t = u with vs_inst_idx := SUC s.vs_inst_idx /\
    buf.buf_operand = Var p /\ not_fresh_at sb p /\
    gas_path_ptr_edge D 0 ctx fn PG G0 tn0 s 0 G1 tn1 (OK t) /\
    ptr_covers G1 tn1 p t N /\ eval_operand buf.buf_operand t = SOME w /\
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (eval_expr cx e) (es,t,G1,tn1)
      (\res ee G tn t'.
        (?tv. res = INL tv /\
          vv_post ctx fn ce cx e es sb sc t ee tv vv t' /\
          t'.vs_current_bb = sc.cs_current_bb /\
          t'.vs_inst_idx = LENGTH sc.cs_current_insts /\
          ghost_inv d ce cx ee G tn t' /\
          ptr_vv_ok cx (expr_type e) tv vv ee G tn t' /\
          (!ty' op. vv = StackValue ty' op /\ ~is_word_type (expr_type e) ==>
            ptr_buf_ok ce e op G t') /\
          (!ty' q. vv = LocatedValue ty' q /\ q.ptr_location = LocMemory ==>
            ptr_buf_ok ce e q.ptr_operand G t') /\
          ghost_kept ce es sb G1 tn1 t G tn) /\
        (!tv. res = INL tv ==>
          ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
            eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
            (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)))
      (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all structlit_alloc_first_child_outcome >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre ce cx env e es` by
    (drule expr_body_pre_struct_field >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  drule_all gas_outcome_ptr_expr_runtime_typed >> strip_tac >>
  qexistsl [`u`, `t`, `G1`, `tn1`, `p`, `w`] >> gvs[]
QED
