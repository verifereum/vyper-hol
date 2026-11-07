Theory bodyPtrStructLitRawChild
Ancestors bodyPtrStructLitAllocationBridge exprOperandVar freshWrites
  exprLoweringProps compileEnv context allocationPtr loweringHalt
  venomState venomExecSemantics venomInst finite_map
  exprSimAggregateLayout fragExec exprLowering bodyPtrPreds
  exprSimAggregateSource exprSimMemorySource exprSimSource exprSimHypsDefs bodyPtrDefs

Theorem structlit_alloc_buffer_reserved:
  compile_alloc_buffer N sa = (buf,sb) /\ local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  local_ptrs_reserved ce sb /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p)
Proof
  strip_tac >> qspecl_then [`N`, `sa`] mp_tac ci_mono_compile_alloc_buffer >>
  simp[] >> strip_tac >>
  conj_tac >- (irule compiler_ci_mono_reserved >> metis_tac[]) >>
  fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem structlit_alloc_buffer_halted:
  compile_alloc_buffer N sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\ N < dimword (:256) ==>
  (u with vs_inst_idx := k).vs_halted = s.vs_halted
Proof
  strip_tac >> drule structlit_alloc_buffer_base_step >>
  disch_then (qspec_then `s` assume_tac) >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `N` mp_tac) >>
      simp[] >> disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
      gvs[update_var_def]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  gvs[step_inst_base_def, mk_inst_def, exec_alloca_def, update_var_def]
QED

Theorem structlit_first_child_suffix:
  compile_struct_lit compile_expr ce ty ((fname,e)::rest) buf off sb = (r,sd) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) ==>
  cs_extends sc sd
Proof
  simp[Once compile_struct_lit_def, LET_THM, comp_bind_def] >>
  strip_tac >>
  `ci_mono sc (SND
    (comp_bind (emit_op ADD [buf; Lit (n2w off)])
      (\dst. comp_bind (unwrap_value ce vv)
        (\v. comp_ignore_bind
          (compile_store_memory ce v dst
            (case ALOOKUP (get_struct_fields ce.ce_struct_fields
              (case ty of StructT n => nsid_to_string n | _ => "")) fname of
               SOME (fty,sz) => fty | NONE => expr_type e)
            (lowered_value_type ce e))
          (compile_struct_lit compile_expr ce ty rest buf
            (off + (case ALOOKUP (get_struct_fields ce.ce_struct_fields
              (case ty of StructT n => nsid_to_string n | _ => "")) fname of
               SOME (fty,sz) => sz | NONE => 32))))) sc))` by
    (ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
     rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
     >- simp[ci_mono_unwrap_value] >>
     rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
     >- simp[ci_mono_compile_store_memory] >>
     gen_tac >> irule ci_mono_compile_struct_lit_cfn >>
     simp[cj 1 compile_expr_ci_mono]) >>
  gvs[comp_bind_def, ci_mono_def]
QED

Theorem structlit_first_child_code:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  fn_has_code sa sd fn ==>
  fn_has_code sa sb fn /\ fn_has_code sb sc fn
Proof
  strip_tac >> drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  `cs_extends sc sd` by (irule structlit_first_child_suffix >> metis_tac[]) >>
  `cs_extends sb sc` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sa sb` by
    (qspecl_then [`SUM (MAP (SND o SND)
        (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))`, `sa`]
       mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `cs_extends sb sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem structlit_first_child_judgment:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  body_exprs_ptr_ok cx (MAP SND ((fname,e)::rest)) ==>
  expr_vv_sim_ptr d ctx PG fn ce cx (expr_type e) e es /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre ce cx env e es` by
    (drule expr_body_pre_struct_field >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  conj_tac
  >- (fs[body_exprs_ptr_ok_def, body_expr_ptr_ok_def] >> metis_tac[]) >>
  irule forced_expr_admissible_raw >>
  irule expr_body_pre_gas_admissible >> metis_tac[]
QED

Theorem structlit_alloc_first_child_outcome:
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
      (\res ee G tn t'. ?tv. res = INL tv /\
        vv_post ctx fn ce cx e es sb sc t ee tv vv t' /\
        t'.vs_current_bb = sc.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sc.cs_current_insts /\
        ghost_inv d ce cx ee G tn t' /\
        ptr_vv_ok cx (expr_type e) tv vv ee G tn t' /\
        (!ty' op. vv = StackValue ty' op /\ ~is_word_type (expr_type e) ==>
          ptr_buf_ok ce e op G t') /\
        (!ty' q. vv = LocatedValue ty' q /\ q.ptr_location = LocMemory ==>
          ptr_buf_ok ce e q.ptr_operand G t') /\
        ghost_kept ce es sb G1 tn1 t G tn)
      (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all structlit_first_child_judgment >>
  disch_then (qspecl_then [`fn`, `d`, `PG`] strip_assume_tac) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule structlit_first_child_code >> metis_tac[]) >>
  drule_all structlit_alloc_buffer_ptr_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `~t.vs_halted` by
    (drule_all structlit_alloc_buffer_halted >> simp[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_ptr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`G1`, `tn1`, `w`] >> gvs[]
QED

(* The returned normal post retains ghost_kept at sb and the allocation
   witnesses include not_fresh_at sb p. Thus ghost_kept_provenance
   (bodyPtrStructLitResourceHandoff) and ghost_kept_operand (wordArgsPtr)
   project FLOOKUP G p = FLOOKUP G1 p and
   op_taint tn (Var p) = op_taint tn1 (Var p) at this very endpoint.
   No memory framing or declared-field-capacity conversion is asserted. *)
