(* Unrestricted projections of the selected slot-copy execution. *)
Theory bodyFullUnwrapSlotOrigin
Ancestors
  bodyFullUnwrapSlotCursor

Theorem unwrap_ensure_slot_origin_loop:
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u cv ds.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
    (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `ensure_slot_copy_walk_ok (\_ _ _. T) nb n sa sb` by
    simp[ensure_slot_copy_walk_ok_def] >>
  drule_all unwrap_ensure_slot_origin_loop_walk >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`, `cv`, `ds`] >>
  asm_rewrite_tac[]
QED

Theorem unwrap_single_slot_origin_execution =
  bodyFullUnwrapSlotCursorTheory.unwrap_single_slot_origin_execution

Theorem unwrap_ensure_slot_origin_single:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32 <= nb /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
      (update_var (STRING #"%" (toString sm.cs_next_var))
        (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
          with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
      {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `ensure_slot_copy_walk_ok (\_ _ _. T) nb 1 sa sb` by
    simp[ensure_slot_copy_walk_ok_def] >>
  drule_all unwrap_ensure_slot_origin_single_walk >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  asm_rewrite_tac[]
QED

Theorem unwrap_ensure_slot_origin_execution:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (n <> 1 ==> ?cv ds.
      toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
      (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted) /\
    (n = 1 ==>
      t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
        (update_var (STRING #"%" (toString sm.cs_next_var))
          (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
            with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
        {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
      tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
      (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `ensure_slot_copy_walk_ok (\_ _ _. T) nb n sa sb` by
    simp[ensure_slot_copy_walk_ok_def] >>
  drule_all unwrap_ensure_slot_origin_execution_walk >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  asm_rewrite_tac[]
QED
