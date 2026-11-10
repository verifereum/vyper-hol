(* Rebase the data tail at capture exit, across start and length only. *)
Theory exprSimSliceOrdinaryContinue
Ancestors
  exprSimSliceOrdinaryFrame exprSimCalldataSlice exprSimWordArgs
  exprSimSliceTerminal exprSimSliceCompose exprSimSource exprSimHyps
  exprSimSliceOrdinaryContext

Theorem slice_two_operand_post_rebase:
  stmt_state_rel ctx func cenv cx ec u /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
  MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  expr_post ctx func cenv cx start ec sc sd u e1 v1 op1 t /\
  expr_post ctx func cenv cx len e1 sd se t e2 v2 op2 r /\
  vv_post ctx func cenv cx result e2 se sf r ef tv vv z ==>
  vv_post ctx func cenv cx result ec sc sf u ef tv vv z
Proof
  strip_tac >>
  `wb_frame cenv ec e1 sc u t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `wb_frame cenv e1 e2 sd t r` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `wb_frame cenv ec e2 sc u r` by
    (drule_all wb_frame_trans >> simp[]) >>
  irule vv_post_prefix_frame >>
  simp[] >> qexistsl_tac [`e2`, `se`, `r`] >> simp[]
QED

(* A forced operand read, with the marked source prefix retained for its tail. *)
Theorem slice_read_outcome_bind:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!marks v mid t.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s) marks (INL v) mid (OK t) /\
    expr_post ctx func cenv cx e es sa sb s (mid with gas_obs := []) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (tail v : evaluation_state -> eval_result evaluation_result)
      (mid with gas_obs := [],t) Q (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) tail) (es,s)
    Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[exprSimDefsTheory.expr_sim_def] >> disch_then drule_all >> strip_tac >>
  irule slice_gas_outcome_bind_value >>
  qexists_tac `\v ee t. expr_post ctx func cenv cx e es sa sb s ee v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  reverse conj_tac
  >- (irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[] >>
      rename1 `expr_exit (INR ex) r` >>
      qspec_then `Value` (qspec_then `INR ex` mp_tac)
        exprSimDefsTheory.expr_exit_success_map >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> fs[] >> metis_tac[]
QED

Theorem slice_uint_read_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx e es sa sb s ee v op t ==>
  expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ?i. v = IntV (&i) /\ i < dimword (:256) /\ eval_operand op t = SOME (n2w i)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `value_runtime_typed env (BaseT (UintT 256)) v` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def,
       vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperValueTheory.evaluate_type_def] >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `0 <= j` >>
  `?i:num. j = &i` by metis_tac[integerTheory.INT_OF_NUM] >> gvs[] >>
  `word_value (IntV (&i))` by simp[loweringSliceTheory.word_value_def] >>
  `eval_operand op t = SOME (val_to_w256 (IntV (&i)))` by
    (drule expr_post_word_operand >>
     simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  gvs[valueEncodingTheory.val_to_w256_def, wordsTheory.dimword_def,
      integer_wordTheory.i2w_def]
QED

Theorem slice_gas_path_ok_not_halted[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==> !t. r = OK t ==> ~t.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[fragExecTheory.exit_result_def]
QED

Theorem slice_marked_read_ok_not_halted:
  gas_marked_exec F (ctx,func) a (es,s) marks (INL v) mid (OK t) ==>
  ~t.vs_halted
Proof
  simp[gasSummaryTheory.gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def] >>
  metis_tac[slice_gas_path_ok_not_halted]
QED

Theorem slice_two_read_outcome:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  expr_sim_case nocalls ctx func cenv cx len /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!e1 e2 t r i k gs1 gs2.
    bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs1) =
      (INL (IntV (&i)),e1) /\
    bind (eval_expr cx len) (read_result cx) (e1 with gas_obs := gs2) =
      (INL (IntV (&k)),e2) /\
    expr_post ctx func cenv cx start ec sc sd u e1 (IntV (&i)) sop t /\
    expr_post ctx func cenv cx len e1 sd se t e2 (IntV (&k)) lop r /\
    MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
    MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
    i < dimword (:256) /\ k < dimword (:256) /\
    eval_operand sop t = SOME (n2w i) /\ eval_operand lop r = SOME (n2w k) /\
    r.vs_current_bb = se.cs_current_bb /\ r.vs_inst_idx = LENGTH se.cs_current_insts /\
    ~r.vs_halted ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (finish_slice (IntV (&i):value) (IntV (&k):value) : evaluation_state -> eval_result evaluation_result)
      (e2,r) Q (\res ee rr. expr_exit res rr)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        finish_slice sv lv od) (ec,u) Q (\res ee rr. expr_exit res rr)
Proof
  strip_tac >>
  `expr_sim ctx func cenv cx ty start ec` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ec` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `sop`, `sc`, `sd`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?gs. bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs) =
    (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env len (mid with gas_obs := [])` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_sim ctx func cenv cx ty len (mid with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `lop`, `sd`, `se`, `ty`] >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  `?gs2. bind (eval_expr cx len) (read_result cx)
     ((mid with gas_obs := []) with gas_obs := gs2) =
     (INL v,mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := []) /\
   MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM (mid' with gas_obs := []).scopes /\
   ?k. v = IntV (&k) /\ k < dimword (:256) /\ eval_operand lop t' = SOME (n2w k)` by
    (irule slice_uint_read_post >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `~t'.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`mid with gas_obs := []`, `gs`, `gs2`, `t`] >> simp[]
QED

Theorem slice_bytes_continue:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  expr_sim_case nocalls ctx func cenv cx len /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH bs)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH bs) u.vs_memory = bs /\
  src_base + LENGTH bs < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH bs) r2.vs_memory = bs) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (BytesT (Dynamic n)) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (expr_type src) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [BytesV bs;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ start` kall_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ len` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ len _` kall_tac >>
  qpat_x_assum `nocalls ==> _` kall_tac >>
  `stmt_state_rel ctx func cenv cx e2 r` by metis_tac[expr_post_state] >>
  `eval_operand sl r = SOME (n2w (LENGTH bs)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH bs) r.vs_memory = bs` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  `?bb. lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts se sf) (DROP r.vs_inst_idx bb.bb_instructions)` by
    suspend "embedding" >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rebase" >>
  suspend "terminal"
QED

Resume slice_bytes_continue[embedding]:
  drule_all exprSimSliceDataTheory.slice_data_embedding >> simp[]
QED

Resume slice_bytes_continue[terminal]:
  drule_all slice_data_bytes_outcome >> simp[]
QED

Resume slice_bytes_continue[rebase]:
  BETA_TAC >> rpt strip_tac >>
  drule_all slice_two_operand_post_rebase >> simp[]
QED

Finalise slice_bytes_continue

Theorem slice_string_continue:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  expr_sim_case nocalls ctx func cenv cx len /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH text)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH text) u.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH text) r2.vs_memory = MAP (n2w o ORD) text) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (StringT n) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (expr_type src) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [StringV text;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ start` kall_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ len` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ len _` kall_tac >>
  qpat_x_assum `nocalls ==> _` kall_tac >>
  `stmt_state_rel ctx func cenv cx e2 r` by metis_tac[expr_post_state] >>
  `eval_operand sl r = SOME (n2w (LENGTH text)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH text) r.vs_memory = MAP (n2w o ORD) text` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  `?bb. lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts se sf) (DROP r.vs_inst_idx bb.bb_instructions)` by
    (drule_all exprSimSliceDataTheory.slice_data_embedding >> simp[]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rebase" >>
  drule_all slice_data_string_outcome >> simp[]
QED

Resume slice_string_continue[rebase]:
  BETA_TAC >> rpt strip_tac >>
  drule_all slice_two_operand_post_rebase >> simp[]
QED

Finalise slice_string_continue

(* Sequential length judgment: needed only after the successful start read. *)
Theorem slice_two_read_outcome_seq:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
    expr_sim_case nocalls ctx func cenv cx len) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!e1 e2 t r i k gs1 gs2.
    bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs1) =
      (INL (IntV (&i)),e1) /\
    bind (eval_expr cx len) (read_result cx) (e1 with gas_obs := gs2) =
      (INL (IntV (&k)),e2) /\
    expr_post ctx func cenv cx start ec sc sd u e1 (IntV (&i)) sop t /\
    expr_post ctx func cenv cx len e1 sd se t e2 (IntV (&k)) lop r /\
    expr_sim_inv cenv cx env e1 /\
    MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
    MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
    i < dimword (:256) /\ k < dimword (:256) /\
    eval_operand sop t = SOME (n2w i) /\ eval_operand lop r = SOME (n2w k) /\
    r.vs_current_bb = se.cs_current_bb /\ r.vs_inst_idx = LENGTH se.cs_current_insts /\
    ~r.vs_halted ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (finish_slice (IntV (&i):value) (IntV (&k):value) : evaluation_state -> eval_result evaluation_result)
      (e2,r) Q (\res ee rr. expr_exit res rr)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        finish_slice sv lv od) (ec,u) Q (\res ee rr. expr_exit res rr)
Proof
  strip_tac >>
  `expr_sim ctx func cenv cx ty start ec` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ec` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `sop`, `sc`, `sd`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?gs. bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs) =
    (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_case nocalls ctx func cenv cx len` by
    (first_x_assum irule >>
     qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env len (mid with gas_obs := [])` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_sim ctx func cenv cx ty len (mid with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `lop`, `sd`, `se`, `ty`] >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  `?gs2. bind (eval_expr cx len) (read_result cx)
     ((mid with gas_obs := []) with gas_obs := gs2) =
     (INL v,mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := []) /\
   MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM (mid' with gas_obs := []).scopes /\
   ?k. v = IntV (&k) /\ k < dimword (:256) /\ eval_operand lop t' = SOME (n2w k)` by
    (irule slice_uint_read_post >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `~t'.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`mid with gas_obs := []`, `gs`, `gs2`, `t`] >> simp[]
QED

Theorem slice_bytes_continue_seq:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
    expr_sim_case nocalls ctx func cenv cx len) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH bs)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH bs) u.vs_memory = bs /\
  src_base + LENGTH bs < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH bs) r2.vs_memory = bs) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (BytesT (Dynamic n)) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (expr_type src) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [BytesV bs;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome_seq >>
  simp[] >> conj_tac >- (first_x_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ start` kall_tac >>
  qpat_x_assum `(?s tv t s1 v t1. _) ==> expr_sim_case _ _ _ _ _ len` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ len _` kall_tac >>
  qpat_x_assum `nocalls ==> _` kall_tac >>
  `stmt_state_rel ctx func cenv cx e2 r` by metis_tac[expr_post_state] >>
  `eval_operand sl r = SOME (n2w (LENGTH bs)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH bs) r.vs_memory = bs` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  `?bb. lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts se sf) (DROP r.vs_inst_idx bb.bb_instructions)` by
    (drule_all exprSimSliceDataTheory.slice_data_embedding >> simp[]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- (BETA_TAC >> rpt strip_tac >>
    drule_all slice_two_operand_post_rebase >> simp[]) >>
  drule_all slice_data_bytes_outcome >> simp[]
QED

Theorem slice_string_continue_seq:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
    expr_sim_case nocalls ctx func cenv cx len) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH text)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH text) u.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH text) r2.vs_memory = MAP (n2w o ORD) text) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (StringT n) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (expr_type src) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [StringV text;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome_seq >>
  simp[] >> conj_tac >- (first_x_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ start` kall_tac >>
  qpat_x_assum `(?s tv t s1 v t1. _) ==> expr_sim_case _ _ _ _ _ len` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ len _` kall_tac >>
  qpat_x_assum `nocalls ==> _` kall_tac >>
  `stmt_state_rel ctx func cenv cx e2 r` by metis_tac[expr_post_state] >>
  `eval_operand sl r = SOME (n2w (LENGTH text)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH text) r.vs_memory = MAP (n2w o ORD) text` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  `?bb. lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts se sf) (DROP r.vs_inst_idx bb.bb_instructions)` by
    (drule_all exprSimSliceDataTheory.slice_data_embedding >> simp[]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- (BETA_TAC >> rpt strip_tac >>
    drule_all slice_two_operand_post_rebase >> simp[]) >>
  drule_all slice_data_string_outcome >> simp[]
QED
