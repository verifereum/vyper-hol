(* Shared upstream interfaces for immediate bytestring hashing. *)
Theory exprSimHashBoundary
Ancestors
  exprBopSimProps exprSimLiteralBuffer exprSimVVFrame
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasSeq fragExec
  exprSimDefs loweringPosts allocLimits
  valueEncoding valueEncodingDefs valueEncodingProofs venomMemDefs
  exprLoweringProps compileEnv loweringStateRelDefs vyperState vyperValue
  words list rich_list

Theorem expr_val_rel_memory:
  expr_val_rel cx t v op s /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >> gvs[expr_val_rel_def] >>
  first_x_assum drule >> simp[]
QED

Theorem expr_val_at_footprint:
  expr_val_at cenv cx t sa sb es v op s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      b <= w2n w /\ w2n w + val_footprint tv v <= b + sz) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\
      b <= w2n w /\ w2n w + val_footprint tv v <= b + sz) \/
   val_footprint tv v = 0)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >>
  rw[] >> metis_tac[]
QED

Theorem expr_sim_suffix:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gs v ee t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     expr_post ctx func cenv cx e es sa sm s0 ee v op t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     ?marks. gas_summary_at F (ctx, func) marks (k v) (ee, t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx, func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es, s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (`bind (eval_expr cx e) (read_result cx)
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!gs v ee t. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          rename1 `gas_summary_at F _ right _ _ _ _` >>
          qexists_tac `marks ++ right` >> disj1_tac >>
          qpat_x_assum `gas_summary_at F _ right _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
          disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
            (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          drule_all gas_marked_exec_bind_normal >> strip_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`fres`, `fin`, `fr`] >> asm_rewrite_tac[]) >>
      Cases_on `res` >> gvs[] >>
      rename1 `expr_exit (INR exc) r` >>
      qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qabbrev_tac `a = bind (eval_expr cx e) (read_result cx)` >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem hash_run_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq insts s = OK t ==>
  gas_marked_path F ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) insts))
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!fuel. t.vs_current_bb = s.vs_current_bb /\
          exec_block fuel ctx bb s =
          exec_block fuel ctx bb (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)` by
    (gen_tac >>
     qspecl_then [`insts`, `s`, `fuel`, `ctx`, `bb`] mp_tac exec_block_run_inst_seq >>
     simp[]) >>
  drule gas_path_normal >> strip_tac >> gvs[gas_marked_path_def]
QED

Theorem hash_readonly_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z with vs_vars := t.vs_vars`) >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  irule literal_state_memory_frame >> qexists_tac `s` >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem hash_live_footprint_bound:
  stmt_state_rel ctx func cenv cx es s /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      b <= p /\ p + n <= b + sz) \/
   (?name b sz. local_region cenv es.scopes s name b sz /\
      b <= p /\ p + n <= b + sz)) ==>
  p + n < dimword (:256)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexistsl_tac [`ctx`, `func`] >>
     gvs[stmt_state_rel_def]) >>
  gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def]
  >- (first_x_assum drule >> decide_tac) >>
  gvs[local_region_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem hash_post_footprint_bound:
  expr_post ctx func cenv cx e es sa sm s0 es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ eval_operand op s = SOME p ==>
  w2n p + val_footprint tv v < dimword (:256)
Proof
  strip_tac >>
  Cases_on `val_footprint tv v = 0` >- simp[wordsTheory.w2n_lt] >>
  `stmt_state_rel ctx func cenv cx es' s /\
   expr_val_at cenv cx (expr_type e) sa sm es' v op s` by
    gvs[expr_post_def] >>
  drule_all expr_val_at_footprint >> strip_tac >>
  gvs[] >>
  irule hash_live_footprint_bound >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem hash_dynamic_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  `expr_val_rel cx (expr_type e) (BytesV bs) op s` by gvs[expr_post_def] >>
  `?p. eval_operand op s = SOME p` by gvs[expr_val_rel_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\ ~is_word_type (expr_type e)` by
    simp[vyperValueTheory.evaluate_type_def, is_word_type_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def] >> strip_tac >>
  qexists_tac `w2n p` >> simp[] >> decide_tac
QED

Theorem hash_string_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (StringT cap)) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH str) /\
    mem_bytes_at (b + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
    b + 32 < dimword (:256) /\ LENGTH str < dimword (:256)
Proof
  strip_tac >>
  `expr_val_rel cx (expr_type e) (StringV str) op s` by gvs[expr_post_def] >>
  `?p. eval_operand op s = SOME p` by gvs[expr_val_rel_def] >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def] >> strip_tac >>
  qexists_tac `w2n p` >> simp[] >> decide_tac
QED
