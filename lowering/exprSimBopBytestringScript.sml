(* Counted simulation of dynamic bytestring equality and inequality. *)

Theory exprSimBopBytestring
Ancestors
  exprSimHashBoundary bytestringHashProps gasSummary fragGasMode fragGasPath
  gasOutcome gasSummaryCompose gasExemptCert
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomInst venomState
  valueEncoding ASCIInumbers words vyperTypeBytesCrypto venomMemProps
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

Theorem comparison_hash_run[local]:
  compile_bytestring_hash ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def,
       bind_outputs_def] >>
  `eval_operand ptr_op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w b + 32w) s) =
     SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, exec_read1_def] >>
  `mload b s = n2w (LENGTH bs)` by
    gvs[mload_def, mem_word_at_def] >>
  simp[mload_def, update_var_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, toString_inj] >>
  gvs[mload_def, word_add_n2w, GSYM mem_bytes_at_def,
      run_inst_seq_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_assum (qspec_then `sa.cs_next_var + 2` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >> gvs[]
QED

Theorem comparison_hash_shape[local]:
  compile_bytestring_hash p sa = (op, sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ cs_extends sa sb /\
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       cs_extends_def, rich_listTheory.IS_PREFIX_APPEND, not_fresh_at_def,
       toString_inj] >> rpt strip_tac >> gvs[toString_inj]
QED

Theorem comparison_hash_counted[local]:
  compile_bytestring_hash ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all comparison_hash_run >> strip_tac >>
  drule comparison_hash_shape >> strip_tac >>
  drule_all hash_run_path >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, stmt_state_rel_inst_idx] >>
  qpat_x_assum `_ with vs_vars := _ = _`
    (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]
QED

Theorem comparison_hash_dynamic[local]:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) ptr_op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  compile_bytestring_hash ptr_op sm = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  irule comparison_hash_counted >> goal_assum drule >>
  gvs[loweringPostsTheory.expr_post_def] >> metis_tac[]
QED

Theorem comparison_hash_string[local]:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) ptr_op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  compile_bytestring_hash ptr_op sm = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (MAP (n2w o ORD) str))) /\
    stmt_state_rel ctx func cenv cx es' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all hash_string_post_view >> strip_tac >>
  irule comparison_hash_counted >> goal_assum drule >>
  gvs[loweringPostsTheory.expr_post_def] >> metis_tac[]
QED

Theorem comparison_hash_literal[local]:
  bytestring_literal_hash e = SOME h ==>
  ?v. (!es. bind (eval_expr cx e) (read_result cx) es = (INL v, es)) /\
    ((?bs. v = BytesV bs /\
       h = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
     (?str. v = StringV str /\
       h = word_of_bytes T (0w:bytes32)
         (Keccak_256_w64 (MAP (n2w o ORD) str))))
Proof
  Cases_on `e` >> simp[bytestring_literal_hash_def] >>
  rename1 `Literal ann lit` >> Cases_on `lit` >>
  simp[bytestring_literal_hash_bytes, bytestring_literal_hash_string,
       bytestring_literal_hash_def] >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem comparison_digest_eq[local]:
  (word_of_bytes T (0w:bytes32) (Keccak_256_w64 xs) =
   word_of_bytes T (0w:bytes32) (Keccak_256_w64 ys)) <=>
  Keccak_256_w64 xs = Keccak_256_w64 ys
Proof
  eq_tac >- (strip_tac >>
    irule (word_of_bytes_be_inj |> INST_TYPE [alpha |-> ``:256``]) >>
    simp[LENGTH_Keccak_256_w64, dividesTheory.compute_divides]) >>
  simp[]
QED

Theorem comparison_source_result[local]:
  (bop = Eq \/ bop = NotEq) /\
  ((?xs ys cap. v1 = BytesV xs /\ v2 = BytesV ys /\
      evaluate_type (get_tenv cx) ty2 = SOME (BaseTV (BytesT (Dynamic cap))) /\
      d1 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 xs) /\
      d2 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 ys)) \/
   (?xs ys. v1 = StringV xs /\ v2 = StringV ys /\
      d1 = word_of_bytes T (0w:bytes32)
        (Keccak_256_w64 (MAP (n2w o ORD) xs)) /\
      d2 = word_of_bytes T (0w:bytes32)
        (Keccak_256_w64 (MAP (n2w o ORD) ys)))) ==>
  bop_result cx ann bop [ty1; ty2] v1 v2 es =
    INL (BoolV (if bop = Eq then d1 = d2 else d1 <> d2))
Proof
  strip_tac >> gvs[exprBopSimDefsTheory.bop_result_def, evaluate_builtin_def,
    vyperValueOperationTheory.evaluate_binop_def,
    vyperValueOperationTheory.binop_negate_def, comparison_digest_eq] >>
  simp[vyperMiscTheory.n2w_o_ORD_eq]
QED

Theorem comparison_digest_run[local]:
  (bop = Eq \/ bop = NotEq) /\
  (if bop = Eq then emit_op EQ [h1; h2] sa = (op, sb)
   else ?q sq. emit_op EQ [h1; h2] sa = (q, sq) /\
               emit_op ISZERO [q] sq = (op, sb)) /\
  eval_operand h1 s = SOME d1 /\ eval_operand h2 s = SOME d2 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (bool_to_word (if bop = Eq then d1 = d2 else d1 <> d2)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> gvs[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[mk_inst_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp_tac (srw_ss()) [instruction_accfupds, instruction_accessors] >>
  ASM_SIMP_TAC std_ss [exec_pure2_def] >>
  simp[Once run_inst_seq_def] >>
  ASM_SIMP_TAC std_ss [Once step_inst_base_def, instruction_accfupds,
       instruction_accessors, exec_pure1_def,
       eval_operand_def, lookup_var_update_var, toString_inj] >>
  simp[run_inst_seq_def, bool_to_word_def, update_var_def, lookup_var_def,
       eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >> gvs[]
QED

Theorem comparison_digest_shape[local]:
  (bop = Eq \/ bop = NotEq) /\
  (if bop = Eq then emit_op EQ [h1; h2] sa = (op, sb)
   else ?q sq. emit_op EQ [h1; h2] sa = (q, sq) /\
               emit_op ISZERO [q] sq = (op, sb)) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  cs_extends sa sb /\ (!x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> gvs[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       cs_extends_def, rich_listTheory.IS_PREFIX_APPEND, not_fresh_at_def,
       toString_inj]
QED

Theorem comparison_digest_counted[local]:
  (bop = Eq \/ bop = NotEq) /\
  (if bop = Eq then emit_op EQ [h1; h2] sa = (op, sb)
   else ?q sq. emit_op EQ [h1; h2] sa = (q, sq) /\
               emit_op ISZERO [q] sq = (op, sb)) /\
  eval_operand h1 s = SOME d1 /\ eval_operand h2 s = SOME d2 /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (val_to_w256 (BoolV (if bop = Eq then d1 = d2 else d1 <> d2))) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all comparison_digest_run >> strip_tac >>
  drule_all comparison_digest_shape >> strip_tac >>
  drule_all hash_run_path >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, stmt_state_rel_inst_idx,
      val_to_w256_def, bool_to_word_def] >>
  qpat_x_assum `_ with vs_vars := _ = _`
    (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >>
  Cases_on `d1 = d2` >> simp[bool_to_word_def]
QED

Theorem comparison_compile_cut[local]:
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) sa =
    (op, sb) ==>
  ?h1 sh1 h2 sh2.
    (case bytestring_literal_hash e1 of
       SOME h => h1 = Lit h /\ sh1 = sa
     | NONE => ?p sm. lower_value compile_expr cenv (expr_type e1) e1 sa =
                       (p, sm) /\ compile_bytestring_hash p sm = (h1, sh1)) /\
    (case bytestring_literal_hash e2 of
       SOME h => h2 = Lit h /\ sh2 = sh1
     | NONE => ?p sm. lower_value compile_expr cenv (expr_type e1) e2 sh1 =
                       (p, sm) /\ compile_bytestring_hash p sm = (h2, sh2)) /\
    (if bop = Eq then emit_op EQ [h1; h2] sh2 = (op, sb)
     else ?q sq. emit_op EQ [h1; h2] sh2 = (q, sq) /\
                 emit_op ISZERO [q] sq = (op, sb))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bop <> In /\ bop <> NotIn` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >> simp[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call,
       vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  Cases_on `bytestring_literal_hash e1` >>
  Cases_on `bytestring_literal_hash e2` >> gvs[] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> metis_tac[]
QED

Theorem gas_summary_at_zero_prefix[local]:
  gas_marked_path memory ctx func t 0 (OK t') /\
  gas_summary_at memory (ctx,func) marks source (ee,t') Q R ==>
  gas_summary_at memory (ctx,func) marks source (ee,t) Q R
Proof
  strip_tac >>
  `t'.vs_gas_readings = t.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  gvs[gas_summary_at_def, gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem comparison_operand_outcome_suffix[local]:
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
     ?u. gas_marked_path F ctx func t 0 (OK u) /\
       gas_outcome F (cx_tops cx) (ctx,func) (k v) (ee,u) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`op`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume comparison_operand_outcome_suffix[normal]:
  `bind (eval_expr cx e) (read_result cx)
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
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) es_end (OK u)` by
    (gvs[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rename1 `gas_summary_at F _ right _ _ _ _` >>
      qexists_tac `marks ++ right` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`res`,`es_end'`,`r`] >> simp[] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`,`u`,`v`] >> gvs[]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ right _ _` >>
  qexists_tac `marks ++ right` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  gvs[ignore_bind_def]
QED

Resume comparison_operand_outcome_suffix[exit]:
  Cases_on `res` >> gvs[] >>
  rename1 `expr_exit (INR exc) r` >>
  qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

Resume comparison_operand_outcome_suffix[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED
Finalise comparison_operand_outcome_suffix

Theorem compile_bop_bytestring_eqne_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) ==>
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  strip_tac >>
  pure_rewrite_tac[expr_sim_case_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    metis_tac[well_typed_binop_def] >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     (conj_tac >- gvs[expr_body_pre_def]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!es'. expr_sim_inv cenv cx env es' ==>
     expr_body_pre cenv cx env e2 es'` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     (conj_tac >- simp[]) >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ e1`
       (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
     disch_then irule >>
     (conj_tac >- gvs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  `bop <> In /\ bop <> NotIn` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >> simp[]) >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all comparison_compile_cut >> strip_tac >>
  drule_all comparison_digest_shape >> strip_tac >>
  `cs_extends sa sh1 /\ cs_extends sh1 sh2` by
    (conj_tac
     >- (qpat_x_assum `case bytestring_literal_hash e1 of NONE => ?p sm. lower_value _ _ _ e1 sa = _ /\ _ | SOME h => _` mp_tac >>
         Cases_on `bytestring_literal_hash e1` >> simp_tac (srw_ss()) [] >>
         strip_tac >> imp_res_tac (cj 2 compile_expr_grows) >>
         imp_res_tac comparison_hash_shape >>
         metis_tac[cs_extends_trans, cs_extends_refl]) >>
     qpat_x_assum `case bytestring_literal_hash e2 of NONE => ?p sm. lower_value _ _ _ e2 sh1 = _ /\ _ | SOME h => _` mp_tac >>
     Cases_on `bytestring_literal_hash e2` >> simp_tac (srw_ss()) [] >>
     strip_tac >> imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac comparison_hash_shape >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  `fn_has_code sa sh1 func /\ fn_has_code sh1 sh2 func /\
   fn_has_code sh2 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `sa.cs_next_var <= sh1.cs_next_var /\ sh1.cs_next_var <= sh2.cs_next_var` by
    (conj_tac >>
     Cases_on `bytestring_literal_hash e1` >>
     Cases_on `bytestring_literal_hash e2` >> gvs[] >>
     imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac comparison_hash_shape >> decide_tac) >>
  `local_ptrs_reserved cenv sh1 /\ local_ptrs_reserved cenv sh2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] exprBopSimPropsTheory.eval_expr_bop_bind] >>
  Cases_on `bytestring_literal_hash e1`
  >- (gvs[] >>
      `fn_has_code sa sm func /\ fn_has_code sm sh1 func` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         imp_res_tac comparison_hash_shape >>
         metis_tac[fn_has_code_mid, cs_extends_refl]) >>
      irule expr_sim_suffix >>
      qpat_assum `expr_sim _ _ _ _ _ e1 _` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ e1 _ = _` (irule_at Any) >>
      simp[] >>
      (conj_tac >- metis_tac[exprBopSimPropsTheory.bop_first_admissible]) >>
      rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by
        simp[expr_body_pre_gas_obs] >>
      drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
      `expr_sim_case nocalls ctx func cenv cx e2 /\
       expr_vv_case nocalls ctx func cenv cx e2` by
        (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
         qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
         metis_tac[]) >>
      `expr_sim ctx func cenv cx (expr_type e1) e2 ee` by
        (qpat_x_assum `expr_sim_case _ _ _ _ _ e2`
           (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
         disch_then irule >>
         (conj_tac >- gvs[int_calls_expr_def]) >>
         qexists_tac `env` >> simp[]) >>
      `?tv. evaluate_type env.type_defs (expr_type e1) = SOME tv /\
            value_has_type tv v` by
        (qpat_x_assum `!v'. INL v = _ ==> _` (qspec_then `v` mp_tac) >>
         simp[expr_result_typed_def, expr_runtime_typed_def,
              value_result_typed_def]) >>
      `!x. p = Var x ==> not_fresh_at sm x` by
        (qpat_assum `lower_value _ _ _ e1 _ = _`
           (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >>
         simp[]) >>
      `local_ptrs_reserved cenv sm` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         metis_tac[local_ptrs_reserved_next_var]) >>
      `?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
             expr_type e1 = BaseT (StringT cap)` by
        (Cases_on `expr_type e1` >> gvs[is_bytestring_type_def] >>
         rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[is_bytestring_type_def] >> Cases_on `b` >>
         gvs[is_bytestring_type_def])
      >- (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
          Cases_on `v` >> gvs[value_has_type_def] >>
          `evaluate_type (get_tenv cx) (expr_type e1) =
             SOME (BaseTV (BytesT (Dynamic cap)))` by simp[vyperValueTheory.evaluate_type_def] >>
          drule_all comparison_hash_dynamic >> strip_tac >>
          irule_at Any gas_summary_at_zero_prefix >>
          qpat_assum `gas_marked_path F ctx func t 0 (OK t')` (irule_at Any) >>
          Cases_on `bytestring_literal_hash e2`
          >- (gvs[] >>
              `fn_has_code sh1 sm' func /\ fn_has_code sm' sh2 func` by
                (imp_res_tac (cj 2 compile_expr_grows) >>
                 imp_res_tac comparison_hash_shape >>
                 metis_tac[fn_has_code_mid, cs_extends_refl]) >>
              FAIL_TAC "second operand needs outcome continuation") >>
          FAIL_TAC "second literal probe") >>
      FAIL_TAC "string hash probe") >>
  FAIL_TAC "literal probe"
QED
