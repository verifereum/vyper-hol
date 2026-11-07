(* Counted simulation of dynamic bytestring equality and inequality. *)

Theory exprSimBopBytestring
Ancestors
  exprSimHashBoundary bytestringHashProps
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
  ASM_SIMP_TAC std_ss [Once step_inst_base_def, exec_pure2_def] >>
  simp[Once run_inst_seq_def] >>
  ASM_SIMP_TAC std_ss [Once step_inst_base_def, exec_pure1_def,
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
  cheat
QED
