(* Counted simulation of dynamic bytestring equality and inequality. *)

Theory exprSimBopBytestring
Ancestors
  exprSimHashBoundary bytestringHashProps
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomInst venomState
  valueEncoding ASCIInumbers words
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
  sa.cs_next_var <= sb.cs_next_var
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
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
  cheat
QED
