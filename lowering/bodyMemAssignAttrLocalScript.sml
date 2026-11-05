(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a local struct (S1's body_assign_attr_local). *)
Theory bodyMemAssignAttrLocal
Ancestors
  bodyMemoryPreds bodyFieldMemoryProps bodyDeclMemoryCounted
  exprSimVVFrame exprOperandVar emitHelperProps gasSummary fragGasMode
  venomState venomInst venomExecSemantics compileEnv emitHelper fragExec
  words ASCIInumbers exprLoweringProps

Theorem assign_attr_local_add_exact_mem[local]:
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts))
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    metis_tac[attr_add_prefix_mem_ok] >>
  `same_blocks sm sn /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
         fresh_var_def, emit_def, same_blocks_def, mk_inst_def,
         is_terminator_def]) >>
  drule_all body_decl_cursor_path >>
  simp[gas_marked_path_def]
QED

Theorem assign_attr_local_add_post_mem[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  alloca_history func s ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    alloca_history func q /\ ~q.vs_halted /\
    q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_memory = s.vs_memory /\
    local_ptrs_reserved cenv sn /\
    sm.cs_next_var <= sn.cs_next_var /\
    (?out. dst = Var out /\ not_fresh_at sn out) /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  drule_all assign_attr_local_add_exact_mem >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `alloca_inv s` by gvs[loweringPostsTheory.vv_post_def,
                       stmt_state_rel_def] >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  drule_all attr_add_history >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, update_var_def,
      eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >>
  irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Theorem body_assign_attr_local_mem:
  !cx id fld e sid fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  cheat
QED
