(* Constructor scaffolding preserves call-freedom up to the internal suffix. *)
Theory ctorCallFreeWrapper
Ancestors
  ctorCallFreeABIDecode ctorCallFreeStmtReturns ctorCallFreeEntry
  ctorDeployLoweringCode ctorDeployLoweringCodeShape ctorUnitShape
  loweringFunctionOpcodes ctorCallFreeValues moduleLowering compileEnv context emitHelper
  loweringShapeDefs vyperCompiler compileVyper list venomInst ctorCallFreeRules
  externalEntryShape

Theorem call_free_fixed_region[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_fixed_region) >> simp[]
QED

Theorem call_free_nonreentrant_lock[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_nonreentrant_lock key trans view st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_nonreentrant_lock) >> simp[]
QED

Theorem call_free_constructor_epilogue[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_constructor_epilogue sz cap imm st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] outcomes_free_constructor_epilogue) >> simp[]
QED

Theorem call_free_register_constructor_args[local]:
  !args ce off sz st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_register_constructor_args ce args off sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] outcomes_free_register_constructor_args) >>
  simp[DISJ_IMP_THM]
QED

Theorem register_constructor_args_labels[local]:
  !args ce off sz st.
    cs_extends st (SND (compile_register_constructor_args ce args off sz st)) /\
    EVERY (isPREFIX "@") (added_labels st
      (SND (compile_register_constructor_args ce args off sz st)))
Proof
  Induct >> simp[compile_register_constructor_args_def, comp_return_labels] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_register_constructor_args_def] >>
  rpt (FIRST [ho_match_mp_tac comp_bind_labels >> conj_tac,
    ho_match_mp_tac comp_ignore_bind_labels >> conj_tac,
    gen_tac, CHANGED_TAC (simp[compile_alloc_buffer_labels, compile_decode_args_labels,
      comp_return_labels]),
    CHANGED_TAC BasicProvers.TOP_CASE_TAC >> gvs[]]) >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac comp_bind_labels >> conj_tac,
    ho_match_mp_tac comp_ignore_bind_labels >> conj_tac,
    gen_tac, CHANGED_TAC (simp[compile_alloc_buffer_labels, compile_decode_args_labels,
      comp_return_labels])])
QED

Theorem constructor_epilogue_labels[local]:
  !sz cap imm st.
    cs_extends st (SND (compile_constructor_epilogue sz cap imm st)) /\
    EVERY (isPREFIX "@") (added_labels st
      (SND (compile_constructor_epilogue sz cap imm st)))
Proof
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_constructor_epilogue_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac comp_bind_labels >> conj_tac,
    ho_match_mp_tac comp_ignore_bind_labels >> conj_tac,
    gen_tac, CHANGED_TAC (simp[emit_op_labels, emit_void_labels,
      emit_inst_labels, compile_alloc_buffer_labels, comp_return_labels])])
QED

Theorem call_free_constructor_prefix[local]:
  (!ce st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce NoLoop NoneT fbody st)))) ==>
  !st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) args 0 sz;
          (if nr then compile_nonreentrant_lock key trans view else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans view else return ());
          compile_constructor_epilogue runtime_size cap imm od st)))
Proof
  strip_tac >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_return, every_state_insts_get,
      every_state_insts_new_block, every_state_insts_fresh_label,
      call_free_fixed_region, call_free_register_constructor_args,
      call_free_nonreentrant_lock, call_free_nonreentrant_unlock,
      call_free_constructor_epilogue])])
QED

Theorem constructor_prefix_labels[local]:
  !st.
    cs_extends st (SND
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) args 0 sz;
          (if nr then compile_nonreentrant_lock key trans view else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans view else return ());
          compile_constructor_epilogue runtime_size cap imm od st)) /\
    EVERY (isPREFIX "@") (added_labels st (SND
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) args 0 sz;
          (if nr then compile_nonreentrant_lock key trans view else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans view else return ());
          compile_constructor_epilogue runtime_size cap imm od st)))
Proof
  rpt (FIRST [irule fresh_label_bind_labels,
    irule new_block_action_labels >> simp[],
    irule comp_bind_labels >> conj_tac,
    irule comp_ignore_bind_labels >> conj_tac,
    gen_tac, disch_tac, IF_CASES_TAC >> gvs[],
    CHANGED_TAC (simp[emit_op_labels, emit_void_labels, emit_inst_labels,
      comp_return_labels, comp_get_labels, compile_fixed_region_with_id_labels,
      register_constructor_args_labels, compile_nonreentrant_lock_labels,
      stmt_context_helpers_labels, compile_stmt_labels, constructor_epilogue_labels])])
QED

Theorem ctor_prefix_from_trace[local]:
  (if pay then comp_return () else
     do cv <- emit_op CALLVALUE []; v <- emit_op ISZERO [cv]; emit_void ASSERT [v] od)
      si = ((),sp) /\
  (if data_size > 0 then
     do p <- compile_fixed_region_with_id data_size; comp_return (SND p).buf_operand od
   else comp_return (Lit 0w)) sp = (imm,s1) /\
  compile_register_constructor_args
    (cenv with ce_imm_alloca := if data_size > 0 then SOME imm else NONE)
    args 0 0 s1 = (ce,s2) /\
  (if nr then compile_nonreentrant_lock key trans F else comp_return ()) s2 = ((),s3) /\
  fresh_label "ctor_exit" s3 = (lbl,sa) /\
  compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody sa = ((),sb) /\
  (if block_is_terminated sb then comp_return () else emit_inst JMP [Label lbl] []) sb = ((),sj) /\
  new_block lbl sj = (bb,sx) /\
  (if nr then compile_nonreentrant_unlock key trans F else comp_return ()) sx = ((),se) /\
  compile_constructor_epilogue runtime_size data_size imm se = ((),sf) ==>
  (do (if ~pay then
         do cv <- emit_op CALLVALUE []; no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
       else return ());
      imm <- (if data_size > 0 then
                do p <- compile_fixed_region_with_id data_size; return (SND p).buf_operand od
              else return (Lit 0w));
      ce <- compile_register_constructor_args
        (cenv with ce_imm_alloca := if data_size > 0 then SOME imm else NONE) args 0 0;
      (if nr then compile_nonreentrant_lock key trans F else return ());
      lbl <- fresh_label "ctor_exit";
      compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
      cs <- comp_get;
      (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
      new_block lbl;
      (if nr then compile_nonreentrant_unlock key trans F else return ());
      compile_constructor_epilogue runtime_size data_size imm od) si = ((),sf)
Proof
  strip_tac >> Cases_on `pay` >>
  rule_assum_tac (PURE_REWRITE_RULE [NOT_CLAUSES, COND_CLAUSES]) >>
  pure_rewrite_tac[NOT_CLAUSES, COND_CLAUSES] >>
  rpt (CHANGED_TAC (pure_once_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
                    pure_asm_rewrite_tac[comp_get_def, LET_THM] >> simp[]))
QED

Theorem constructor_prefix_label_absent[local]:
  !s n. cs_extends (initial_compile_state "__deploy") s /\
    EVERY (isPREFIX "@") (added_labels (initial_compile_state "__deploy") s) /\
    n <> "__deploy" /\ ~isPREFIX "@" n ==>
    ~MEM n (MAP (\bb. bb.bb_label) (all_blocks s))
Proof
  rpt gen_tac >> strip_tac >> drule cs_extends_labels >>
  disch_then SUBST1_TAC >> simp[MEM_APPEND] >> conj_tac
  >- simp[initial_compile_state_def, all_blocks_def] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem deploy_ctor_call_free_prefix:
  !tops rpolicy runtime_bc dunit exts ints fb cf
   cenv args pay nr key trans fbody ret.
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  set_constructor_package_target rpolicy.rpol_target
    (package_constructor tops T (K global_nonreentrant_slot) cf) =
      (cenv,args,pay,nr,key,trans,fbody,ret) /\
  cenv.ce_return_pc = NONE /\
  cenv.ce_nonreentrant = (nr,key,trans,F) /\
  ~supported_stmts_expr_exists expr_shape_root fbody /\
  (!ce st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_stmts ce NoLoop NoneT fbody st)))) ==>
  ?se sf ctx data.
    compile_internal_fn_bodies
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
        (order_internals (deploy_internal_order (SOME cf) ints) ints))
      se = ((),sf) /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts se) /\
    ((order_internals (deploy_internal_order (SOME cf) ints) ints) <> [] ==> ~MEM
      (FST (HD (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
        (order_internals (deploy_internal_order (SOME cf) ints) ints))))
      (MAP (\bb. bb.bb_label) (all_blocks se))) /\
    extract_context_with_internals "__deploy"
      (MAP (set_internal_package_target rpolicy.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
        (order_internals (deploy_internal_order (SOME cf) ints) ints))
      sf = SOME (ctx,data) /\
    dunit.cu_context = install_immutable_reservation (imm_len tops) ctx
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >> gvs[] >>
  rename1 `compile_stmts _ NoLoop NoneT fbody _ = _` >>
  drule_all ctor_prefix_from_trace >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts st_final)` by
    (drule call_free_constructor_prefix >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
        (state_insts (initial_compile_state "__deploy"))` by
       simp[initial_compile_state_def, state_insts_def, all_blocks_def] >>
     metis_tac[pairTheory.SND]) >>
  `cs_extends (initial_compile_state "__deploy") st_final /\
   EVERY (isPREFIX "@") (added_labels (initial_compile_state "__deploy") st_final)` by
    (qpat_assum `_ (initial_compile_state "__deploy") = ((),st_final)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[constructor_prefix_labels, pairTheory.SND]) >>
  qexistsl_tac [`st_final`, `post`, `ctx`, `data`] >> simp[] >>
  strip_tac >> irule constructor_prefix_label_absent >> simp[] >>
  Cases_on `order_internals (deploy_internal_order (SOME cf) ints) ints` >> gvs[] >> PairCases_on `h` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       internal_label_ok_def, internal_fn_label_prefix, internal_fn_label_def]
QED
