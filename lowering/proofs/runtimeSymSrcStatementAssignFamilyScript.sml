Theory runtimeSymSrcStatementAssignFamily
Ancestors
  runtimeSymSrcStatementAssign runtimeSymSrcAssignValue runtimeSymSrcAssignTuple
  runtimeSymSrcAssignConstructors runtimeSymSrcAssignUpdates
  runtimeSymSrcDeclarations runtimeSymSrcContextTyped runtimeSymSrcContextCopy
  runtimeSymSrcContext runtimeSymSrcInterfaces supportedStmts supportedStmtTraverse
  stmtLowering exprLowering compileEnv venomInst stackPlanTypes list

(* Publication ledger: all assignment-local operations are discharged below
   using the five family developments. Already published context primitives
   discharge their literal premises. The remaining callback contracts are
   guarded expression/target calls (C1.1.4/C1.1.3), unwrap/snapshot values
   (C1.1.3.2), and binop/dynarray primitives (C1.1.3). No additional source
   restriction is imposed by this join. *)

Theorem runtime_sym_assignment_value:
  ~is_label_operand dst /\ ~is_label_operand value /\
  (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_assign_value ce dst loc value prim sl dt st da n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  mp_tac runtime_sym_compile_assign_value >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[runtime_sym_alloc_buffer]
      >- metis_tac[runtime_sym_copy_memory]
      >- metis_tac[runtime_sym_store_memory]
      >- metis_tac[runtime_sym_store_memory_typed]
      >- metis_tac[runtime_sym_dynarray_to_storage]
      >- metis_tac[runtime_sym_memory_to_storage]
      >- metis_tac[runtime_sym_memory_to_transient]
      >- metis_tac[runtime_sym_imm_store_word]
      >- metis_tac[runtime_sym_store_immutable_bytestring]
      >> metis_tac[runtime_sym_imm_store_words]) >>
  metis_tac[]
QED

Theorem runtime_sym_assignment_store:
  ~is_label_operand dst /\ ~is_label_operand value /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_at_loc imm dst value loc s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> mp_tac runtime_sym_store_at_loc >>
  impl_tac >- (rpt strip_tac >> metis_tac[runtime_sym_imm_store_word]) >>
  metis_tac[]
QED

Theorem runtime_sym_assignment_load:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_tuple_load_all ce src tys off s = (ops,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  EVERY (\op. ~is_label_operand op) ops
Proof
  mp_tac runtime_sym_tuple_load_all >>
  impl_tac >- metis_tac[runtime_sym_load_memory] >>
  metis_tac[]
QED

Theorem runtime_sym_assignment_target_base:
  supported_append_target tops target ==>
  ~is_label_operand (compile_target_base ce target)
Proof
  Cases_on `target` >> simp[supported_append_target_def, compile_target_base_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars p` >> simp[is_label_operand_def] >>
  Cases_on `x` >> simp[is_label_operand_def]
QED

Theorem runtime_sym_assignment_unpack:
  (!bt s op loc pt s'. runtime_sym_env ce /\
    supported_target tops bindings bt /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !st mem targets e op s u s'.
    runtime_sym_env ce /\
    supported_assignment tops bindings (TupleTarget targets) e /\
    ~supported_assignments_exists is_self_code targets /\
    ~is_label_operand op /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_unpack ce st mem targets op s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `!t. MEM t targets ==> ~supported_assignment_exists is_self_code t` by
    (qpat_x_assum `~supported_assignments_exists _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Induct_on `targets` >> simp[supported_assignment_exists_def] >> metis_tac[]) >>
  `!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b` by
    fs[runtime_sym_env_def] >>
  mp_tac runtime_sym_tuple_unpack_boundary >>
  impl_tac
  >- (conj_tac >- metis_tac[runtime_sym_alloc_buffer] >>
      conj_tac >- metis_tac[runtime_sym_assignment_load] >>
      rpt gen_tac >> strip_tac >>
      mp_tac runtime_sym_tuple_store_all >> impl_tac
      >- (conj_tac
          >- (rpt gen_tac >> strip_tac >> irule runtime_sym_assignment_value >>
              goal_assum (drule_at Any) >> simp[]) >>
          rpt gen_tac >> strip_tac >> irule runtime_sym_assignment_store >>
          goal_assum (drule_at Any) >> simp[]) >>
      disch_then (drule_at (Pat `compile_tuple_store_all _ _ _ _ _ = _`)) >>
      impl_tac
      >- (simp[] >> rpt gen_tac >> strip_tac >>
          `supported_target tops bindings bt` by
            (qpat_x_assum `supported_assignment _ _ _ _` mp_tac >>
             simp[supported_assignment_def, EVERY_MEM] >> strip_tac >>
             first_x_assum (qspec_then `BaseTarget bt` mp_tac) >> simp[]) >>
          `~supported_target_exists is_self_code bt` by
            (qpat_x_assum `!t. MEM t targets ==> _`
               (qspec_then `BaseTarget bt` mp_tac) >>
             simp[supported_assignment_exists_def]) >>
          qpat_x_assum `!bt s op loc pt s'. _` drule_all >> simp[]) >>
      simp[]) >>
  metis_tac[]
QED

Theorem runtime_sym_assignment_annassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (AnnAssign id vtyp e)
Proof
  strip_tac >> irule runtime_sym_stmt_annassign >> rpt conj_tac
  >- metis_tac[runtime_sym_emit_local_alloca]
  >- (rpt gen_tac >> strip_tac >> irule runtime_sym_assignment_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Theorem runtime_sym_assignment_baseassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!s op loc pt s'. runtime_sym_env ce /\
    supported_assignment tops bindings (BaseTarget bt) e /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!v s out s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ compile_snapshot_vv ce T v s = (out,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value out) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assign (BaseTarget bt) e)
Proof
  strip_tac >> irule runtime_sym_stmt_baseassign >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >> strip_tac >> irule runtime_sym_assignment_value >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt gen_tac >> strip_tac >> irule runtime_sym_assignment_store >>
      goal_assum (drule_at Any) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_sym_assignment_tupleassign:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  (!v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce v s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!bt s op loc pt s'. runtime_sym_env ce /\
    supported_target tops bindings bt /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assign (TupleTarget targets) e)
Proof
  strip_tac >> irule runtime_sym_stmt_tupleassign >> simp[] >>
  drule runtime_sym_assignment_unpack >> metis_tac[]
QED

(* AugAssign has no assignment-local premises: runtime_sym_stmt_augassign
   is already the published constructor boundary, imported unchanged. *)
Theorem runtime_sym_assignment_append:
  (!t s op s'. runtime_sym_env ce /\ supported_expr tops val_e /\
    ~supported_expr_exists is_self_code val_e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t val_e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!base v ws es et st cap prim load store s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Append target val_e)
Proof
  strip_tac >> irule runtime_sym_stmt_append >> rpt conj_tac
  >- metis_tac[runtime_sym_alloc_buffer]
  >- first_assum ACCEPT_TAC
  >- metis_tac[runtime_sym_store_memory]
  >- first_assum ACCEPT_TAC >>
  metis_tac[runtime_sym_assignment_target_base]
QED
