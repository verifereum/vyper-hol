(* Joint two-shift MethodId selector, independent of hashing and allocation. *)
Theory bodyFullBuiltinEnvMethodIdSelector
Ancestors
  methodIdSelectorObserved
  vyperStorageFootprint vyperStorageTrace exprSimHash bodyFullGhostFrame fragGasSeqPtr emitHelperProps emitHelper
  exprLoweringProps compileEnv fragExec fragExecMem loweringStateRelDefs
  allocaHistoryFragment instMemFrontier memSafeRun loweringSlice
  contextCodegenRel codegenRel ptrSafeRun bodyPtrDefs ptrDiscipline ptrDisciplineEmptyTaint
  venomState venomInst venomExecSemantics finite_map list rich_list

Theorem method_id_selector_full_run:
  builtin_result cx acc ann MethodId [ty] [v] = INL r /\
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) /\
  eval_operand hash s = SOME w /\ op_taint tn hash = {} /\
  op_prov G hash = NONE /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s)
  ==> ?t G' tn'.
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    eval_operand op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
        (BytesV (TAKE 4 (word_to_bytes w T)))) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)
Proof
  strip_tac >> drule_all method_id_selector_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED
