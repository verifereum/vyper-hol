(* Checked runtime entry for immutable array iteration. *)
Theory bodyImmEntryPtr
Ancestors
  immutableRegionLoadPtr bodyImmEntryMemory forPtrArrayEntry
  bodyPtrBytestringBuiltinsCalldataReserved augAssignPtrScalarContinuation
  stmtSimForArrayLoop loweringPosts logTopicScalarPtr
  ptrDiscipline immutableCopyExecution fragGasSeqPtr stmtAppendStorageRunPtr exprSimStorageCopy
  exprSimBopRestWordLoads exprSimBopRestWordLoadPath
  appendStorageGhostPtr augAssignPtrScalarFrame abiDecodePtrScalarReplay
  bodyPtrDefs stmtSimProps exprSimCopy exprLoweringProps
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs
  venomInst venomState finite_map words list arithmetic rich_list stmtSimDefs fragExec
Libs monadsyntax

Theorem immutable_optional_length_checked:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) ==>
  ?t H tm.
    copy_runtime_frame sa s sb t /\ t = s with vs_vars := t.vs_vars /\
    eval_operand lvo t = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb lvo /\ op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    (!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H tm) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  Cases_on `dyn` >> simp[comp_return_def] >> strip_tac
  >- (gvs[] >>
      `context$compile_ptr_load F cenv.ce_imm_alloca LocCode
         (Lit (n2w off)) sa = (lvo,sb)` by simp[compile_ptr_load_def] >>
      `eval_operand (Lit (n2w off)) s = SOME (n2w off : bytes32)` by
        simp[eval_operand_def] >>
      drule_all rest_word_array_immutable_header >> strip_tac >>
      drule compile_imm_load_word_checked >>
      simp[eval_operand_def, op_taint_def] >> strip_tac >>
      gvs[GSYM immutable_copy_read_def] >>
      `!t. copy_runtime_frame sa s sb t ==> t = s with vs_vars := t.vs_vars` by
        (rpt strip_tac >> drule rest_word_ptr_load_run_frame >> simp[] >>
         fs[copy_runtime_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  gvs[] >> qexistsl [`s`,`G`,`tn`] >>
  simp[copy_runtime_frame_def, copy_static_def, emitted_insts_def,
    copy_old_operand_def, eval_operand_def, op_prov_def, op_taint_def,
    inst_seq_ptr_def, run_inst_seq_def, same_blocks_def]
QED

Theorem immutable_optional_length_path_ptr:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ ghost_inv d cenv cx es H tm u /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb lvo /\ op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    ret_pc_ok cenv sa u /\ array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all immutable_optional_length_checked >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (Cases_on `dyn`
     >- (`context$compile_ptr_load F cenv.ce_imm_alloca LocCode
          (Lit (n2w off)) sa = (lvo,sb)` by gvs[compile_ptr_load_def] >>
         drule rest_word_ptr_load_code >> simp[] >> strip_tac >>
         fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
         simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
     gvs[comp_return_def, emitted_insts_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, copy_runtime_frame_def, same_blocks_def] >>
     simp[DROP_APPEND]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 H tm
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (fs[copy_runtime_frame_def, EVERY_CONJ] >>
     `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm` by
       (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
       (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_ptr >>
     simp[EVERY_CONJ, ADD_COMM] >>
     disch_then irule >> metis_tac[]) >>
  `tm.t_imm = tn.t_imm` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `0` assume_tac) >>
     fs[EVERY_CONJ] >> metis_tac[inst_seq_ptr_immutable_taint_frame]) >>
  suspend "length_frame"
QED
Resume immutable_optional_length_path_ptr[length_frame]:
  qexistsl [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`tm`] >>
  simp[] >> suspend "length_frame_finish"
QED
Resume immutable_optional_length_path_ptr[length_frame_finish]:
  `stmt_state_rel ctx func cenv cx es t` by
    (irule bodyPtrBytestringBuiltinsCalldataReservedTheory.stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> fs[copy_runtime_frame_def] >> metis_tac[]) >>
  `ghost_inv d cenv cx es H tm t` by
    (irule ghost_inv_old_transport >>
     conj_tac >- (qpat_x_assum `t = _` SUBST_ALL_TAC >>
       gvs[ghost_inv_def, stor_taint_ok_def]) >>
     qexistsl [`G`,`es`,`s`,`sa`,`tn`] >>
     fs[copy_runtime_frame_def] >>
     qpat_x_assum `t = _` SUBST_ALL_TAC >> simp[]) >>
  fs[copy_runtime_frame_def, same_blocks_def] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx] >>
  gvs[array_caller_frame_def, ret_pc_ok_def, lookup_var_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[venom_state_fupdcanon]
QED
Finalise immutable_optional_length_path_ptr
