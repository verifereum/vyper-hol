(* The successful scalar operator and its read-only frame share an endpoint. *)
Theory bodyAugOperatorSuccessMods
Ancestors
  augAssignFullOperatorExec augAssignFullScalarSuccess augAssignPtrCompiler
  bodyAugReadOnlyFrameMods fragGasFresh freshWrites varsExt bodyUnopFragMemory
  exprBopSimProps exprSimDefs loweringPosts ptrDiscipline stateFrame
  venomExecSemantics venomState venomInst compileEnv finite_map pred_set list rich_list

Theorem augassign_operator_success_path_mods:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  type_bits ty MOD 8 = 0 /\ is_word_type ty /\
  (bop = Exp ==>
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==>
    (?i. v2 = IntV i /\ 0 <= i) \/
    (ty = BaseT (BytesT (Fixed 32)) /\ ?bs. v2 = BytesV bs /\ LENGTH bs = 32)) /\
  evaluate_type (get_tenv cx) ty = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type (get_tenv cx) t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  bop_result cx ty bop tys v1 v2 es = INL v /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fn_has_code sa sb func /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  (!l. x <> Label l /\ y <> Label l) /\
  eval_operand x s = SOME (typed_val_to_w256 tv1 v1) /\
  eval_operand y s = SOME (typed_val_to_w256 tv2 v2) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> allocas_from lo s) ==>
  ?u G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')) /\
    expr_val_rel cx ty v op u /\ eval_operand op u = SOME (typed_val_to_w256 tv1 v) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sb.cs_current_bb = sa.cs_current_bb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s /\
          FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
    eval_operand x u = SOME (typed_val_to_w256 tv1 v1) /\
    eval_operand y u = SOME (typed_val_to_w256 tv2 v2) /\
    op_prov G' x = NONE /\ op_taint tn' x = {} /\
    op_prov G' y = NONE /\ op_taint tn' y = {}
Proof
  strip_tac >>
  drule_all_then assume_tac typed_binop_scalar_member_ptr >>
  `straight_fresh (compile_binop bop x y ty bl el)` by
    metis_tac[compile_binop_straight_fresh_ptr] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [straight_fresh_def]
    compile_binop_straight_fresh_ptr) >>
  drule_then assume_tac writes_fresh_path_opcodes >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_assum `writes_fresh _ _` mp_tac >>
     simp_tac std_ss [writes_fresh_def, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> simp[fresh_write_op_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[writes_fresh_mem_ok] >>
  drule_all_then strip_assume_tac straight_fresh_code_prefix >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
        expr_val_rel cx ty v op t0` by suspend "typed" >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all_then strip_assume_tac compile_binop_clean_certificate_ptr >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all augassign_scalar_success_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  conj_tac >-
    (rpt strip_tac >> simp[Abbr `u`, LENGTH_APPEND] >> metis_tac[]) >>
  suspend "frame"
QED

Resume augassign_operator_success_path_mods[typed]:
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s) = SOME (typed_val_to_w256 tv1 v1) /\
   eval_operand y (drop_fresh sa s) = SOME (typed_val_to_w256 tv2 v2)` by
    metis_tac[eval_operand_drop_fresh] >>
  `expr_res_ok (bop_result cx ty bop tys v1 v2 es)` by simp[expr_res_ok_def] >>
  drule_all augassign_typed_execution >> gvs[] >> metis_tac[]
QED

Resume augassign_operator_success_path_mods[frame]:
  `eval_operand op t0 = SOME (typed_val_to_w256 tv1 v)` by
    metis_tac[expr_val_rel_typed] >>
  `eval_operand op u = SOME (typed_val_to_w256 tv1 v)` by suspend "result" >>
  `expr_val_rel cx ty v op u` by simp[expr_val_rel_def] >>
  drule_all_then strip_assume_tac run_inst_seq_writes_fresh >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_labels = s.vs_labels` by
    (simp[Abbr `u`] >> qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
     simp[state_frame_def]) >>
  `!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s /\
        FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)` by
    suspend "old_vars" >>
  `eval_operand x u = eval_operand x s /\
   op_prov G' x = op_prov G x /\ op_taint tn' x = op_taint tn x` by
    (irule aug_readonly_saved_operand_mods >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `eval_operand y u = eval_operand y s /\
   op_prov G' y = op_prov G y /\ op_taint tn' y = op_taint tn y` by
    (irule aug_readonly_saved_operand_mods >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
  simp[]
QED

Resume augassign_operator_success_path_mods[result]:
  `eval_operand op t = SOME (typed_val_to_w256 tv1 v)` by
    (fs[vars_ext_def] >> qpat_assum `t = t0 with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  simp[Abbr `u`, instIdxIndepTheory.eval_op_inst_idx]
QED

Resume augassign_operator_success_path_mods[old_vars]:
  rpt strip_tac
  >- simp[Abbr `u`, lookup_var_def] >>
  `~MEM z (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (qpat_assum `writes_fresh _ _` mp_tac >>
     simp_tac std_ss [writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >> metis_tac[]
QED

Finalise augassign_operator_success_path_mods
