(*
 * S2 of #626 decomposed: the raw runtime lowering emits O1 source shape.
 *
 * Each generator family gets one shape_step fact (loweringShapeDefs); the
 * runtime stream lemma assembles them, package_internal_blocks_segments
 * splits the stream exactly at the internal entry labels, and
 * run_lowering_source_unit_ok reads o1_source_unit_ok off the packaged
 * unit.
 *
 * TOP-LEVEL:
 *   expr_shape_root            — the source forms whose lowering breaks the
 *                                shape (msg.gas, raw_call(msg.data),
 *                                selfdestruct) and
 *                                builtins with too few arguments
 *   cenv_shape_ok, cenv_static_ok, value_shape_ok, loop_ctx_shape_ok
 *   external_fn_shape_ok, fallback_shape_ok, internal_fn_shape_ok
 *   internal_segment_ok        — one internal function's blocks
 *   internal_label_ok          — internal entry labels ("internal ..."),
 *                                apart from every other label
 *   compile_expr_shape, compile_stmt_shape, compile_*_shape
 *   compile_generate_runtime_shape — the whole runtime block stream
 *   package_internal_blocks_segments
 *   run_lowering_source_unit_ok
 *   supported_function_body_shape, package_*_shape_ok — supported_program
 *                                gives the generator side conditions
 *)
Theory loweringShapeProps
Ancestors
  list rich_list loweringShapeDefs loweringShapeRules compileEnv context
  emitHelper exprLowering stmtLowering moduleLowering vyperCompiler
  compileVyper abiEncoder supportedProgram supportedNames
  supportedStmtTraverse supportedExprTraverse unitShapeDefs venomInst vyperAST

(* ===== Side conditions ===== *)

(* How many arguments the builtin dispatchers read by position (HD, EL n).
   Fewer leaves HD [] for compile_expr, an unspecified expression. *)
Definition builtin_arity_def:
  builtin_arity bi =
    case bi of
      Bop _ => 2:num | AddMod => 3 | MulMod => 3 | Slice _ => 3
    | ECRecover => 4 | PowMod256 => 2 | ECAdd => 2 | ECMul => 2
    | Len => 1 | CalldataSlice _ => 1 | Not => 1 | Neg => 1 | Abs => 1
    | Keccak256 => 1 | Sha256 => 1 | AsWeiValue _ => 1 | Uint2Str _ => 1
    | Ceil => 1 | Floor => 1 | BlockHash => 1 | BlobHash => 1 | Acc _ => 1
    | MethodId => 1
    | _ => 0
End

Definition type_builtin_arity_def:
  type_builtin_arity tb =
    case tb of
      Convert => 1:num | Extract32 => 2 | AbiEncode _ _ => 1
    | AbiDecode _ => 1 | _ => 0
End

(* msg.gas returns a GAS output as an ordinary value; raw_call(t, msg.data)
   lowers to DALLOCA (and DELEGATECALL with is_delegate_call); selfdestruct
   emits SELFDESTRUCT, excluded by the current instruction shape policy;
   a builtin with too few arguments compiles HD []. *)
Definition expr_shape_root_def:
  expr_shape_root e <=>
    (?ty es. e = Builtin ty (Env MsgGas) es) \/
    (?ty flags es d. e = Call ty (RawCallCalldataTarget flags) es d) \/
    (?ty es d. e = Call ty SelfDestructTarget es d) \/
    (?ty bi es. e = Builtin ty bi es /\ LENGTH es < builtin_arity bi) \/
    (?ty tb target es. e = TypeBuiltin ty tb target es /\
                       LENGTH es < type_builtin_arity tb)
End

(* No ImmutableLoc: its LocCode reads lower to DLOAD. *)
Definition loc_shape_ok_def:
  loc_shape_ok st (PtrVar op sz) = plain_operand st op /\
  loc_shape_ok st (ImmutableLoc n) = F /\
  loc_shape_ok st (MemLoc off sz) = T /\
  loc_shape_ok st (StorageLoc slot) = T /\
  loc_shape_ok st (TransientLoc slot) = T
End

(* ce_return_pc decides the Return lowering: NONE is external code. *)
Definition cenv_shape_ok_def:
  cenv_shape_ok st cenv <=>
    (!n loc. FLOOKUP cenv.ce_vars n = SOME loc ==> loc_shape_ok st loc) /\
    (!loc. cenv.ce_return_buf = SOME loc ==> loc_shape_ok st loc) /\
    case cenv.ce_return_pc of
      NONE => T
    | SOME (MemLoc off sz) => T
    | SOME (PtrVar op sz) => retpc_operand st op \/ plain_operand st op
    | SOME _ => F
End

(* What package_*_fn builds, before any code is emitted. *)
Definition static_loc_def:
  static_loc (MemLoc off sz) = T /\
  static_loc (StorageLoc slot) = T /\
  static_loc (TransientLoc slot) = T /\
  static_loc (PtrVar op sz) = F /\
  static_loc (ImmutableLoc n) = F
End

Definition cenv_static_ok_def:
  cenv_static_ok cenv <=>
    (!n loc. FLOOKUP cenv.ce_vars n = SOME loc ==> static_loc loc) /\
    (!loc. cenv.ce_return_buf = SOME loc ==> ?off sz. loc = MemLoc off sz) /\
    (!loc. cenv.ce_return_pc = SOME loc ==> ?off sz. loc = MemLoc off sz)
End

Definition value_shape_ok_def:
  value_shape_ok st (StackValue ty op) = plain_operand st op /\
  value_shape_ok st (LocatedValue ty p) =
    (plain_operand st p.ptr_operand /\ p.ptr_location <> LocCode /\
     !b. p.ptr_buf = SOME b ==> plain_operand st b.buf_operand)
End

Definition loop_ctx_shape_ok_def:
  loop_ctx_shape_ok NoLoop = T /\
  loop_ctx_shape_ok (InLoop break_lbl continue_lbl) =
    (jump_label_ok break_lbl /\ jump_label_ok continue_lbl)
End

Definition external_fn_shape_ok_def:
  external_fn_shape_ok
    (entry_lbl, cenv, pos_args, min_cds, is_payable, is_nr, nkey,
     use_trans, is_view, body, ret_type) <=>
    isPREFIX "fn_" entry_lbl /\ cenv_static_ok cenv /\
    cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body
End

Definition fallback_shape_ok_def:
  fallback_shape_ok NONE = T /\
  fallback_shape_ok
    (SOME (cenv, is_payable, is_nr, nkey, use_trans, is_view, body,
           ret_type)) =
    (cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
     ~supported_stmts_expr_exists expr_shape_root body)
End

Definition internal_fn_shape_ok_def:
  internal_fn_shape_ok
    (fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans, is_view,
     is_ctor, imm_len, body, ret_type) <=>
    cenv_static_ok cenv /\
    ~supported_stmts_expr_exists expr_shape_root body
End

(* The blocks of one internal function: its entry label first, then only
   compiler labels; internal-function code throughout. *)
Definition internal_segment_ok_def:
  internal_segment_ok (lbl : string, has_ret_buf : bool, rc : num) seg <=>
    seg <> [] /\ (HD seg).bb_label = lbl /\
    EVERY compiler_label (TL (MAP (\bb. bb.bb_label) seg)) /\
    EVERY (\bb. EVERY (lowered_inst_ok T) bb.bb_instructions) seg
End

(* Internal entry labels are internal_fn_label's "internal ..." spelling,
   so they avoid the reserved labels and every other label the lowering
   makes: "__entry", compiler labels ("@...") and external entry labels
   ("fn_" ++ name). *)
Definition internal_label_ok_def:
  internal_label_ok lbl <=> isPREFIX "internal " lbl
End

(* ===== Stability ===== *)

Theorem loc_shape_ok_mono:
  !internal LP st st' loc.
    shape_extends internal LP st st' /\ loc_shape_ok st loc ==>
    loc_shape_ok st' loc
Proof
  Cases_on `loc` >> rw[loc_shape_ok_def] >> metis_tac[plain_operand_mono]
QED

Theorem cenv_shape_ok_stable:
  !cenv. shape_stable (\st. cenv_shape_ok st cenv)
Proof
  rw[shape_stable_def, cenv_shape_ok_def]
  >- metis_tac[loc_shape_ok_mono]
  >- metis_tac[loc_shape_ok_mono]
  >> BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[plain_operand_mono, retpc_operand_mono]
QED

Theorem value_shape_ok_stable:
  !v. shape_stable (\st. value_shape_ok st v)
Proof
  Cases >> rw[shape_stable_def, value_shape_ok_def] >>
  metis_tac[plain_operand_mono]
QED

Theorem cenv_static_ok_shape_ok:
  !cenv st. cenv_static_ok cenv ==> cenv_shape_ok st cenv
Proof
  rw[cenv_static_ok_def, cenv_shape_ok_def]
  >- (res_tac >> Cases_on `loc` >> gvs[static_loc_def, loc_shape_ok_def])
  >- (res_tac >> gvs[loc_shape_ok_def])
  >> Cases_on `cenv.ce_return_pc` >> simp[] >> res_tac >> gvs[]
QED

(* ===== Expression and statement lowering ===== *)

Theorem compile_ptr_load_shape:
  !loc is_ctor op internal.
    loc <> LocCode ==>
    shape_step internal compiler_label (\st. plain_operand st op)
      (compile_ptr_load is_ctor loc op) (\x st. plain_operand st x)
Proof
    rpt strip_tac >> Cases_on `is_label_operand op`
  >- simp[shape_step_def, plain_operand_def] >>
  Cases_on `loc` >> gvs[compile_ptr_load_def] >>
  (irule shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. T /\ EVERY (label_or_plain st) [op]`,
            `\x st. T /\ plain_operand st x`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[label_or_plain_def] >>
  conj_tac >- simp[] >>
  match_mp_tac (BETA_RULE (Q.SPECL [`internal`, `compiler_label`, `\st. T`]
    shape_step_emit_op)) >>
  simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def])
QED

Theorem compile_alloc_buffer_shape:
  !nbytes internal.
    shape_step internal compiler_label (\st. T)
      (compile_alloc_buffer nbytes) (\buf st. plain_operand st buf.buf_operand)
Proof
  rpt gen_tac >> simp[compile_alloc_buffer_def] >>
  irule shape_step_bind >> qexists_tac `\op st. plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl [`compiler_label`,
            `\st. T /\ EVERY (label_or_plain st) [Lit (n2w nbytes)]`,
            `\x st. T /\ plain_operand st x`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  conj_tac >- simp[] >>
  match_mp_tac (BETA_RULE (Q.SPECL [`internal`, `compiler_label`, `\st. T`]
    shape_step_emit_op)) >>
  simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shape_step_emit_op_guarded:
  !internal LP P opc ops.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
    shape_step internal LP P (emit_op opc ops)
      (\x st. P st /\ plain_operand st x)
Proof
  rpt gen_tac >> strip_tac >> rw[shape_step_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all shape_step_emit_op >>
  simp[shape_step_def] >> disch_then drule_all >> simp[]
QED

Theorem shape_step_emit_inst_guarded:
  !internal LP P opc ops outs.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      (!id. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
    shape_step internal LP P (emit_inst opc ops outs) (\x st. P st)
Proof
  rpt gen_tac >> strip_tac >> rw[shape_step_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all shape_step_emit_inst >>
  simp[shape_step_def] >> disch_then drule_all >> simp[]
QED

Theorem shape_step_pure_pre:
  !internal LP b P m Q.
    (b ==> shape_step internal LP P m Q) ==>
    shape_step internal LP (\st. b /\ P st) m Q
Proof
  rw[shape_step_def] >> metis_tac[]
QED

Theorem compile_word_copy_loop_shape:
  !src dst nwords loc is_ctor internal.
    (loc = LocStorage \/ loc = LocTransient) ==>
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_word_copy_loop src dst nwords loc LocMemory is_ctor)
      (\x st. T)
Proof
  rpt gen_tac >> disch_tac >>
  simp[compile_word_copy_loop_def] >>
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
  conj_tac
  >- (qx_gen_tac `cond_lbl` >> BETA_TAC >>
      once_rewrite_tac[CONJ_COMM] >> ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
      irule shape_step_bind >>
      qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
      conj_tac
      >- (qx_gen_tac `body_lbl` >> BETA_TAC >>
          once_rewrite_tac[CONJ_COMM] >> ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
          irule shape_step_bind >>
          qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
          conj_tac
          >- (qx_gen_tac `exit_lbl` >> BETA_TAC >>
              once_rewrite_tac[CONJ_COMM] >> ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
              suspend "initialization") >>
          ho_match_mp_tac shape_step_fresh_label >>
          simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      ho_match_mp_tac shape_step_fresh_label >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  ho_match_mp_tac shape_step_fresh_label >>
  simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Resume compile_word_copy_loop_shape[initialization]:
  irule shape_step_bind >>
  qexists_tac `\v st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var v)` >>
  conj_tac
  >- (qx_gen_tac `counter` >> BETA_TAC >>
      irule shape_step_ignore_bind >>
      qexists_tac `\u st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var counter)` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> suspend "init_jump") >>
      ho_match_mp_tac shape_step_emit_inst_guarded >>
      conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def,
           inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
           is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
           is_param_opcode_def, label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  ho_match_mp_tac shape_step_fresh_var >>
  simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Resume compile_word_copy_loop_shape[init_jump]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var counter)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule shape_step_ignore_bind >>
      qexists_tac `\u st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var counter)` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> suspend "condition") >>
      ho_match_mp_tac shape_step_new_block >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, jump_label_ok_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[condition]:
  irule shape_step_bind >>
  qexists_tac `\v st. ((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `done_op` >> BETA_TAC >> suspend "condition_branch") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[condition_branch]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. ((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st done_op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> suspend "body_block") >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def, jump_label_ok_def,
       stackPlanTypesTheory.is_label_operand_def] >>
  rpt strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[body_block]:
  irule shape_step_conseq >>
  qexistsl [`compiler_label`,
            `\st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var counter)`,
            `\x st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var counter)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> suspend "source_offset") >>
  ho_match_mp_tac shape_step_new_block >>
  simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Resume compile_word_copy_loop_shape[source_offset]:
  `word_scale loc = 1` by metis_tac[word_scale_def] >>
  simp[word_scale_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. ((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `src_off` >> BETA_TAC >> suspend "load") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[load]:
  irule shape_step_bind >>
  qexists_tac `\v st. ((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `val_loaded` >> BETA_TAC >> suspend "destination_offset") >>
  ho_match_mp_tac shape_step_frame >>
  conj_tac >- (irule compile_ptr_load_shape >> gvs[]) >>
  simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Resume compile_word_copy_loop_shape[destination_offset]:
  irule shape_step_bind >>
  qexists_tac `\v st. (((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st val_loaded) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `dst_off` >> BETA_TAC >> suspend "store") >>
  irule shape_step_bind >>
  qexists_tac `\v st. (((plain_operand st src /\ plain_operand st dst) /\
                      plain_operand st (Var counter)) /\ plain_operand st val_loaded) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `scaled` >> BETA_TAC >> suspend "destination_add") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[destination_add]:
  irule shape_step_conseq >>
  qexistsl [`compiler_label`,
    `\st. (((plain_operand st src /\ plain_operand st dst) /\
       plain_operand st (Var counter)) /\ plain_operand st val_loaded) /\ plain_operand st scaled`,
    `\v st. ((((plain_operand st src /\ plain_operand st dst) /\
       plain_operand st (Var counter)) /\ plain_operand st val_loaded) /\ plain_operand st scaled) /\ plain_operand st v`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[store]:
  simp[compile_ptr_store_def] >>
  `emit_void MSTORE [dst_off; val_loaded] = emit_inst MSTORE [dst_off; val_loaded] []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  simp[] >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. (((plain_operand st src /\ plain_operand st dst) /\
       plain_operand st (Var counter)) /\ plain_operand st val_loaded) /\ plain_operand st dst_off` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> suspend "increment") >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[increment]:
  irule shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. plain_operand st (Var counter)`, `\x st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st (Var counter) /\ plain_operand st v` >>
  conj_tac
  >- (qx_gen_tac `new_ctr` >> BETA_TAC >> suspend "counter_assign") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[counter_assign]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st (Var counter) /\ plain_operand st new_ctr` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> suspend "back_edge") >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_word_copy_loop_shape[back_edge]:
  irule shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. T`, `\x st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> ho_match_mp_tac shape_step_new_block >>
      simp[shape_stable_def]) >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_param_opcode_def, label_or_plain_def, jump_label_ok_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Finalise compile_word_copy_loop_shape

Theorem compile_ensure_in_memory_shape:
  !loc src_ptr mem_bytes nwords is_ctor internal.
    loc <> LocCode ==>
    shape_step internal compiler_label (\st. plain_operand st src_ptr)
      (compile_ensure_in_memory src_ptr loc mem_bytes nwords is_ctor)
      (\op st. plain_operand st op)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `loc` >>
  gvs[compile_ensure_in_memory_def]
  >- (irule shape_step_return >> simp[])
  >- suspend "slots"
  >- suspend "slots"
  >> suspend "calldata"
QED

Resume compile_ensure_in_memory_shape[slots]:
  markerLib.RESUME_TAC >>
  (irule shape_step_bind >>
   qexists_tac `\b st. plain_operand st src_ptr /\ plain_operand st b.buf_operand` >>
   conj_tac
   >- (qx_gen_tac `buf` >> BETA_TAC >> suspend "slot_copy") >>
   irule shape_step_conseq >>
   qexistsl [`compiler_label`, `\st. plain_operand st src_ptr /\ T`,
             `\b st. plain_operand st src_ptr /\ plain_operand st b.buf_operand`] >>
   conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
   ho_match_mp_tac shape_step_frame >>
   conj_tac >- irule compile_alloc_buffer_shape >>
   simp[shape_stable_def] >> metis_tac[plain_operand_mono])
QED

Resume compile_ensure_in_memory_shape[slot_copy]:
  markerLib.RESUME_TAC >>
  (irule shape_step_ignore_bind >>
   qexists_tac `\x st. plain_operand st buf.buf_operand` >>
   conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
   Cases_on `nwords = 1` >> simp[]
   >- (irule shape_step_bind >>
       qexists_tac `\x st. (plain_operand st src_ptr /\ plain_operand st buf.buf_operand) /\ plain_operand st x` >>
       conj_tac >- (gen_tac >> BETA_TAC >> suspend "single_store") >>
       ho_match_mp_tac shape_step_emit_op_guarded >>
       conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
       simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
            inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
            label_positions_ok_def, is_terminator_def, is_param_opcode_def,
            label_or_plain_def, plain_operand_def] >> metis_tac[]) >>
   irule shape_step_ignore_bind >>
   qexists_tac `\x st. plain_operand st buf.buf_operand` >>
   conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
   simp[compile_storage_to_memory_def, compile_transient_to_memory_def] >>
   suspend "loop_copy")
QED

Resume compile_ensure_in_memory_shape[single_store]:
  markerLib.RESUME_TAC >>
  (pure_rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
   irule shape_step_conseq >>
   qexistsl [`compiler_label`,
     `\st. (plain_operand st src_ptr /\ plain_operand st buf.buf_operand) /\ plain_operand st x`,
     `\u st. (plain_operand st src_ptr /\ plain_operand st buf.buf_operand) /\ plain_operand st x`] >>
   conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
   ho_match_mp_tac shape_step_emit_inst_guarded >>
   conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
   simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, is_param_opcode_def,
        label_or_plain_def, plain_operand_def] >> metis_tac[])
QED

Resume compile_ensure_in_memory_shape[loop_copy]:
  markerLib.RESUME_TAC >>
  (irule shape_step_conseq >>
   qexistsl [`compiler_label`,
     `\st. plain_operand st buf.buf_operand /\ (plain_operand st src_ptr /\ plain_operand st buf.buf_operand)`,
     `\u st. plain_operand st buf.buf_operand /\ T`] >>
   conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
   ho_match_mp_tac shape_step_frame >>
   conj_tac >- (irule compile_word_copy_loop_shape >> simp[]) >>
   simp[shape_stable_def] >> metis_tac[plain_operand_mono])
QED

Resume compile_ensure_in_memory_shape[calldata]:
  irule shape_step_bind >>
  qexists_tac `\x st. plain_operand st src_ptr /\ plain_operand st x` >>
  conj_tac
  >- (qx_gen_tac `len_op` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\b st. (plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st b.buf_operand` >>
      conj_tac >- (qx_gen_tac `buf` >> BETA_TAC >> suspend "cd_store") >>
      irule shape_step_conseq >>
      qexistsl [`compiler_label`,
        `\st. (plain_operand st src_ptr /\ plain_operand st len_op) /\ T`,
        `\b st. (plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st b.buf_operand`] >>
      conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
      ho_match_mp_tac shape_step_frame >>
      conj_tac >- irule compile_alloc_buffer_shape >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def]
QED

Resume compile_ensure_in_memory_shape[cd_store]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. (plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> suspend "cd_adds") >>
  pure_rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def] >> metis_tac[]
QED

Resume compile_ensure_in_memory_shape[cd_adds]:
  irule shape_step_bind >>
  qexists_tac `\x st. ((plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st buf.buf_operand) /\ plain_operand st x` >>
  conj_tac >- (qx_gen_tac `data_ptr` >> BETA_TAC >> suspend "cd_src") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]
QED

Resume compile_ensure_in_memory_shape[cd_src]:
  irule shape_step_bind >>
  qexists_tac `\x st. (((plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st buf.buf_operand) /\ plain_operand st data_ptr) /\ plain_operand st x` >>
  conj_tac >- (qx_gen_tac `src_data` >> BETA_TAC >> suspend "cd_copy") >>
  ho_match_mp_tac shape_step_emit_op_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]
QED

Resume compile_ensure_in_memory_shape[cd_copy]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. (((plain_operand st src_ptr /\ plain_operand st len_op) /\ plain_operand st buf.buf_operand) /\ plain_operand st data_ptr) /\ plain_operand st src_data` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  pure_rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
  ho_match_mp_tac shape_step_emit_inst_guarded >>
  conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def] >> metis_tac[]
QED

Finalise compile_ensure_in_memory_shape

(* Shared helper of every value consumer. *)
Theorem unwrap_value_shape:
  !cenv v internal.
    shape_step internal compiler_label
      (\st. cenv_shape_ok st cenv /\ value_shape_ok st v)
      (unwrap_value cenv v) (\op st. plain_operand st op)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[unwrap_value_def]
  >- (irule shape_step_return >> simp[value_shape_ok_def]) >>
  rename1 `LocatedValue ty p` >>
  Cases_on `p.ptr_location = LocCode`
  >- simp[shape_step_def, value_shape_ok_def] >>
  irule shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. plain_operand st p.ptr_operand`,
            `\op st. plain_operand st op`] >>
  conj_tac >- simp[] >> conj_tac >- simp[value_shape_ok_def] >>
  conj_tac >- simp[] >>
  Cases_on `is_word_type ty` >> simp[]
  >- (irule compile_ptr_load_shape >> simp[]) >>
  Cases_on `p.ptr_location` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  irule compile_ensure_in_memory_shape >> simp[]
QED

(* Ordinary emissions may establish instruction validity from their input. *)
Theorem shape_step_emit_op_pre:
  !internal LP P opc ops.
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
    shape_step internal LP P (emit_op opc ops)
      (\x st. plain_operand st x)
Proof
  rpt strip_tac >> Cases_on `?st. P st`
  >- (pop_assum strip_assume_tac >>
      irule shape_step_conseq >>
      qexistsl_tac [`LP`, `\st. T /\ EVERY (label_or_plain st) ops`,
                    `\x st. T /\ plain_operand st x`] >>
      conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
      conj_tac >- simp[] >>
      irule (BETA_RULE (Q.SPECL [`internal`, `LP`, `\st. T`]
        shape_step_emit_op)) >> simp[shape_stable_def] >> metis_tac[]) >>
  gvs[shape_step_def]
QED

Theorem shape_step_emit_void_pre:
  !internal LP P opc ops.
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> EVERY (label_or_plain st) ops /\
      (!id. lowered_inst_ok internal (mk_inst id opc ops []))) ==>
    shape_step internal LP P (emit_void opc ops) (\x st. T)
Proof
  rpt strip_tac >> Cases_on `?st. P st`
  >- (pop_assum strip_assume_tac >>
      irule shape_step_conseq >>
      qexistsl_tac [`LP`, `\st. T /\ EVERY (label_or_plain st) ops`,
                    `\x st. T`] >>
      conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
      conj_tac >- simp[] >>
      irule (BETA_RULE (Q.SPECL [`internal`, `LP`, `\st. T`]
        shape_step_emit_void)) >> simp[shape_stable_def] >> metis_tac[]) >>
  gvs[shape_step_def]
QED

Theorem compile_nonreentrant_unlock_shape:
  !internal LP nkey use_trans is_view.
    shape_step internal LP (\st. T)
      (compile_nonreentrant_unlock nkey use_trans is_view) (\x st. T)
Proof
  rpt gen_tac >>
  Cases_on `is_view` >> Cases_on `use_trans` >>
  simp[compile_nonreentrant_unlock_def, shape_step_return] >>
  (qmatch_goalsub_abbrev_tac `emit_void opc ops` >>
  irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. T /\ EVERY (label_or_plain st) ops`,
    `\x st. T`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `ops`, label_or_plain_def, plain_operand_def,
                   stackPlanTypesTheory.is_label_operand_def] >>
  conj_tac >- simp[] >>
  irule (BETA_RULE (Q.SPECL [`internal`, `LP`, `\st. T`] shape_step_emit_void)) >>
  simp[Abbr `opc`, Abbr `ops`, shape_stable_def,
       lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       label_positions_ok_def, is_read0_opcode_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, mk_inst_def,
       stackPlanTypesTheory.is_label_operand_def])
QED

Theorem compile_nonreentrant_lock_shape:
  !internal LP nkey use_trans is_view.
    shape_step internal LP (\st. T)
      (compile_nonreentrant_lock nkey use_trans is_view) (\x st. T)
Proof
  let
    val inst_simp = simp[label_or_plain_def, plain_operand_def,
      lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
      label_positions_ok_def, is_read0_opcode_def, inst_jump_labels_ok_def,
      is_terminator_def, is_param_opcode_def, mk_inst_def,
      stackPlanTypesTheory.is_label_operand_def]
  in
    rpt gen_tac >> Cases_on `use_trans` >>
    simp[compile_nonreentrant_lock_def] >>
    (ntac 3
      (irule shape_step_bind >>
       qexists_tac `\x st. plain_operand st x` >>
       reverse conj_tac
       >- (irule shape_step_emit_op_pre >> inst_simp) >>
       gen_tac >> BETA_TAC) >>
     irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
     reverse conj_tac
     >- (irule shape_step_emit_void_pre >> inst_simp) >>
     gen_tac >> BETA_TAC >> Cases_on `is_view` >>
     simp[shape_step_return] >>
     irule shape_step_emit_void_pre >> inst_simp)
  end
QED


(* The cenv a statement body runs under: one more plain PtrVar local when
   ce_alloca_locals is set, the same locals otherwise. *)
Theorem declare_local_shape:
  !internal cenv id ty.
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (declare_local cenv id ty)
      (\cenv' st. cenv_shape_ok st cenv' /\
                  cenv'.ce_return_pc = cenv.ce_return_pc)
Proof
  rpt gen_tac >> simp[declare_local_def] >> IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\x st'. cenv_shape_ok st' cenv /\ plain_operand st' (Var x)` >>
      reverse conj_tac
      >- (mp_tac (Q.SPECL [`internal`, `compiler_label`,
            `\st. cenv_shape_ok st cenv`] shape_step_fresh_var) >>
          simp[cenv_shape_ok_stable]) >>
      gen_tac >> BETA_TAC >> irule shape_step_return >>
      rw[cenv_shape_ok_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      gvs[cenv_shape_ok_def, loc_shape_ok_def] >>
      Cases_on `id = n` >> gvs[loc_shape_ok_def] >> metis_tac[]) >>
  irule shape_step_return >> rw[cenv_shape_ok_def] >> gvs[cenv_shape_ok_def] >>
  res_tac
QED

Theorem declare_stmt_local_shape:
  !internal cenv s.
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (declare_stmt_local cenv s)
      (\cenv' st. cenv_shape_ok st cenv' /\
                  cenv'.ce_return_pc = cenv.ce_return_pc)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, declare_local_shape] >>
  rpt gen_tac >> irule shape_step_return >> simp[]
QED

Theorem infer_array_location_not_code[local]:
  !st cenv e. cenv_shape_ok st cenv ==>
    infer_array_location cenv e <> LocCode
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >>
  gvs[infer_array_location_def, cenv_shape_ok_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
  gvs[loc_shape_ok_def] >> metis_tac[loc_shape_ok_def]
QED

Theorem value_shape_ok_operand[local]:
  !st vv. value_shape_ok st vv ==> plain_operand st (vv_operand vv)
Proof
  Cases_on `vv` >> simp[value_shape_ok_def, vv_operand_def]
QED

Theorem cenv_shape_ok_lookup[local]:
  !st cenv n loc. cenv_shape_ok st cenv /\
    FLOOKUP cenv.ce_vars n = SOME loc ==> loc_shape_ok st loc
Proof
  rw[cenv_shape_ok_def] >> metis_tac[]
QED

Theorem emit_local_alloca_shape[local]:
  !internal cenv id.
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (emit_local_alloca cenv id) (\x st. cenv_shape_ok st cenv)
Proof
  rpt gen_tac >> simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  rename1 `PtrVar op sz` >> Cases_on `op` >> simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  mp_tac (Q.SPECL [`internal`, `compiler_label`, `\st. cenv_shape_ok st cenv`,
    `ALLOCA`, `[Lit (n2w sz)]`, `[s]`] shape_step_emit_inst) >>
  simp[cenv_shape_ok_stable, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def, mk_inst_def,
       raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_read0_opcode_def, label_positions_ok_def,
       is_param_opcode_def]
QED

Theorem emit_jmp_if_not_terminated_shape[local]:
  !internal lbl. jump_label_ok lbl ==>
    shape_step internal compiler_label (\st. T)
      (emit_jmp_if_not_terminated lbl) (\x st. T)
Proof
  rpt strip_tac >> simp[emit_jmp_if_not_terminated_def] >>
  irule shape_step_bind >> qexists_tac `\cs st. T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_return >> simp[]) >>
      mp_tac (Q.SPECL [`internal`, `compiler_label`, `\st. T`,
        `JMP`, `[Label lbl]`, `[]`] shape_step_emit_inst) >>
      simp[shape_stable_def, label_or_plain_def,
           stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
           mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
           inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
           label_positions_ok_def, is_param_opcode_def]) >>
  simp[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem stmt_shape_emit_op[local]:
  !internal P opc ops.
    shape_stable P /\
    (!st. P st ==> EVERY (label_or_plain st) ops) /\
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> !id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal compiler_label P (emit_op opc ops)
      (\x st. P st /\ plain_operand st x)
Proof
  rpt strip_tac >> rewrite_tac[shape_step_def] >> rpt strip_tac >>
  `!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)` by metis_tac[] >>
  `shape_step internal compiler_label
     (\st. P st /\ EVERY (label_or_plain st) ops) (emit_op opc ops)
     (\x st. P st /\ plain_operand st x)` by
    (irule shape_step_emit_op >> simp[]) >>
  `EVERY (label_or_plain st) ops` by metis_tac[] >>
  fs[shape_step_def] >> metis_tac[]
QED

Theorem stmt_shape_emit_inst[local]:
  !internal P opc ops outs.
    shape_stable P /\
    (!st. P st ==> EVERY (label_or_plain st) ops) /\
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> !id. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal compiler_label P (emit_inst opc ops outs)
      (\x st. P st)
Proof
  rpt strip_tac >> rewrite_tac[shape_step_def] >> rpt strip_tac >>
  `!id. lowered_inst_ok internal (mk_inst id opc ops outs)` by metis_tac[] >>
  `shape_step internal compiler_label
     (\st. P st /\ EVERY (label_or_plain st) ops) (emit_inst opc ops outs)
     (\x st. P st)` by
    (irule shape_step_emit_inst >> simp[]) >>
  `EVERY (label_or_plain st) ops` by metis_tac[] >>
  fs[shape_step_def] >> metis_tac[]
QED

Theorem stmt_shape_emit_void[local]:
  !internal P opc ops.
    shape_stable P /\
    (!st. P st ==> EVERY (label_or_plain st) ops) /\
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st. P st ==> !id. lowered_inst_ok internal (mk_inst id opc ops [])) ==>
    shape_step internal compiler_label P (emit_void opc ops)
      (\x st. P st)
Proof
  rpt strip_tac >>
  `emit_void opc ops = emit_inst opc ops []` by
    simp[emit_void_def, emit_inst_def] >>
  asm_rewrite_tac[] >> irule stmt_shape_emit_inst >> metis_tac[]
QED

Theorem stmt_shape_stable_plain[local]:
  !op. shape_stable (\st. plain_operand st op)
Proof
  gen_tac >> mp_tac (Q.SPEC `[op]` shape_stable_plain_operands) >> simp[]
QED

val stmt_shape_emit_simp = simp[
  lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
  inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
  label_positions_ok_def, is_param_opcode_def];

Theorem compile_with_byte_offset_shape[local]:
  !internal base offset.
    shape_step internal compiler_label (\st. plain_operand st base)
      (compile_with_byte_offset base offset)
      (\op st. plain_operand st op)
Proof
  map_every qx_gen_tac [`internal`, `base_op`, `off`] >>
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. plain_operand st base_op`,
               `\op st. plain_operand st base_op /\ plain_operand st op`] >>
  simp[] >> ho_match_mp_tac stmt_shape_emit_op >>
  simp[stmt_shape_stable_plain] >> conj_tac
  >- (simp[label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem stmt_shape_frame[local]:
  !internal A m B R P.
    shape_step internal compiler_label A m B /\ shape_stable R /\
    (!st. P st ==> A st /\ R st) ==>
    shape_step internal compiler_label P m (\x st. B x st /\ R st)
Proof
  rpt strip_tac >> drule_all shape_step_frame >>
  strip_tac >> irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. R st /\ A st`,
               `\x st. R st /\ B x st`] >> simp[] >> metis_tac[]
QED

val stmt_plain_emit =
  qmatch_goalsub_abbrev_tac `shape_step _ _ pre _ _` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `pre`,
               `\x st. pre st /\ plain_operand st x`] >>
  simp[] >> ho_match_mp_tac stmt_shape_emit_op >>
  simp[Abbr `pre`, stmt_shape_stable_plain, shape_stable_conj] >>
  conj_tac
  >- simp[label_or_plain_def, plain_operand_def,
          stackPlanTypesTheory.is_label_operand_def] >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def];

Theorem compile_bytestring_copy_len_shape[local]:
  !internal val_op.
    shape_step internal compiler_label (\st. plain_operand st val_op)
      (compile_bytestring_copy_len val_op) (\op st. plain_operand st op)
Proof
  rpt gen_tac >> simp[compile_bytestring_copy_len_def] >>
  irule shape_step_bind >> qexists_tac `\op st. plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\op st. plain_operand st op` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\op st. plain_operand st op` >> conj_tac
          >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
          stmt_plain_emit) >>
      stmt_plain_emit) >>
  stmt_plain_emit
QED


Theorem compile_copy_memory_dynamic_shape[local]:
  !internal dst src len.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len)
      (compile_copy_memory_dynamic dst src len) (\x st. T)
Proof
  rpt gen_tac >> simp[compile_copy_memory_dynamic_def] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len`,
    `\x st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len`] >>
  simp[] >> ho_match_mp_tac stmt_shape_emit_void >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >> conj_tac
  >- simp[label_or_plain_def, plain_operand_def,
          stackPlanTypesTheory.is_label_operand_def] >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_copy_memory_shape[local]:
  !internal dst src n.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_copy_memory dst src n) (\x st. T)
Proof
  rpt gen_tac >> Cases_on `n` >> simp[compile_copy_memory_def]
  >- (irule shape_step_return >> simp[]) >>
  rewrite_tac[GSYM compile_copy_memory_dynamic_def] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st dst /\ plain_operand st src /\
           plain_operand st (Lit (n2w (SUC n')) )`, `\x st. T`] >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       compile_copy_memory_dynamic_shape]
QED

Theorem compile_store_bytestring_shape[local]:
  !internal src dst.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_store_bytestring src dst) (\x st. T)
Proof
  rpt gen_tac >> simp[compile_store_bytestring_def] >>
  irule shape_step_bind >>
  qexists_tac `\len st. plain_operand st len /\
                           (plain_operand st src /\ plain_operand st dst)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >>
      rewrite_tac[GSYM compile_copy_memory_dynamic_def] >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st x`,
        `\x st. T`] >> simp[compile_copy_memory_dynamic_shape]) >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st src` >>
  simp[compile_bytestring_copy_len_shape, shape_stable_conj, stmt_shape_stable_plain]
QED

val stmt_plain_void =
  ho_match_mp_tac stmt_shape_emit_void >>
  simp[stmt_shape_stable_plain, shape_stable_conj, label_or_plain_def] >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def];

Theorem compile_store_byte_chunks_shape[local]:
  !data_ptr bs off internal.
    shape_step internal compiler_label (\st. plain_operand st data_ptr)
      (compile_store_byte_chunks data_ptr bs off) (\x st. plain_operand st data_ptr)
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >>
  fs[] >> simp[Once compile_store_byte_chunks_def]
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_bind >>
  qexists_tac `\dst st. plain_operand st data_ptr /\ plain_operand st dst` >>
  conj_tac
  >- (qx_gen_tac `dst_op` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\x st. plain_operand st data_ptr /\ plain_operand st dst_op` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. plain_operand st data_ptr`,
                       `\x st. plain_operand st data_ptr`] >> simp[]) >>
      stmt_plain_void) >>
  ho_match_mp_tac stmt_shape_emit_op >>
  simp[stmt_shape_stable_plain] >> conj_tac
  >- simp[label_or_plain_def, plain_operand_def,
          stackPlanTypesTheory.is_label_operand_def] >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_bytelike_literal_shape[local]:
  !internal bs max_len.
    shape_step internal compiler_label (\st. T)
      (compile_bytelike_literal bs max_len)
      (\buf st. plain_operand st buf.buf_operand)
Proof
  rpt gen_tac >> simp[compile_bytelike_literal_def] >>
  irule shape_step_bind >>
  qexists_tac `\buf st. plain_operand st buf.buf_operand` >> conj_tac
  >- (qx_gen_tac `buf` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\x st. plain_operand st buf.buf_operand` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
          qexists_tac `\x st. plain_operand st buf.buf_operand` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          irule compile_store_byte_chunks_shape) >>
      stmt_plain_void) >>
  irule compile_alloc_buffer_shape
QED


Theorem compile_ptr_store_shape[local]:
  !internal is_ctor loc dst v.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st v)
      (compile_ptr_store is_ctor loc dst v) (\x st. T)
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ptr_store_def] >>
  TRY (IF_CASES_TAC) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st dst /\ plain_operand st v`,
    `\x st. plain_operand st dst /\ plain_operand st v`] >>
  simp[] >> stmt_plain_void
QED

Theorem stmt_shape_stable_const[local]:
  !b. shape_stable (\st. b)
Proof
  simp[shape_stable_def]
QED

Theorem stmt_shape_new_block[local]:
  !internal P lbl.
    shape_stable P /\ (!st. P st ==> compiler_label lbl) ==>
    shape_step internal compiler_label P (new_block lbl) (\x st. P st)
Proof
  rpt strip_tac >> rewrite_tac[shape_step_def] >> rpt strip_tac >>
  `compiler_label lbl` by metis_tac[] >>
  `shape_step internal compiler_label P (new_block lbl) (\x st. P st)` by
    (irule shape_step_new_block >> simp[]) >>
  fs[shape_step_def] >> metis_tac[]
QED

Theorem stmt_word_offset_shape[local]:
  !internal base_op ctr scale.
    shape_step internal compiler_label
      (\st. plain_operand st base_op /\ plain_operand st (Var ctr))
      (if scale = 1 then emit_op ADD [base_op; Var ctr]
       else do scaled <- emit_op MUL [Var ctr; Lit (n2w scale)];
               emit_op ADD [base_op; scaled] od)
      (\x st. plain_operand st x)
Proof
  rpt gen_tac >> IF_CASES_TAC
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st base_op /\ plain_operand st (Var ctr)`,
        `\x st. (plain_operand st base_op /\ plain_operand st (Var ctr)) /\
                 plain_operand st x`] >> simp[] >>
      ho_match_mp_tac stmt_shape_emit_op >>
      simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
      stmt_shape_emit_simp >>
      simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  irule shape_step_bind >>
  qexists_tac `\x st. plain_operand st x /\ plain_operand st base_op` >> conj_tac
  >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st (Var ctr)` >>
  simp[stmt_shape_stable_plain] >> stmt_plain_emit
QED


Theorem wrap_truncate_shape[local]:
  !internal res ty.
    shape_step internal compiler_label (\st. plain_operand st res)
      (wrap_truncate res ty) (\x st. plain_operand st x)
Proof
  rpt gen_tac >> simp[wrap_truncate_def] >> IF_CASES_TAC
  >- (IF_CASES_TAC >> stmt_plain_emit) >>
  irule shape_step_return >> simp[]
QED

Theorem compile_compare_shape[local]:
  !internal op x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_compare op x y ty) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> Cases_on `op` >> simp[compile_compare_def] >>
  TRY (IF_CASES_TAC) >> FIRST [
    stmt_plain_emit >> NO_TAC,
    (irule shape_step_bind >> qexists_tac `\x st. plain_operand st x` >>
     conj_tac
     >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit) >> NO_TAC,
    (irule shape_step_ignore_bind >>
     qexists_tac `\u st. plain_operand st x /\ plain_operand st y` >>
     conj_tac
     >- (gen_tac >> BETA_TAC >> irule shape_step_return >>
         simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
     ho_match_mp_tac stmt_shape_emit_inst >>
     simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp)]
QED

Theorem compile_select_shape[local]:
  !internal cond_op then_op else_op.
    shape_step internal compiler_label
      (\st. plain_operand st cond_op /\ plain_operand st then_op /\
            plain_operand st else_op)
      (compile_select cond_op then_op else_op) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_select_def] >> irule shape_step_bind >>
  qexists_tac `\diff st. plain_operand st diff /\
                         (plain_operand st cond_op /\ plain_operand st else_op)` >>
  conj_tac
  >- (qx_gen_tac `diff` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\scaled st. plain_operand st scaled /\ plain_operand st else_op` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st cond_op /\ plain_operand st diff` >>
      simp[stmt_shape_stable_plain] >> stmt_plain_emit) >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st then_op /\ plain_operand st else_op` >>
  simp[stmt_shape_stable_plain, shape_stable_conj] >> stmt_plain_emit
QED

fun stmt_drop preserving_tac =
  qmatch_goalsub_abbrev_tac `shape_step _ _ pre _ _` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `pre`, `\x st. pre st`] >>
  simp[Abbr `pre`] >> preserving_tac;
val stmt_plain_void_drop = stmt_drop stmt_plain_void;
fun stmt_frame_emit input =
  ho_match_mp_tac stmt_shape_frame >> qexists_tac input >>
  simp[stmt_shape_stable_plain, shape_stable_conj] >> stmt_plain_emit;

Theorem compile_clamp_shape[local]:
  !internal val_op ty.
    shape_step internal compiler_label (\st. plain_operand st val_op)
      (compile_clamp val_op ty) (\x st. T)
Proof
  rpt gen_tac >> simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ plain_operand st val_op` >>
      conj_tac
      >- (qx_gen_tac `slt_lo` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\ plain_operand st val_op` >>
          conj_tac
          >- (qx_gen_tac `ge_lo` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\ plain_operand st ge_lo` >>
              conj_tac
              >- (qx_gen_tac `sgt_hi` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a /\ plain_operand st ge_lo` >>
                  conj_tac
                  >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
                      qexists_tac `\a st. plain_operand st a` >> conj_tac
                      >- (gen_tac >> BETA_TAC >> stmt_plain_void_drop) >>
                      stmt_plain_emit) >>
                  stmt_frame_emit `\st. plain_operand st sgt_hi`) >>
              stmt_frame_emit `\st. plain_operand st val_op`) >>
          stmt_frame_emit `\st. plain_operand st slt_lo`) >>
      stmt_frame_emit `\st. plain_operand st val_op`) >>
  irule shape_step_bind >> qexists_tac `\a st. plain_operand st a` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a` >> conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_plain_void_drop) >> stmt_plain_emit) >>
  stmt_plain_emit
QED

Theorem clamp_and_return_shape[local]:
  !internal res ty.
    shape_step internal compiler_label (\st. plain_operand st res)
      (clamp_and_return res ty) (\x st. plain_operand st x)
Proof
  rpt gen_tac >> simp[clamp_and_return_def] >> irule shape_step_ignore_bind >>
  qexists_tac `\x st. T /\ plain_operand st res` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st res` >>
  simp[compile_clamp_shape, stmt_shape_stable_plain]
QED

Theorem stmt_nonzero_then_shape[local]:
  !internal P y m Q.
    shape_stable P /\ (!st. P st ==> plain_operand st y) /\
    shape_step internal compiler_label P m Q ==>
    shape_step internal compiler_label P
      (do z <- emit_op ISZERO [y];
          nz <- emit_op ISZERO [z];
          emit_void ASSERT [nz]; m od) Q
Proof
  rpt strip_tac >> irule shape_step_bind >>
  qexists_tac `\z st. plain_operand st z /\ P st` >> conj_tac
  >- (qx_gen_tac `zero_op` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\z st. plain_operand st z /\ P st` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
          qexists_tac `\u st. P st` >> conj_tac
          >- (gen_tac >> BETA_TAC >> simp[ETA_THM]) >>
          stmt_plain_void_drop) >>
      stmt_frame_emit `\st. plain_operand st zero_op`) >>
  stmt_frame_emit `\st. plain_operand st y`
QED

Theorem compile_safe_mod_shape[local]:
  !internal x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_mod x y ty) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[compile_safe_mod_def] >>
  ho_match_mp_tac stmt_nonzero_then_shape >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >>
  IF_CASES_TAC >> stmt_plain_emit
QED

Theorem compile_safe_decimal_div_shape[local]:
  !internal x y divisor ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_decimal_div x y divisor ty) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[compile_safe_decimal_div_def] >> irule shape_step_bind >>
  qexists_tac `\z st. plain_operand st z /\ plain_operand st y` >> conj_tac
  >- (qx_gen_tac `scaled` >> BETA_TAC >>
      ho_match_mp_tac stmt_nonzero_then_shape >>
      simp[shape_stable_conj, stmt_shape_stable_plain] >>
      irule shape_step_bind >> qexists_tac `\z st. plain_operand st z` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule clamp_and_return_shape) >>
      stmt_plain_emit) >>
  stmt_frame_emit `\st. plain_operand st x`
QED

Theorem compile_safe_div_shape[local]:
  !internal x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_div x y ty) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[compile_safe_div_def] >>
  ho_match_mp_tac stmt_nonzero_then_shape >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >>
  reverse IF_CASES_TAC >- stmt_plain_emit >>
  irule shape_step_bind >>
  qexists_tac `\res st. plain_operand st res /\
                           (plain_operand st x /\ plain_operand st y)` >>
  conj_tac
  >- (qx_gen_tac `res` >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\
                             (plain_operand st y /\ plain_operand st res)` >>
          conj_tac
          >- (qx_gen_tac `x_min` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\
                                 (plain_operand st x_min /\ plain_operand st res)` >>
              conj_tac
              >- (qx_gen_tac `ny` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a /\
                                     (plain_operand st x_min /\ plain_operand st res)` >>
                  conj_tac
                  >- (qx_gen_tac `y_neg1` >> BETA_TAC >> irule shape_step_bind >>
                      qexists_tac `\a st. plain_operand st a /\ plain_operand st res` >>
                      conj_tac
                      >- (qx_gen_tac `bad` >> BETA_TAC >> irule shape_step_bind >>
                          qexists_tac `\a st. plain_operand st a /\ plain_operand st res` >>
                          conj_tac
                          >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
                              qexists_tac `\u st. plain_operand st res` >> conj_tac
                              >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
                              stmt_plain_void_drop) >>
                          stmt_frame_emit `\st. plain_operand st bad`) >>
                      stmt_frame_emit `\st. plain_operand st x_min /\ plain_operand st y_neg1`) >>
                  stmt_frame_emit `\st. plain_operand st ny`) >>
              stmt_frame_emit `\st. plain_operand st y`) >>
          stmt_frame_emit `\st. plain_operand st x`) >>
      IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. plain_operand st res`, `\z st. plain_operand st z`] >>
          simp[clamp_and_return_shape]) >>
      irule shape_step_return >> simp[]) >>
  stmt_frame_emit `\st. plain_operand st x /\ plain_operand st y`
QED

Theorem compile_safe_add_sub_shape[local]:
  (!internal x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_add x y ty) (\z st. plain_operand st z)) /\
  (!internal x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_sub x y ty) (\z st. plain_operand st z))
Proof
  conj_tac >> (rpt gen_tac >>
  simp[compile_safe_add_def, compile_safe_sub_def] >> irule shape_step_bind >>
  qexists_tac `\res st. plain_operand st res /\
                         (plain_operand st x /\ plain_operand st y)` >> conj_tac
  >- (qx_gen_tac `res` >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. plain_operand st res`, `\z st. plain_operand st z`] >>
          simp[clamp_and_return_shape]) >>
      IF_CASES_TAC
      >- (irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\
                             (plain_operand st res /\ plain_operand st x)` >> conj_tac
          >- (qx_gen_tac `neg_op` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\
                                 (plain_operand st neg_op /\ plain_operand st res)` >> conj_tac
              >- (qx_gen_tac `cmp` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a /\ plain_operand st res` >> conj_tac
                  >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
                      qexists_tac `\u st. plain_operand st res` >> conj_tac
                      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
                      stmt_plain_void_drop) >>
                  stmt_frame_emit `\st. plain_operand st neg_op /\ plain_operand st cmp`) >>
              stmt_frame_emit `\st. plain_operand st res /\ plain_operand st x`) >>
          stmt_frame_emit `\st. plain_operand st y`) >>
      irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ plain_operand st res` >> conj_tac
      >- (qx_gen_tac `cmp` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\ plain_operand st res` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
              qexists_tac `\u st. plain_operand st res` >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
              stmt_plain_void_drop) >>
          stmt_frame_emit `\st. plain_operand st cmp`) >>
      stmt_frame_emit `\st. plain_operand st res /\ plain_operand st x`) >>
  stmt_frame_emit `\st. plain_operand st x /\ plain_operand st y`)
QED

Theorem stmt_checked_then_shape[local]:
  !internal P check m Q.
    shape_stable P /\
    shape_step internal compiler_label P check (\z st. plain_operand st z) /\
    shape_step internal compiler_label P m Q ==>
    shape_step internal compiler_label P
      (do ok <- check; emit_void ASSERT [ok]; m od) Q
Proof
  rpt strip_tac >> irule shape_step_bind >>
  qexists_tac `\z st. plain_operand st z /\ P st` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\u st. P st` >> conj_tac
      >- (gen_tac >> BETA_TAC >> simp[ETA_THM]) >> stmt_plain_void_drop) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `P` >> simp[]
QED

Theorem compile_safe_pow_shape:
  !internal x y ty base_literal exp_literal.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_pow x y ty base_literal exp_literal)
      (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[compile_safe_pow_def] >>
  Cases_on `base_literal`
  >- (Cases_on `exp_literal` >> simp[]
      >- (irule shape_step_bind >>
          qexists_tac `\z st. plain_operand st z` >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              rewrite_tac[GSYM clamp_and_return_def] >> irule clamp_and_return_shape) >> stmt_plain_emit) >>
      IF_CASES_TAC
      >- (irule shape_step_ignore_bind >>
          qexists_tac `\u st. plain_operand st x /\ plain_operand st y` >> conj_tac
          >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_void_drop) >>
      IF_CASES_TAC
      >- suspend "signed_exponent" >>
      suspend "upper_bound") >>
  simp[] >> IF_CASES_TAC
  >- suspend "small_base" >>
  suspend "upper_bound"
QED

Resume compile_safe_pow_shape[signed_exponent]:
  irule shape_step_bind >>
  qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
  conj_tac
  >- (qx_gen_tac `below` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
      conj_tac
      >- (qx_gen_tac `ge` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\
                             (plain_operand st ge /\ (plain_operand st x /\ plain_operand st y))` >>
          conj_tac
          >- (qx_gen_tac `above` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\
                                 (plain_operand st ge /\ (plain_operand st x /\ plain_operand st y))` >>
              conj_tac
              >- (qx_gen_tac `le` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a /\
                                     (plain_operand st x /\ plain_operand st y)` >>
                  conj_tac
                  >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
                      qexists_tac `\u st. plain_operand st x /\ plain_operand st y` >> conj_tac
                      >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_void_drop) >>
                  stmt_frame_emit `\st. plain_operand st ge /\ plain_operand st le`) >>
              stmt_frame_emit `\st. plain_operand st above`) >>
          stmt_frame_emit `\st. plain_operand st x`) >>
      stmt_frame_emit `\st. plain_operand st below`) >>
  stmt_frame_emit `\st. plain_operand st x`
QED
Resume compile_safe_pow_shape[upper_bound]:
  markerLib.RESUME_TAC >> (irule shape_step_bind >>
  qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
  conj_tac
  >- (qx_gen_tac `above` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
          qexists_tac `\u st. plain_operand st x /\ plain_operand st y` >> conj_tac
          >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_void_drop) >>
      stmt_frame_emit `\st. plain_operand st above`) >>
  ho_match_mp_tac stmt_shape_frame >>
  qmatch_goalsub_abbrev_tac `emit_op GT [bound_op; _]` >>
  qexists_tac `\st. plain_operand st bound_op` >>
  simp[stmt_shape_stable_plain, shape_stable_conj, Abbr `bound_op`] >> stmt_plain_emit)
QED
Resume compile_safe_pow_shape[small_base]:
  ho_match_mp_tac stmt_checked_then_shape >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >> reverse conj_tac
  >- stmt_plain_emit >> IF_CASES_TAC
  >- (irule shape_step_bind >> qexists_tac `\a st. plain_operand st a` >> conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit) >>
  irule shape_step_return >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Finalise compile_safe_pow_shape[local]

Theorem compile_mul_overflow_check_shape:
  !internal x y res signed bits.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y /\ plain_operand st res)
      (compile_mul_overflow_check x y res signed bits) (\u st. T)
Proof
  rpt gen_tac >> simp[compile_mul_overflow_check_def] >>
  irule shape_step_bind >>
  qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
  conj_tac
  >- (qx_gen_tac `div_res` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
      conj_tac
      >- (qx_gen_tac `div_ok` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\
                             (plain_operand st div_ok /\ (plain_operand st x /\ plain_operand st y))` >>
          conj_tac
          >- (qx_gen_tac `y_zero` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
              conj_tac
              >- (qx_gen_tac `ok_op` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a` >> conj_tac
                  >- (gen_tac >> BETA_TAC >> stmt_plain_void_drop) >>
                  IF_CASES_TAC >- suspend "special" >> irule shape_step_return >> simp[]) >>
              stmt_frame_emit `\st. plain_operand st div_ok /\ plain_operand st y_zero`) >>
          stmt_frame_emit `\st. plain_operand st y`) >>
      stmt_frame_emit `\st. plain_operand st div_res /\ plain_operand st x`) >>
  IF_CASES_TAC >> stmt_frame_emit `\st. plain_operand st res /\ plain_operand st y`
QED
Resume compile_mul_overflow_check_shape[special]:
  irule shape_step_bind >>
  qexists_tac `\a st. plain_operand st a /\ (plain_operand st y /\ plain_operand st ok_op)` >>
  conj_tac
  >- (qx_gen_tac `x_min` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ (plain_operand st x_min /\ plain_operand st ok_op)` >>
      conj_tac
      >- (qx_gen_tac `ny` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\a st. plain_operand st a /\ (plain_operand st x_min /\ plain_operand st ok_op)` >>
          conj_tac
          >- (qx_gen_tac `y_neg1` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\a st. plain_operand st a /\ plain_operand st ok_op` >> conj_tac
              >- (qx_gen_tac `special` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\a st. plain_operand st a /\ plain_operand st ok_op` >> conj_tac
                  >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
                  stmt_frame_emit `\st. plain_operand st special`) >>
              stmt_frame_emit `\st. plain_operand st x_min /\ plain_operand st y_neg1`) >>
          stmt_frame_emit `\st. plain_operand st ny`) >>
      stmt_frame_emit `\st. plain_operand st y`) >>
  stmt_frame_emit `\st. plain_operand st x`
QED
Finalise compile_mul_overflow_check_shape[local]

Theorem compile_safe_mul_shape[local]:
  !internal x y ty.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_safe_mul x y ty) (\z st. plain_operand st z)
Proof
  rpt gen_tac >> simp[compile_safe_mul_def] >> irule shape_step_bind >>
  qexists_tac `\res st. plain_operand st res /\
                         (plain_operand st x /\ plain_operand st y)` >> conj_tac
  >- (qx_gen_tac `res` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\u st. plain_operand st res` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\z st. plain_operand st z` >> conj_tac
          >- (qx_gen_tac `res1` >> BETA_TAC >> IF_CASES_TAC
              >- irule clamp_and_return_shape >> irule shape_step_return >> simp[]) >>
          IF_CASES_TAC
          >- (IF_CASES_TAC >> stmt_plain_emit) >> irule shape_step_return >> simp[]) >>
      IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. plain_operand st res /\ (plain_operand st x /\ plain_operand st y)`,
            `\u st. T /\ plain_operand st res`] >> reverse (rpt conj_tac)
          >- (ho_match_mp_tac stmt_shape_frame >>
              qexists_tac `\st. plain_operand st x /\ plain_operand st y /\ plain_operand st res` >>
              simp[compile_mul_overflow_check_shape, stmt_shape_stable_plain]) >> simp[]) >>
      irule shape_step_return >> simp[]) >>
  stmt_frame_emit `\st. plain_operand st x /\ plain_operand st y`
QED

Theorem compile_binop_shape[local]:
  !internal op x y ty base_literal exp_literal.
    shape_step internal compiler_label
      (\st. plain_operand st x /\ plain_operand st y)
      (compile_binop op x y ty base_literal exp_literal)
      (\z st. plain_operand st z)
Proof
  rpt gen_tac >> Cases_on `op` >>
  (simp[compile_binop_def, compile_safe_add_sub_shape, compile_safe_mul_shape,
        compile_safe_div_shape, compile_safe_decimal_div_shape,
        compile_safe_mod_shape, compile_safe_pow_shape, compile_compare_shape] >>
   FIRST [
     stmt_plain_emit >> NO_TAC,
     (rename1 `shape_step _ _ _ (if is_decimal_type ty then _ else _) _` >>
      IF_CASES_TAC >> simp[compile_safe_div_shape, compile_safe_decimal_div_shape]) >> NO_TAC,
     (rename1 `emit_op SAR [y; x]` >> IF_CASES_TAC >> stmt_plain_emit) >> NO_TAC,
     (rename1 `wrap_truncate` >>
      irule shape_step_bind >> qexists_tac `\a st. plain_operand st a` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule wrap_truncate_shape) >>
      TRY (IF_CASES_TAC) >> stmt_plain_emit) >> NO_TAC,
     (rename1 `compile_select` >> irule shape_step_bind >>
      qexists_tac `\a st. plain_operand st a /\ (plain_operand st x /\ plain_operand st y)` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule compile_select_shape) >>
      IF_CASES_TAC >> stmt_frame_emit `\st. plain_operand st x /\ plain_operand st y`) >> NO_TAC,
     (rename1 `emit_op ISZERO` >>
      irule shape_step_bind >> qexists_tac `\a st. plain_operand st a` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          FIRST [stmt_plain_emit >> NO_TAC,
            irule shape_step_bind >> qexists_tac `\a st. plain_operand st a` >> conj_tac
            >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit]) >>
      stmt_plain_emit) >> NO_TAC,
     (irule shape_step_ignore_bind >>
      qexists_tac `\u st. plain_operand st x /\ plain_operand st y` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >>
          simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
      ho_match_mp_tac stmt_shape_emit_inst >>
      simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
      stmt_shape_emit_simp)])
QED

Theorem stmt_shape_jmp[local]:
  !internal P lbl.
    shape_stable P /\ (!st. P st ==> compiler_label lbl) ==>
    shape_step internal compiler_label P (emit_inst JMP [Label lbl] [])
      (\u st. P st)
Proof
  rpt strip_tac >> ho_match_mp_tac stmt_shape_emit_inst >> simp[] >>
  conj_tac
  >- simp[label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >>
  stmt_shape_emit_simp >> simp[jump_label_ok_def] >> metis_tac[]
QED

Theorem stmt_shape_jnz[local]:
  !internal P test yes no.
    shape_stable P /\
    (!st. P st ==> plain_operand st test /\ compiler_label yes /\ compiler_label no) ==>
    shape_step internal compiler_label P
      (emit_inst JNZ [test; Label yes; Label no] []) (\u st. P st)
Proof
  rpt strip_tac >> ho_match_mp_tac stmt_shape_emit_inst >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[label_or_plain_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_shape_emit_simp >>
  rpt strip_tac >> first_x_assum drule >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def, jump_label_ok_def] >>
  strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

fun stmt_sequence pre first_step =
  irule shape_step_ignore_bind >> qexists_tac pre >>
  reverse conj_tac >- first_step >> gen_tac >> BETA_TAC;

Theorem compile_word_copy_loop_noncode_shape:
  !internal src dst n load_loc store_loc is_ctor.
    load_loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_word_copy_loop src dst n load_loc store_loc is_ctor) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_word_copy_loop_def] >>
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
  conj_tac
  >- (qx_gen_tac `cond_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label cond_lbl`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >>
      qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
      conj_tac
      >- (qx_gen_tac `body_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label body_lbl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >>
          qexists_tac `\l st. (plain_operand st src /\ plain_operand st dst) /\ compiler_label l` >>
          conj_tac
          >- (qx_gen_tac `exit_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label exit_lbl`)
              >- simp[shape_step_def] >> simp[] >>
              irule shape_step_bind >>
              qexists_tac `\ctr st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr)` >>
              conj_tac >- suspend "loop" >>
              ho_match_mp_tac shape_step_fresh_var >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
          ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_word_copy_loop_noncode_shape[loop]:
  qx_gen_tac `ctr` >> BETA_TAC >>
  qabbrev_tac `wcopy_live = \st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr)` >>
  stmt_sequence `\u st. wcopy_live st`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >> suspend "initial_assign") >>
  stmt_sequence `\u st. wcopy_live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. wcopy_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\test st. plain_operand st test /\ wcopy_live st` >>
  conj_tac
  >- (qx_gen_tac `done_op` >> BETA_TAC >>
      stmt_sequence `\u st. wcopy_live st`
        (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
         simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain])) >>
      stmt_sequence `\u st. wcopy_live st`
        (ho_match_mp_tac stmt_shape_new_block >>
         simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
      simp[Abbr `wcopy_live`] >> suspend "copy") >>
  simp[Abbr `wcopy_live`] >> stmt_frame_emit `\st. plain_operand st (Var ctr)`
QED
Resume compile_word_copy_loop_noncode_shape[initial_assign]:
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_word_copy_loop_noncode_shape[copy]:
  qabbrev_tac `wcopy_live = \st. (plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr)` >>
  irule shape_step_bind >>
  qexists_tac `\off st. plain_operand st off /\ wcopy_live st` >> conj_tac
  >- (qx_gen_tac `src_off` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\loaded st. plain_operand st loaded /\ (plain_operand st dst /\ plain_operand st (Var ctr))` >> conj_tac
      >- suspend "destination" >>
      ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st src_off` >>
      simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain, compile_ptr_load_shape]) >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st src /\ plain_operand st (Var ctr)` >>
  simp[Abbr `wcopy_live`, shape_stable_conj, stmt_shape_stable_plain, stmt_word_offset_shape]
QED
Resume compile_word_copy_loop_noncode_shape[destination]:
  qx_gen_tac `loaded` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\off st. plain_operand st off /\ (plain_operand st loaded /\ plain_operand st (Var ctr))` >> conj_tac
  >- suspend "store" >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st dst /\ plain_operand st (Var ctr)` >>
  simp[shape_stable_conj, stmt_shape_stable_plain, stmt_word_offset_shape]
QED
Resume compile_word_copy_loop_noncode_shape[store]:
  qx_gen_tac `dst_off` >> BETA_TAC >>
  stmt_sequence `\u st. T /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st dst_off /\ plain_operand st loaded` >>
     simp[stmt_shape_stable_plain, compile_ptr_store_shape]) >>
  simp[] >> irule shape_step_bind >>
  qexists_tac `\next st. plain_operand st next /\ plain_operand st (Var ctr)` >> conj_tac
  >- suspend "increment" >>
  stmt_frame_emit `\st. plain_operand st (Var ctr)`
QED
Resume compile_word_copy_loop_noncode_shape[increment]:
  qx_gen_tac `new_ctr` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st new_ctr /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. plain_operand st new_ctr /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_jmp >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_drop (ho_match_mp_tac stmt_shape_new_block >>
    simp[shape_stable_conj, stmt_shape_stable_plain])
QED
Finalise compile_word_copy_loop_noncode_shape[local]

Theorem compile_memory_to_storage_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_memory_to_storage src dst n) (\u st. T)
Proof
  simp[compile_memory_to_storage_def, compile_word_copy_loop_noncode_shape]
QED

Theorem compile_memory_to_transient_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_memory_to_transient src dst n) (\u st. T)
Proof
  simp[compile_memory_to_transient_def, compile_word_copy_loop_noncode_shape]
QED

Theorem compile_slot_to_memory_shape[local]:
  !internal src dst n loc.
    loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_slot_to_memory src dst n loc) (\u st. T)
Proof
  simp[compile_slot_to_memory_def, compile_word_copy_loop_noncode_shape]
QED

Theorem stmt_typed_copy_loop_shape:
  !internal action dst src bound dst_sz src_sz cond_lbl body_lbl exit_lbl.
    compiler_label cond_lbl /\ compiler_label body_lbl /\ compiler_label exit_lbl /\
    (!dp sp. shape_step internal compiler_label
      (\st. plain_operand st dp /\ plain_operand st sp) (action dp sp) (\u:unit st. T)) ==>
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st bound)
      (do counter <- fresh_var;
          emit_inst ASSIGN [Lit 0w] [counter];
          emit_inst JMP [Label cond_lbl] [];
          new_block cond_lbl;
          lt_op <- emit_op LT [Var counter; bound];
          done_op <- emit_op ISZERO [lt_op];
          emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
          new_block body_lbl;
          src_off <- emit_op MUL [Var counter; Lit (n2w src_sz)];
          dst_off <- emit_op MUL [Var counter; Lit (n2w dst_sz)];
          src_elem <- emit_op ADD [src; src_off];
          dst_elem <- emit_op ADD [dst; dst_off];
          action dst_elem src_elem;
          new_ctr <- emit_op ADD [Var counter; Lit 1w];
          emit_inst ASSIGN [new_ctr] [counter];
          emit_inst JMP [Label cond_lbl] [];
          _ <- new_block exit_lbl;
          return () od) (\u st. T)
Proof
  rpt strip_tac >> irule shape_step_bind >>
  qexists_tac `\ctr st. (plain_operand st dst /\ plain_operand st src /\ plain_operand st bound) /\ plain_operand st (Var ctr)` >> conj_tac
  >- suspend "counter" >>
  ho_match_mp_tac shape_step_fresh_var >>
  simp[shape_stable_conj, stmt_shape_stable_plain]
QED
Resume stmt_typed_copy_loop_shape[counter]:
  qx_gen_tac `ctr` >> BETA_TAC >>
  qabbrev_tac `typed_live = \st. (plain_operand st dst /\ plain_operand st src) /\ plain_operand st (Var ctr)` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. typed_live st /\ plain_operand st bound`, `\u st. T`] >>
  simp[] >> conj_tac >- simp[Abbr `typed_live`] >>
  stmt_sequence `\u st. typed_live st /\ plain_operand st bound`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[Abbr `typed_live`, shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. typed_live st /\ plain_operand st bound`
    (ho_match_mp_tac stmt_shape_jmp >> simp[Abbr `typed_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. typed_live st /\ plain_operand st bound`
    (ho_match_mp_tac stmt_shape_new_block >> simp[Abbr `typed_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\lt st. plain_operand st lt /\ typed_live st` >> conj_tac
  >- (qx_gen_tac `lt_op` >> BETA_TAC >>
      irule shape_step_bind >> qexists_tac `\done st. plain_operand st done /\ typed_live st` >> conj_tac
      >- (qx_gen_tac `done_op` >> BETA_TAC >>
          stmt_sequence `\u st. typed_live st`
            (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
             simp[Abbr `typed_live`, shape_stable_conj, stmt_shape_stable_plain])) >>
          stmt_sequence `\u st. typed_live st`
            (ho_match_mp_tac stmt_shape_new_block >>
             simp[Abbr `typed_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
          simp[Abbr `typed_live`] >> suspend "elements") >>
      simp[Abbr `typed_live`] >> stmt_frame_emit `\st. plain_operand st lt_op`) >>
  simp[Abbr `typed_live`] >> stmt_frame_emit `\st. plain_operand st (Var ctr) /\ plain_operand st bound`
QED
Resume stmt_typed_copy_loop_shape[elements]:
  irule shape_step_bind >>
  qexists_tac `\so st. plain_operand st so /\ ((plain_operand st dst /\ plain_operand st src) /\ plain_operand st (Var ctr))` >> conj_tac
  >- (qx_gen_tac `so` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\doff st. plain_operand st doff /\ (plain_operand st so /\ (plain_operand st dst /\ plain_operand st src /\ plain_operand st (Var ctr)))` >> conj_tac
      >- suspend "pointers" >>
      stmt_frame_emit `\st. plain_operand st (Var ctr)`) >>
  stmt_frame_emit `\st. plain_operand st (Var ctr)`
QED
Resume stmt_typed_copy_loop_shape[pointers]:
  qx_gen_tac `doff` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\sp st. plain_operand st sp /\ (plain_operand st doff /\ plain_operand st dst /\ plain_operand st (Var ctr))` >> conj_tac
  >- (qx_gen_tac `sp` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\dp st. plain_operand st dp /\ (plain_operand st sp /\ plain_operand st (Var ctr))` >> conj_tac
      >- suspend "action" >>
      stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st doff`) >>
  stmt_frame_emit `\st. plain_operand st src /\ plain_operand st so`
QED
Resume stmt_typed_copy_loop_shape[action]:
  qx_gen_tac `dp` >> BETA_TAC >>
  stmt_sequence `\u st. T /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st dp /\ plain_operand st sp` >>
     simp[stmt_shape_stable_plain]) >>
  simp[] >> irule shape_step_bind >>
  qexists_tac `\next st. plain_operand st next /\ plain_operand st (Var ctr)` >> conj_tac
  >- suspend "increment" >>
  stmt_frame_emit `\st. plain_operand st (Var ctr)`
QED
Resume stmt_typed_copy_loop_shape[increment]:
  qx_gen_tac `next` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st next /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. plain_operand st next /\ plain_operand st (Var ctr)`
    (ho_match_mp_tac stmt_shape_jmp >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  stmt_drop (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain])
QED
Finalise stmt_typed_copy_loop_shape[local]

Theorem compile_typed_copy_shape:
  (!cenv dst dst_ty src src_ty. !internal.
    shape_step internal compiler_label (\st. plain_operand st dst /\ plain_operand st src)
      (compile_store_memory_typed cenv dst dst_ty src src_ty) (\u st. T)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off. !internal.
    shape_step internal compiler_label (\st. plain_operand st dst /\ plain_operand st src)
      (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off) (\u st. T)) /\
  (!cenv dst dst_elem src src_elem count. !internal.
    shape_step internal compiler_label (\st. plain_operand st dst /\ plain_operand st src)
      (compile_copy_sarray_typed cenv dst dst_elem src src_elem count) (\u st. T)) /\
  (!cenv dst dst_elem capacity src src_elem. !internal.
    shape_step internal compiler_label (\st. plain_operand st dst /\ plain_operand st src)
      (compile_copy_dynarray_typed cenv dst dst_elem capacity src src_elem) (\u st. T)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off. !internal.
    shape_step internal compiler_label (\st. plain_operand st dst /\ plain_operand st src)
      (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off) (\u st. T))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >> rpt gen_tac >> irule shape_step_return >> simp[]) >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >> rpt gen_tac >> irule shape_step_return >> simp[]) >>
  conj_tac >- suspend "fields" >>
  conj_tac >- suspend "sarray" >>
  conj_tac >- suspend "dynarray" >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >> rpt gen_tac >> irule shape_step_return >> simp[]) >>
  suspend "struct"
QED
Resume compile_typed_copy_shape[dispatch]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ plain_operand st dst` >> conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_plain_void_drop) >>
      stmt_frame_emit `\st. plain_operand st src`) >>
  IF_CASES_TAC
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. plain_operand st src /\ plain_operand st dst`, `\u st. T`] >>
      simp[compile_store_bytestring_shape]) >>
  IF_CASES_TAC >- stmt_plain_void_drop >>
  Cases_on `dst_ty` >> Cases_on `src_ty` >>
  simp[compile_copy_memory_shape] >> gvs[] >>
  FIRST [
    (rename1 `ArrayT elem dst_len` >>
     qpat_x_assum `~is_word_type (ArrayT elem dst_len)` kall_tac >>
     Cases_on `dst_len` >>
     qmatch_goalsub_rename_tac `case src_len of Fixed _ => _ | Dynamic _ => _` >>
     Cases_on `src_len` >> gvs[compile_copy_memory_shape]) >> NO_TAC,
    first_assum irule]
QED
Resume compile_typed_copy_shape[fields]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  gvs[] >> simp[Once compile_store_memory_typed_def] >>
  irule shape_step_bind >>
  qexists_tac `\dp st. plain_operand st dp /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- (qx_gen_tac `dp` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\sp st. plain_operand st sp /\ (plain_operand st dp /\ (plain_operand st dst /\ plain_operand st src))` >> conj_tac
      >- (qx_gen_tac `sp` >> BETA_TAC >>
          stmt_sequence `\u st. T /\ (plain_operand st dst /\ plain_operand st src)`
            (ho_match_mp_tac stmt_shape_frame >>
             qexists_tac `\st. plain_operand st dp /\ plain_operand st sp` >>
             simp[shape_stable_conj, stmt_shape_stable_plain] >> first_assum irule) >>
          simp[] >> first_assum irule) >>
      ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st src` >>
      simp[shape_stable_conj, stmt_shape_stable_plain, compile_with_byte_offset_shape]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st dst` >>
  simp[shape_stable_conj, stmt_shape_stable_plain, compile_with_byte_offset_shape]
QED
Resume compile_typed_copy_shape[struct]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  gvs[] >> simp[Once compile_store_memory_typed_def] >>
  pairarg_tac >> gvs[] >>
  irule shape_step_bind >>
  qexists_tac `\dp st. plain_operand st dp /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- (qx_gen_tac `dp` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\sp st. plain_operand st sp /\ (plain_operand st dp /\ (plain_operand st dst /\ plain_operand st src))` >> conj_tac
      >- (qx_gen_tac `sp` >> BETA_TAC >>
          stmt_sequence `\u st. T /\ (plain_operand st dst /\ plain_operand st src)`
            (ho_match_mp_tac stmt_shape_frame >>
             qexists_tac `\st. plain_operand st dp /\ plain_operand st sp` >>
             simp[shape_stable_conj, stmt_shape_stable_plain] >> first_assum irule) >>
          simp[] >> first_assum irule) >>
      ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st src` >>
      simp[shape_stable_conj, stmt_shape_stable_plain, compile_with_byte_offset_shape]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st dst` >>
  simp[shape_stable_conj, stmt_shape_stable_plain, compile_with_byte_offset_shape]
QED
Resume compile_typed_copy_shape[sarray]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  rename1 `compile_copy_sarray_typed cenv dst dst_elem src src_elem ncopy` >>
  simp[Once compile_store_memory_typed_def] >> IF_CASES_TAC
  >- simp[compile_copy_memory_shape] >> gvs[] >>
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st dst /\ plain_operand st src) /\ compiler_label l` >> conj_tac
  >- (qx_gen_tac `cl` >> BETA_TAC >> reverse (Cases_on `compiler_label cl`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >>
      qexists_tac `\l st. (plain_operand st dst /\ plain_operand st src) /\ compiler_label l` >> conj_tac
      >- (qx_gen_tac `bl` >> BETA_TAC >> reverse (Cases_on `compiler_label bl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >>
          qexists_tac `\l st. (plain_operand st dst /\ plain_operand st src) /\ compiler_label l` >> conj_tac
          >- (qx_gen_tac `el` >> BETA_TAC >> reverse (Cases_on `compiler_label el`)
              >- simp[shape_step_def] >> simp[] >>
              irule shape_step_conseq >>
              qexistsl_tac [`compiler_label`,
                `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st (Lit (n2w ncopy))`, `\u st. T`] >>
              simp[] >> conj_tac
              >- simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
              ho_match_mp_tac stmt_typed_copy_loop_shape >> simp[]) >>
          ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_typed_copy_shape[dynarray]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[Once compile_store_memory_typed_def] >>
  irule shape_step_bind >>
  qexists_tac `\len st. plain_operand st len /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- suspend "length" >>
  stmt_frame_emit `\st. plain_operand st src`
QED
Resume compile_typed_copy_shape[length]:
  qx_gen_tac `len` >> BETA_TAC >>
  qabbrev_tac `dyn_live = \st. plain_operand st len /\ (plain_operand st dst /\ plain_operand st src)` >>
  irule shape_step_bind >> qexists_tac `\test st. plain_operand st test /\ dyn_live st` >> conj_tac
  >- (qx_gen_tac `too_long` >> BETA_TAC >>
      irule shape_step_bind >> qexists_tac `\test st. plain_operand st test /\ dyn_live st` >> conj_tac
      >- (qx_gen_tac `ok` >> BETA_TAC >>
          stmt_sequence `\u st. dyn_live st`
            (irule shape_step_conseq >>
             qexistsl_tac [`compiler_label`, `\st. plain_operand st ok /\ dyn_live st`,
               `\u st. plain_operand st ok /\ dyn_live st`] >> simp[] >>
             simp[Abbr `dyn_live`] >> stmt_plain_void) >>
          stmt_sequence `\u st. dyn_live st`
            (simp[Abbr `dyn_live`] >> stmt_plain_void) >>
          simp[Abbr `dyn_live`] >> suspend "data") >>
      simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st too_long`) >>
  simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st len`
QED
Resume compile_typed_copy_shape[data]:
  irule shape_step_bind >>
  qexists_tac `\sp st. plain_operand st sp /\ (plain_operand st dst /\ plain_operand st len)` >> conj_tac
  >- (qx_gen_tac `sp` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\dp st. plain_operand st dp /\ plain_operand st sp /\ plain_operand st len` >> conj_tac
      >- suspend "copy_data" >>
      stmt_frame_emit `\st. plain_operand st dst`) >>
  stmt_frame_emit `\st. plain_operand st src`
QED
Resume compile_typed_copy_shape[copy_data]:
  qx_gen_tac `dp` >> BETA_TAC >> IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\sz st. plain_operand st sz /\ (plain_operand st dp /\ plain_operand st sp)` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. plain_operand st dp /\ plain_operand st sp /\ plain_operand st x`, `\u st. T`] >>
          simp[compile_copy_memory_dynamic_shape]) >>
      stmt_frame_emit `\st. plain_operand st len`) >>
  gvs[] >> suspend "dyn_labels"
QED
Resume compile_typed_copy_shape[dyn_labels]:
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st dp /\ plain_operand st sp /\ plain_operand st len) /\ compiler_label l` >> conj_tac
  >- (qx_gen_tac `cl` >> BETA_TAC >> reverse (Cases_on `compiler_label cl`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >>
      qexists_tac `\l st. (plain_operand st dp /\ plain_operand st sp /\ plain_operand st len) /\ compiler_label l` >> conj_tac
      >- (qx_gen_tac `bl` >> BETA_TAC >> reverse (Cases_on `compiler_label bl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >>
          qexists_tac `\l st. (plain_operand st dp /\ plain_operand st sp /\ plain_operand st len) /\ compiler_label l` >> conj_tac
          >- (qx_gen_tac `el` >> BETA_TAC >> reverse (Cases_on `compiler_label el`)
              >- simp[shape_step_def] >> simp[] >>
              ho_match_mp_tac stmt_typed_copy_loop_shape >> simp[]) >>
          ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]
QED
Finalise compile_typed_copy_shape[local]

Theorem compile_store_memory_shape:
  !cenv src dst dst_ty src_ty internal.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_store_memory cenv src dst dst_ty src_ty) (\u st. T)
Proof
  rpt gen_tac >> simp[Once compile_store_memory_def] >> IF_CASES_TAC
  >- stmt_plain_void_drop >>
  IF_CASES_TAC
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. plain_operand st src /\ plain_operand st dst`, `\u st. T`] >>
      simp[compile_store_bytestring_shape]) >>
  IF_CASES_TAC >> simp[compile_typed_copy_shape, compile_copy_memory_shape]
QED


Theorem compile_abi_encode_static_shape[local]:
  !internal dst src.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_abi_encode_static dst src) (\v st. plain_operand st v)
Proof
  rpt gen_tac >> simp[compile_abi_encode_static_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ plain_operand st dst` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      stmt_sequence `\u st. T` stmt_plain_void_drop >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_frame_emit `\st. plain_operand st src`
QED

Theorem compile_abi_encode_static_info_shape[local]:
  !internal dst src info.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_abi_encode_static_info dst src info) (\v st. plain_operand st v)
Proof
  rpt gen_tac >> Cases_on `info` >> simp[compile_abi_encode_static_info_def]
  >- irule compile_abi_encode_static_shape
  >- (irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])
  >- (stmt_sequence `\u st. T` stmt_plain_void_drop >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])
  >> irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_abi_encode_dyn_static_loop_shape:
  !internal dst src info asz msz len_op.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)
      (compile_abi_encode_dyn_static_loop dst src info asz msz len_op)
      (\v st. plain_operand st v)
Proof
  rpt gen_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  irule shape_step_bind >>
  qexists_tac `\b st. plain_operand st b.buf_operand /\
    (plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)` >>
  conj_tac >- suspend "allocated" >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
  simp[compile_alloc_buffer_shape, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_dyn_static_loop_shape[allocated]:
  qx_gen_tac `buf` >> BETA_TAC >> simp[] >>
  qabbrev_tac `enc_live = \st. plain_operand st buf.buf_operand /\
    (plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)` >>
  stmt_sequence `\u st. enc_live st`
    (simp[Abbr `enc_live`] >> stmt_plain_void) >>
  irule shape_step_bind >> qexists_tac `\l st. enc_live st /\ compiler_label l` >> conj_tac
  >- (qx_gen_tac `hdr` >> BETA_TAC >> reverse (Cases_on `compiler_label hdr`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >> qexists_tac `\l st. enc_live st /\ compiler_label l` >> conj_tac
      >- (qx_gen_tac `body_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label body_lbl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >> qexists_tac `\l st. enc_live st /\ compiler_label l` >> conj_tac
          >- (qx_gen_tac `exit` >> BETA_TAC >> reverse (Cases_on `compiler_label exit`)
              >- simp[shape_step_def] >> simp[] >> suspend "header") >>
          ho_match_mp_tac shape_step_fresh_label >>
          simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >>
      simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >>
  simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_dyn_static_loop_shape[header]:
  stmt_sequence `\u st. enc_live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. enc_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ enc_live st` >> conj_tac
  >- (qx_gen_tac `index` >> BETA_TAC >>
      irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ enc_live st` >> conj_tac
      >- (qx_gen_tac `cmp` >> BETA_TAC >>
          irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ enc_live st` >> conj_tac
          >- (qx_gen_tac `done_op` >> BETA_TAC >>
              stmt_sequence `\u st. enc_live st`
                (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
                 simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain])) >>
              stmt_sequence `\u st. enc_live st`
                (ho_match_mp_tac stmt_shape_new_block >>
                 simp[Abbr `enc_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
              suspend "body") >>
          simp[Abbr `enc_live`] >> stmt_frame_emit `\st. plain_operand st cmp`) >>
      simp[Abbr `enc_live`] >> stmt_frame_emit `\st. plain_operand st index /\ plain_operand st len_op`) >>
  simp[Abbr `enc_live`] >> stmt_frame_emit `\st. plain_operand st buf.buf_operand`
QED
Resume compile_abi_encode_dyn_static_loop_shape[body]:
  simp[Abbr `enc_live`] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st src /\ plain_operand st dst /\ plain_operand st buf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `idx` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st src /\ plain_operand st dst /\ plain_operand st buf.buf_operand)` >> conj_tac
      >- (qx_gen_tac `src_data` >> BETA_TAC >>
          irule shape_step_bind >>
          qexists_tac `\v st. plain_operand st v /\ (plain_operand st src_data /\ plain_operand st idx /\ plain_operand st src /\ plain_operand st dst /\ plain_operand st buf.buf_operand)` >> conj_tac
          >- (qx_gen_tac `src_off` >> BETA_TAC >>
              irule shape_step_bind >>
              qexists_tac `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st src /\ plain_operand st dst /\ plain_operand st buf.buf_operand)` >> conj_tac
              >- suspend "destination" >>
              stmt_frame_emit `\st. plain_operand st src_data /\ plain_operand st src_off`) >>
          stmt_frame_emit `\st. plain_operand st idx`) >>
      stmt_frame_emit `\st. plain_operand st src`) >>
  stmt_frame_emit `\st. plain_operand st buf.buf_operand`
QED
Resume compile_abi_encode_dyn_static_loop_shape[destination]:
  qx_gen_tac `child_src` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_src /\ plain_operand st idx /\ plain_operand st src /\ plain_operand st buf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `dst_data` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st dst_data /\ plain_operand st child_src /\ plain_operand st idx /\ plain_operand st src /\ plain_operand st buf.buf_operand)` >> conj_tac
      >- (qx_gen_tac `dst_off` >> BETA_TAC >>
          irule shape_step_bind >>
          qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_src /\ plain_operand st idx /\ plain_operand st src /\ plain_operand st buf.buf_operand)` >> conj_tac
          >- suspend "encode" >>
          stmt_frame_emit `\st. plain_operand st dst_data /\ plain_operand st dst_off`) >>
      stmt_frame_emit `\st. plain_operand st idx`) >>
  stmt_frame_emit `\st. plain_operand st dst`
QED
Resume compile_abi_encode_dyn_static_loop_shape[encode]:
  qx_gen_tac `child_dst` >> BETA_TAC >>
  stmt_sequence `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st src /\ plain_operand st buf.buf_operand)`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st child_dst /\ plain_operand st child_src` >>
     simp[compile_abi_encode_static_info_shape, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st src /\ plain_operand st buf.buf_operand)` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      stmt_sequence `\u st. plain_operand st src` stmt_plain_void_drop >>
      suspend "exit") >>
  stmt_frame_emit `\st. plain_operand st idx`
QED
Resume compile_abi_encode_dyn_static_loop_shape[exit]:
  stmt_sequence `\u st. plain_operand st src`
    (ho_match_mp_tac stmt_shape_jmp >> simp[stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st src`
    (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit) >>
  stmt_plain_emit
QED
Finalise compile_abi_encode_dyn_static_loop_shape[local]

Theorem compile_abi_encode_shape:
  (!dst cp ci is_dyn off dp internal.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st cp /\ plain_operand st dp)
      (compile_abi_encode_child dst cp ci is_dyn off dp)
      (\v st. plain_operand st v)) /\
  (!dst src info internal.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_abi_encode_to_buf dst src info) (\v st. plain_operand st v)) /\
  (!dst src elems so ho dp internal.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st dp)
      (compile_abi_encode_complex_elems dst src elems so ho dp)
      (\v st. plain_operand st v)) /\
  (!dst src info asz msz len_op internal.
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)
      (compile_abi_encode_dyn_loop dst src info asz msz len_op)
      (\v st. plain_operand st v))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- (rpt gen_tac >> simp[Once compile_abi_encode_child_def, compile_abi_encode_static_shape])
  >- suspend "bytes"
  >- (rpt gen_tac >> simp[Once compile_abi_encode_child_def] >>
      stmt_sequence `\u st. T` stmt_plain_void_drop >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])
  >- suspend "array"
  >- (rpt gen_tac >> simp[Once compile_abi_encode_child_def] >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])
  >- suspend "complex"
  >- (rpt gen_tac >> simp[Once compile_abi_encode_child_def] >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])
  >- suspend "elems"
  >> suspend "dyn_loop"
QED
Resume compile_abi_encode_shape[child]:
  map_every qx_gen_tac [`dst`, `child_ptr`, `ci`, `is_dyn`, `off`, `dp`] >>
  strip_tac >> gen_tac >> simp[Once compile_abi_encode_child_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st dst /\ plain_operand st child_ptr /\ plain_operand st dp)` >> conj_tac
  >- (qx_gen_tac `static_ptr` >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. plain_operand st static_ptr /\ plain_operand st child_ptr`, `\v st. plain_operand st v`] >>
          simp[] >> first_x_assum irule >> simp[]) >>
      suspend "dynamic_child") >>
  stmt_frame_emit `\st. plain_operand st dst`
QED
Resume compile_abi_encode_shape[dynamic_child]:
  gvs[] >> irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st static_ptr /\ plain_operand st dst /\ plain_operand st child_ptr /\ plain_operand st dp)` >> conj_tac
  >- (qx_gen_tac `dyn_off` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st static_ptr /\ plain_operand st dyn_off /\ plain_operand st child_ptr /\ plain_operand st dp)` >> conj_tac
      >- (qx_gen_tac `child_dst` >> BETA_TAC >>
          irule shape_step_bind >>
          qexists_tac `\v st. plain_operand st v /\ (plain_operand st static_ptr /\ plain_operand st dyn_off /\ plain_operand st dp)` >> conj_tac
          >- suspend "child_tail" >>
          ho_match_mp_tac stmt_shape_frame >>
          qexists_tac `\st. plain_operand st child_dst /\ plain_operand st child_ptr` >>
          simp[shape_stable_conj, stmt_shape_stable_plain] >> first_x_assum irule >> simp[]) >>
      stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st dyn_off`) >>
  stmt_frame_emit `\st. plain_operand st dp`
QED
Resume compile_abi_encode_shape[child_tail]:
  qx_gen_tac `child_len` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st dp` stmt_plain_void_drop >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_len /\ plain_operand st dp)` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      stmt_sequence `\u st. plain_operand st child_len` stmt_plain_void_drop >>
      irule shape_step_return >> simp[]) >>
  stmt_frame_emit `\st. plain_operand st dyn_off /\ plain_operand st child_len`
QED
Resume compile_abi_encode_shape[bytes]:
  rpt gen_tac >> simp[Once compile_abi_encode_child_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- (qx_gen_tac `len_op` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st len_op /\ plain_operand st dst /\ plain_operand st src)` >> conj_tac
      >- (qx_gen_tac `ceil_arg` >> BETA_TAC >>
          irule shape_step_bind >>
          qexists_tac `\v st. plain_operand st v /\ (plain_operand st len_op /\ plain_operand st dst /\ plain_operand st src)` >> conj_tac
          >- (qx_gen_tac `last_off` >> BETA_TAC >>
              irule shape_step_bind >>
              qexists_tac `\v st. plain_operand st v /\ (plain_operand st len_op /\ plain_operand st dst /\ plain_operand st src)` >> conj_tac
              >- suspend "bytes_copy" >>
              stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st last_off`) >>
          stmt_frame_emit `\st. plain_operand st ceil_arg`) >>
      stmt_frame_emit `\st. plain_operand st len_op`) >>
  stmt_frame_emit `\st. plain_operand st src`
QED
Resume compile_abi_encode_shape[bytes_copy]:
  qx_gen_tac `last_ptr` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st len_op /\ plain_operand st dst /\ plain_operand st src` stmt_plain_void_drop >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st len_op /\ plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      stmt_sequence `\u st. plain_operand st len_op` stmt_plain_void_drop >>
      irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
          >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit) >>
      stmt_plain_emit) >>
  stmt_frame_emit `\st. plain_operand st len_op`
QED
Resume compile_abi_encode_shape[array]:
  rpt strip_tac >> simp[Once compile_abi_encode_child_def] >>
  irule shape_step_bind >>
  qexists_tac `\b st. plain_operand st b.buf_operand /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- suspend "array_alloc" >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
  simp[compile_alloc_buffer_shape, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_shape[array_alloc]:
  qx_gen_tac `buf` >> BETA_TAC >> simp[] >>
  stmt_sequence `\u st. plain_operand st buf.buf_operand /\ (plain_operand st dst /\ plain_operand st src)` stmt_plain_void >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st buf.buf_operand /\ plain_operand st dst /\ plain_operand st src)` >> conj_tac
  >- (qx_gen_tac `len_op` >> BETA_TAC >>
      stmt_sequence `\u st. plain_operand st len_op /\ (plain_operand st buf.buf_operand /\ plain_operand st dst /\ plain_operand st src)` stmt_plain_void >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ plain_operand st buf.buf_operand` >> conj_tac
      >- suspend "array_tail" >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op` >>
      simp[stmt_shape_stable_plain] >> IF_CASES_TAC
      >- irule compile_abi_encode_dyn_static_loop_shape >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st src /\ plain_operand st len_op)` >> conj_tac
      >- (gen_tac >> BETA_TAC >> first_x_assum irule >>
          gvs[]) >>
      stmt_frame_emit `\st. plain_operand st dst`) >>
  stmt_frame_emit `\st. plain_operand st src`
QED
Resume compile_abi_encode_shape[array_tail]:
  qx_gen_tac `encoded_size` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st encoded_size /\ plain_operand st buf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `parent_dyn` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ plain_operand st buf.buf_operand` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          stmt_sequence `\u st. plain_operand st buf.buf_operand` stmt_plain_void_drop >> stmt_plain_emit) >>
      stmt_frame_emit `\st. plain_operand st parent_dyn /\ plain_operand st encoded_size`) >>
  stmt_frame_emit `\st. plain_operand st buf.buf_operand`
QED
Resume compile_abi_encode_shape[complex]:
  rpt strip_tac >> simp[Once compile_abi_encode_child_def] >> IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\b st. plain_operand st b.buf_operand /\ (plain_operand st dst /\ plain_operand st src)` >> conj_tac
      >- suspend "complex_alloc" >>
      ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
      simp[compile_alloc_buffer_shape, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. T`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st (Lit 0w)`, `\v st. plain_operand st v`] >>
     simp[] >> conj_tac
     >- simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
     first_x_assum irule >> gvs[]) >>
  irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_abi_encode_shape[complex_alloc]:
  qx_gen_tac `buf` >> BETA_TAC >> simp[] >>
  stmt_sequence `\u st. plain_operand st buf.buf_operand /\ (plain_operand st dst /\ plain_operand st src)` stmt_plain_void >>
  stmt_sequence `\v st. plain_operand st v /\ plain_operand st buf.buf_operand`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st buf.buf_operand` >>
     simp[stmt_shape_stable_plain] >> first_x_assum irule >> gvs[] >>
     qexists_tac `buf` >> simp[]) >>
  stmt_plain_emit
QED
Resume compile_abi_encode_shape[elems]:
  rpt strip_tac >> simp[Once compile_abi_encode_child_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st dst /\ plain_operand st src /\ plain_operand st dp)` >> conj_tac
  >- (qx_gen_tac `elem_ptr` >> BETA_TAC >>
      stmt_sequence `\v st. plain_operand st v /\ (plain_operand st dst /\ plain_operand st src /\ plain_operand st dp)`
        (ho_match_mp_tac stmt_shape_frame >>
         qexists_tac `\st. plain_operand st dst /\ plain_operand st elem_ptr /\ plain_operand st dp` >>
         simp[shape_stable_conj, stmt_shape_stable_plain] >> first_x_assum irule) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. plain_operand st dst /\ plain_operand st src /\ plain_operand st dp`, `\v st. plain_operand st v`] >>
      gvs[arithmeticTheory.ADD_COMM]) >>
  stmt_frame_emit `\st. plain_operand st src`
QED
Resume compile_abi_encode_shape[dyn_loop]:
  rpt strip_tac >> simp[Once compile_abi_encode_child_def] >>
  irule shape_step_bind >>
  qexists_tac `\b st. plain_operand st b.buf_operand /\ (plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)` >> conj_tac
  >- suspend "dyn_counter" >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
  simp[compile_alloc_buffer_shape, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_shape[dyn_counter]:
  qx_gen_tac `ibuf` >> BETA_TAC >> simp[] >>
  stmt_sequence `\u st. plain_operand st ibuf.buf_operand /\ (plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)` stmt_plain_void >>
  irule shape_step_bind >>
  qexists_tac `\b st. plain_operand st b.buf_operand /\ (plain_operand st ibuf.buf_operand /\ plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op)` >> conj_tac
  >- suspend "dyn_alloc" >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
  simp[compile_alloc_buffer_shape, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_shape[dyn_alloc]:
  qx_gen_tac `dbuf` >> BETA_TAC >> simp[] >>
  qabbrev_tac `dyn_live = \st. plain_operand st dbuf.buf_operand /\ plain_operand st ibuf.buf_operand /\ plain_operand st dst /\ plain_operand st src /\ plain_operand st len_op` >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ dyn_live st` >> conj_tac
  >- (qx_gen_tac `init_dyn` >> BETA_TAC >>
      stmt_sequence `\u st. dyn_live st` (suspend "dyn_init_store") >>
      suspend "dyn_labels") >>
  simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st len_op`
QED
Resume compile_abi_encode_shape[dyn_init_store]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. plain_operand st init_dyn /\ dyn_live st`, `\u st. plain_operand st init_dyn /\ dyn_live st`] >>
  simp[] >> ho_match_mp_tac stmt_shape_emit_void >> conj_tac
  >- (qspec_then `[init_dyn; dbuf.buf_operand; ibuf.buf_operand; dst; src; len_op]` mp_tac shape_stable_plain_operands >>
      simp[EVERY_DEF, Abbr `dyn_live`]) >>
  simp[Abbr `dyn_live`, label_or_plain_def] >>
  stmt_shape_emit_simp >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_abi_encode_shape[dyn_labels]:
  irule shape_step_bind >> qexists_tac `\l st. dyn_live st /\ compiler_label l` >> conj_tac
  >- (qx_gen_tac `hdr` >> BETA_TAC >> reverse (Cases_on `compiler_label hdr`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >> qexists_tac `\l st. dyn_live st /\ compiler_label l` >> conj_tac
      >- (qx_gen_tac `body_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label body_lbl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >> qexists_tac `\l st. dyn_live st /\ compiler_label l` >> conj_tac
          >- (qx_gen_tac `exit` >> BETA_TAC >> reverse (Cases_on `compiler_label exit`)
              >- simp[shape_step_def] >> simp[] >> suspend "dyn_header") >>
          ho_match_mp_tac shape_step_fresh_label >>
          simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >>
      simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >>
  simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_abi_encode_shape[dyn_header]:
  `shape_stable dyn_live` by
    (qspec_then `[dbuf.buf_operand; ibuf.buf_operand; dst; src; len_op]` mp_tac shape_stable_plain_operands >>
     simp[EVERY_DEF, Abbr `dyn_live`]) >>
  `!v. shape_stable (\st. plain_operand st v /\ dyn_live st)` by
    (gen_tac >> qspec_then `[v; dbuf.buf_operand; ibuf.buf_operand; dst; src; len_op]` mp_tac shape_stable_plain_operands >>
     simp[EVERY_DEF, Abbr `dyn_live`]) >>
  stmt_sequence `\u st. dyn_live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. dyn_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ dyn_live st` >> conj_tac
  >- (qx_gen_tac `index` >> BETA_TAC >>
      irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ dyn_live st` >> conj_tac
      >- (qx_gen_tac `cmp` >> BETA_TAC >>
          irule shape_step_bind >> qexists_tac `\v st. plain_operand st v /\ dyn_live st` >> conj_tac
          >- (qx_gen_tac `done_op` >> BETA_TAC >>
              stmt_sequence `\u st. dyn_live st`
                (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
                 simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain])) >>
              stmt_sequence `\u st. dyn_live st`
                (ho_match_mp_tac stmt_shape_new_block >>
                 simp[Abbr `dyn_live`, shape_stable_conj, stmt_shape_stable_plain]) >>
              suspend "dyn_source") >>
          simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st cmp`) >>
      simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st index /\ plain_operand st len_op`) >>
  simp[Abbr `dyn_live`] >> stmt_frame_emit `\st. plain_operand st ibuf.buf_operand`
QED
Resume compile_abi_encode_shape[dyn_source]:
  simp[Abbr `dyn_live`] >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st src /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `idx` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
      >- (qx_gen_tac `src_data` >> BETA_TAC >>
          irule shape_step_bind >>
          qexists_tac `\v st. plain_operand st v /\ (plain_operand st src_data /\ plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
          >- (qx_gen_tac `src_off` >> BETA_TAC >>
              irule shape_step_bind >>
              qexists_tac `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
              >- suspend "dyn_destination" >>
              stmt_frame_emit `\st. plain_operand st src_data /\ plain_operand st src_off`) >>
          stmt_frame_emit `\st. plain_operand st idx`) >>
      stmt_frame_emit `\st. plain_operand st src`) >>
  stmt_frame_emit `\st. plain_operand st ibuf.buf_operand`
QED
Resume compile_abi_encode_shape[dyn_destination]:
  qx_gen_tac `child_src` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_src /\ plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `dyn_off` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_src /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
      >- suspend "dyn_encode" >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st dst /\ plain_operand st dyn_off` >>
      conj_tac >- stmt_plain_emit >> conj_tac
      >- (qspec_then `[child_src; dyn_off; idx; dst; ibuf.buf_operand; dbuf.buf_operand]` mp_tac shape_stable_plain_operands >> simp[EVERY_DEF]) >>
      simp[]) >>
  stmt_frame_emit `\st. plain_operand st dbuf.buf_operand`
QED
Resume compile_abi_encode_shape[dyn_encode]:
  qx_gen_tac `child_dst` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
  >- suspend "dyn_head" >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st child_dst /\ plain_operand st child_src` >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >> first_x_assum irule >> simp[]
QED
Resume compile_abi_encode_shape[dyn_head]:
  qx_gen_tac `child_len` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st dst /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
  >- (qx_gen_tac `head_off` >> BETA_TAC >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
      >- suspend "dyn_updates" >>
      stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st head_off`) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st idx` >>
  conj_tac >- stmt_plain_emit >> conj_tac
  >- (qspec_then `[child_len; dyn_off; idx; dst; ibuf.buf_operand; dbuf.buf_operand]` mp_tac shape_stable_plain_operands >> simp[EVERY_DEF]) >> simp[]
QED
Resume compile_abi_encode_shape[dyn_updates]:
  qx_gen_tac `head_ptr` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand`
    (suspend "dyn_head_store") >>
  irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v /\ (plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      stmt_sequence `\u st. plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand` stmt_plain_void_drop >>
      irule shape_step_bind >>
      qexists_tac `\v st. plain_operand st v /\ (plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand)` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          stmt_sequence `\u st. plain_operand st dbuf.buf_operand` stmt_plain_void_drop >> suspend "dyn_exit") >>
      stmt_frame_emit `\st. plain_operand st idx`) >>
  stmt_frame_emit `\st. plain_operand st dyn_off /\ plain_operand st child_len`
QED
Resume compile_abi_encode_shape[dyn_head_store]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. plain_operand st head_ptr /\ plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand`, `\u st. plain_operand st head_ptr /\ plain_operand st child_len /\ plain_operand st dyn_off /\ plain_operand st idx /\ plain_operand st ibuf.buf_operand /\ plain_operand st dbuf.buf_operand`] >>
  simp[] >> ho_match_mp_tac stmt_shape_emit_void >> conj_tac
  >- (qspec_then `[head_ptr; child_len; dyn_off; idx; ibuf.buf_operand; dbuf.buf_operand]` mp_tac shape_stable_plain_operands >> simp[EVERY_DEF]) >>
  simp[label_or_plain_def] >> stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_abi_encode_shape[dyn_exit]:
  stmt_sequence `\u st. plain_operand st dbuf.buf_operand`
    (ho_match_mp_tac stmt_shape_jmp >> simp[stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st dbuf.buf_operand`
    (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_plain]) >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >> stmt_plain_emit
QED
Finalise compile_abi_encode_shape[local]


Theorem compile_encode_log_topic_shape[local]:
  !internal val_op is_bytestring.
    shape_step internal compiler_label (\st. plain_operand st val_op)
      (compile_encode_log_topic val_op is_bytestring)
      (\op st. plain_operand st op)
Proof
  rpt gen_tac >> simp[compile_encode_log_topic_def] >>
  Cases_on `is_bytestring`
  >- (simp[] >> irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st p /\ plain_operand st val_op` >>
      conj_tac
      >- (qx_gen_tac `data_ptr` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\n st. plain_operand st n /\ plain_operand st data_ptr` >>
          conj_tac
          >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
          stmt_frame_emit `\st. plain_operand st val_op`) >>
      stmt_frame_emit `\st. plain_operand st val_op`) >>
  simp[] >> irule shape_step_return >> simp[]
QED

Theorem compile_mapping_subscript_shape[local]:
  !internal base_slot key_op.
    shape_step internal compiler_label
      (\st. plain_operand st base_slot /\ plain_operand st key_op)
      (compile_mapping_subscript base_slot key_op)
      (\op st. plain_operand st op)
Proof
  rpt gen_tac >> simp[compile_mapping_subscript_def] >>
  irule shape_step_bind >>
  qexists_tac `\b st. plain_operand st b.buf_operand /\
                      (plain_operand st base_slot /\ plain_operand st key_op)` >>
  conj_tac
  >- (qx_gen_tac `buf` >> BETA_TAC >> simp[] >>
      stmt_sequence `\x st. plain_operand st buf.buf_operand /\
                               plain_operand st base_slot /\ plain_operand st key_op`
        stmt_plain_void >>
      irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st p /\
                         (plain_operand st buf.buf_operand /\ plain_operand st key_op)` >>
      conj_tac
      >- (qx_gen_tac `key_ptr` >> BETA_TAC >>
          stmt_sequence `\x st. plain_operand st key_ptr /\
                                   plain_operand st buf.buf_operand /\ plain_operand st key_op`
            stmt_plain_void >> stmt_plain_emit) >>
      stmt_frame_emit `\st. plain_operand st buf.buf_operand /\ plain_operand st key_op`) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
  simp[stmt_shape_stable_plain, shape_stable_conj] >>
  irule compile_alloc_buffer_shape
QED

Theorem compile_array_subscript_shape[local]:
  !internal base_op idx_op is_dynamic static_count ws elem_size signed_idx loc.
    loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st base_op /\ plain_operand st idx_op)
      (compile_array_subscript base_op idx_op is_dynamic static_count
         ws elem_size signed_idx (load_opc_for loc))
      (\op st. plain_operand st op)
Proof
  rpt strip_tac >> simp[compile_array_subscript_def] >>
  irule shape_step_bind >>
  qexists_tac `\n st. plain_operand st n /\
                     (plain_operand st base_op /\ plain_operand st idx_op)` >>
  conj_tac
  >- (qx_gen_tac `len` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\neg_flag st. plain_operand st neg_flag /\
        (plain_operand st len /\ plain_operand st base_op /\ plain_operand st idx_op)` >>
      conj_tac
      >- (qx_gen_tac `neg_flag` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\oob st. plain_operand st oob /\
            (plain_operand st neg_flag /\ plain_operand st base_op /\ plain_operand st idx_op)` >>
          conj_tac
          >- (qx_gen_tac `oob` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\not_oob st. plain_operand st not_oob /\
                (plain_operand st neg_flag /\ plain_operand st base_op /\ plain_operand st idx_op)` >>
              conj_tac
              >- (qx_gen_tac `not_oob` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\invalid st. plain_operand st invalid /\
                    (plain_operand st base_op /\ plain_operand st idx_op)` >>
                  conj_tac
                  >- (qx_gen_tac `invalid` >> BETA_TAC >> irule shape_step_bind >>
                      qexists_tac `\valid st. plain_operand st valid /\
                        (plain_operand st base_op /\ plain_operand st idx_op)` >>
                      conj_tac
                      >- (qx_gen_tac `valid` >> BETA_TAC >>
                          stmt_sequence `\x st. plain_operand st valid /\
                            plain_operand st base_op /\ plain_operand st idx_op`
                            stmt_plain_void >>
                          irule shape_step_bind >>
                          qexists_tac `\p st. plain_operand st p /\ plain_operand st idx_op` >>
                          conj_tac
                          >- (qx_gen_tac `data_ptr` >> BETA_TAC >>
                              irule shape_step_bind >>
                              qexists_tac `\off st. plain_operand st off /\ plain_operand st data_ptr` >>
                              conj_tac
                              >- (gen_tac >> BETA_TAC >> stmt_plain_emit) >>
                              stmt_frame_emit `\st. plain_operand st idx_op`) >>
                          IF_CASES_TAC
                          >- (simp[] >> stmt_frame_emit `\st. plain_operand st base_op`) >>
                          irule shape_step_return >> simp[]) >>
                      stmt_frame_emit `\st. plain_operand st invalid`) >>
                  stmt_frame_emit `\st. plain_operand st neg_flag /\ plain_operand st not_oob`) >>
              stmt_frame_emit `\st. plain_operand st oob`) >>
          stmt_frame_emit `\st. plain_operand st idx_op /\ plain_operand st len`) >>
      IF_CASES_TAC
      >- (stmt_frame_emit `\st. plain_operand st idx_op`) >>
      irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  IF_CASES_TAC
  >- (Cases_on `loc` >> gvs[load_opc_for_def] >>
      stmt_frame_emit `\st. plain_operand st base_op`) >>
  irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_dynarray_append_shape:
  !cenv base_op val_op ws elem_size dst_ty src_ty capacity is_prim loc internal.
    loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st base_op /\ plain_operand st val_op)
      (compile_dynarray_append cenv base_op val_op ws elem_size dst_ty src_ty
         capacity is_prim (load_opc_for loc) (store_opc_for loc)) (\u st. T)
Proof
  rpt strip_tac >> simp[compile_dynarray_append_def] >>
  irule shape_step_bind >>
  qexists_tac `\n st. plain_operand st n /\
                     (plain_operand st base_op /\ plain_operand st val_op)` >>
  conj_tac
  >- (qx_gen_tac `len` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\valid st. plain_operand st valid /\
        (plain_operand st len /\ plain_operand st base_op /\ plain_operand st val_op)` >>
      conj_tac
      >- (qx_gen_tac `valid` >> BETA_TAC >>
          stmt_sequence `\u st. plain_operand st valid /\ plain_operand st len /\
            plain_operand st base_op /\ plain_operand st val_op` stmt_plain_void >>
          irule shape_step_bind >>
          qexists_tac `\p st. plain_operand st p /\
            (plain_operand st len /\ plain_operand st base_op /\ plain_operand st val_op)` >>
          conj_tac
          >- (qx_gen_tac `data_ptr` >> BETA_TAC >> irule shape_step_bind >>
              qexists_tac `\off st. plain_operand st off /\
                (plain_operand st data_ptr /\ plain_operand st len /\
                 plain_operand st base_op /\ plain_operand st val_op)` >>
              conj_tac
              >- (qx_gen_tac `offset` >> BETA_TAC >> irule shape_step_bind >>
                  qexists_tac `\p st. plain_operand st p /\
                    (plain_operand st len /\ plain_operand st base_op /\ plain_operand st val_op)` >>
                  conj_tac
                  >- suspend "store_and_length" >>
                  stmt_frame_emit `\st. plain_operand st data_ptr /\ plain_operand st offset`) >>
              stmt_frame_emit `\st. plain_operand st len`) >>
          stmt_frame_emit `\st. plain_operand st base_op`) >>
      stmt_frame_emit `\st. plain_operand st len`) >>
  Cases_on `loc` >> gvs[load_opc_for_def] >>
  stmt_frame_emit `\st. plain_operand st base_op`
QED

Resume compile_dynarray_append_shape[store_and_length]:
  qx_gen_tac `elem_ptr` >> BETA_TAC >>
  stmt_sequence `\u st. plain_operand st len /\ plain_operand st base_op`
    (suspend "store_element") >>
  irule shape_step_bind >>
  qexists_tac `\n st. plain_operand st n /\ plain_operand st base_op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> Cases_on `loc` >> gvs[store_opc_for_def] >>
      stmt_plain_void_drop) >>
  stmt_frame_emit `\st. plain_operand st len`
QED

Resume compile_dynarray_append_shape[store_element]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st elem_ptr /\ plain_operand st len /\
          plain_operand st base_op /\ plain_operand st val_op`,
    `\u st. T /\ (plain_operand st len /\ plain_operand st base_op)`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st elem_ptr /\ plain_operand st val_op` >>
  simp[stmt_shape_stable_plain, shape_stable_conj] >>
  IF_CASES_TAC
  >- (Cases_on `loc` >> gvs[store_opc_for_def] >> stmt_plain_void_drop) >>
  Cases_on `loc` >> gvs[store_opc_for_def] >>
  (stmt_sequence `\u st. T`
    (FIRST [irule compile_store_memory_shape,
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st val_op /\ plain_operand st elem_ptr`, `\u st. T`] >>
      simp[] >> irule compile_word_copy_loop_noncode_shape >> simp[]]) >>
   irule shape_step_return >> simp[])
QED
Finalise compile_dynarray_append_shape[local]

Theorem compile_target_base_shape[local]:
  !bt cenv st. cenv_shape_ok st cenv ==>
    plain_operand st (compile_target_base cenv bt)
Proof
  Induct >> simp[compile_target_base_def] >> rpt strip_tac >>
  BasicProvers.TOP_CASE_TAC >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  rename1 `FLOOKUP _ _ = SOME vloc` >>
  `loc_shape_ok st vloc` by metis_tac[cenv_shape_ok_lookup] >>
  Cases_on `vloc` >> gvs[loc_shape_ok_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Theorem stmt_return_bind[local]:
  comp_bind (comp_return x) f = f x
Proof
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem shape_step_frame_from[local]:
  !R internal P m Q PP QQ.
    shape_stable R /\ shape_step internal compiler_label P m Q /\
    (!st. PP st ==> R st /\ P st) /\ (!x st. R st /\ Q x st ==> QQ x st) ==>
    shape_step internal compiler_label PP m QQ
Proof
  rpt strip_tac >> drule_all shape_step_frame >> strip_tac >>
  irule shape_step_conseq >> pop_assum (irule_at Any) >> gvs[]
QED

(* A framed form of a generator lemma proved above, for the expression
   cases, which carry a stable frame R through each step. *)
fun shape_framed_tac th =
  rpt strip_tac >> irule shape_step_frame_from >> irule_at Any th >>
  qexists_tac `R` >> gvs[];

Theorem expr_shape_list_member[local]:
  ~supported_exprs_exists p es /\ MEM e es ==>
  ~supported_expr_exists p e
Proof
  simp[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]
QED

Theorem expr_shape_list_el[local]:
  ~supported_exprs_exists p es /\ n < LENGTH es ==>
  ~supported_expr_exists p (EL n es)
Proof
  strip_tac >> irule expr_shape_list_member >>
  qexists_tac `es` >> simp[EL_MEM]
QED

Theorem expr_shape_list_hd[local]:
  ~supported_exprs_exists p es /\ 0 < LENGTH es ==>
  ~supported_expr_exists p (HD es)
Proof
  Cases_on `es` >> simp[supported_expr_exists_def]
QED

Theorem expr_shape_builtin[local]:
  ~supported_expr_exists expr_shape_root (Builtin ann bi es) <=>
  bi <> Env MsgGas /\ builtin_arity bi <= LENGTH es /\
  ~supported_exprs_exists expr_shape_root es
Proof
  simp[supported_expr_exists_def, expr_shape_root_def, arithmeticTheory.NOT_LESS, CONJ_ASSOC]
QED

Theorem expr_shape_type_builtin[local]:
  ~supported_expr_exists expr_shape_root (TypeBuiltin ann tb target es) <=>
  type_builtin_arity tb <= LENGTH es /\
  ~supported_exprs_exists expr_shape_root es
Proof
  simp[supported_expr_exists_def, expr_shape_root_def, arithmeticTheory.NOT_LESS]
QED

Theorem expr_shape_extcode_addr[local]:
  ~supported_expr_exists p e /\ is_extcode e ==>
  ~supported_expr_exists p (extcode_addr_expr e)
Proof
  qid_spec_tac `e` >> recInduct is_extcode_ind >>
  simp[is_extcode_def, extcode_addr_expr_def, supported_expr_exists_def] >>
  rpt strip_tac
  >- (rename1 `~p (Attribute ann addr (STRING #"c" (STRING #"o" (STRING #"d" (STRING #"e" tail)))))` >>
      Cases_on `tail` >> gvs[])
  >- (rename1 `~p (Attribute ann addr (STRING #"c" (STRING #"o" (STRING #"d" tail))))` >>
      Cases_on `tail` >> gvs[] >>
      BasicProvers.FULL_CASE_TAC >> gvs[])
  >- (rename1 `~p (Attribute ann addr (STRING #"c" (STRING #"o" tail)))` >>
      Cases_on `tail` >> gvs[] >>
      BasicProvers.FULL_CASE_TAC >> gvs[] >>
      BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rename1 `~p (Attribute ann addr (STRING #"c" tail))` >>
  Cases_on `tail` >> gvs[] >>
  BasicProvers.FULL_CASE_TAC >> gvs[] >>
  BasicProvers.FULL_CASE_TAC >> gvs[] >>
  BasicProvers.FULL_CASE_TAC >> gvs[]
QED

Theorem shape_step_uncurry[local]:
  shape_step internal LP P m Q /\
  (!x. shape_step internal LP (Q x) (k x) R) ==>
  shape_step internal LP P (\st. UNCURRY k (m st)) R
Proof
  strip_tac >>
  ` (\st. UNCURRY k (m st)) = comp_bind m k` by
    (simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
     Cases_on `m st` >> simp[]) >>
  pop_assum SUBST1_TAC >> match_mp_tac shape_step_bind >>
  qexists_tac `Q` >> simp[]
QED

Theorem invalid_expr_call_shape[local]:
  shape_step internal compiler_label (\st. T) (invalid_expr_call ty)
    (\v st. value_shape_ok st v)
Proof
  `invalid_expr_call ty = comp_ignore_bind (emit_inst INVALID [] [])
      (comp_return (StackValue ty (Lit 0w)))` by
    (simp[FUN_EQ_THM, exprCallBoundsTheory.invalid_expr_call_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def] >> gen_tac >>
     Cases_on `emit_inst INVALID [] [] st` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\x st. T` >>
  conj_tac
  >- (mp_tac (Q.SPECL [`internal`, `compiler_label`, `\st. T`,
                       `INVALID`, `[]`, `[]`] shape_step_emit_inst) >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
           inst_jump_labels_ok_def,
           is_terminator_def, is_param_opcode_def]) >>
  gen_tac >> irule shape_step_return >>
  simp[value_shape_ok_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem expr_child_callback_shape[local]:
  (!ce t e internal.
     expr_size e < bound /\ ~supported_expr_exists expr_shape_root e ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (f ce t e) (\v st. value_shape_ok st v)) ==>
  !ce t e internal.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st ce)
      (expr_child_callback bound f ce t e) (\v st. value_shape_ok st v)
Proof
  rpt strip_tac >>
  `expr_child_callback bound f ce t e =
     if expr_size e < bound then f ce t e
     else invalid_expr_call (expr_type e)` by
    (Cases_on `expr_size e < bound` >>
     simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def]) >>
  pop_assum SUBST1_TAC >> Cases_on `expr_size e < bound` >> simp[] >>
  match_mp_tac shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. T`, `\v st. value_shape_ok st v`] >>
  simp[invalid_expr_call_shape]
QED

Theorem builtin_child_callback_shape[local]:
  (!ce rt t bi args internal.
     list_size expr_size args < bound /\ bi <> Env MsgGas /\
     builtin_arity bi <= LENGTH args /\
     ~supported_exprs_exists expr_shape_root args ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (f ce rt t bi args) (\v st. value_shape_ok st v)) ==>
  !ce rt t bi args internal.
    bi <> Env MsgGas /\ builtin_arity bi <= LENGTH args /\
    ~supported_exprs_exists expr_shape_root args ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st ce)
      (builtin_child_callback bound f ce rt t bi args)
      (\v st. value_shape_ok st v)
Proof
  rpt strip_tac >>
  `builtin_child_callback bound f ce rt t bi args =
     if list_size expr_size args < bound then f ce rt t bi args
     else invalid_expr_call rt` by
    (Cases_on `list_size expr_size args < bound` >>
     simp[FUN_EQ_THM, exprCallBoundsTheory.builtin_child_callback_def]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `list_size expr_size args < bound` >> simp[] >>
  match_mp_tac shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. T`, `\v st. value_shape_ok st v`] >>
  simp[invalid_expr_call_shape]
QED

Theorem type_child_callback_shape[local]:
  (!ce vt t tb rt args internal.
     list_size expr_size args < bound /\
     type_builtin_arity tb <= LENGTH args /\
     ~supported_exprs_exists expr_shape_root args ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (f ce vt t tb rt args) (\v st. value_shape_ok st v)) ==>
  !ce vt t tb rt args internal.
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists expr_shape_root args ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st ce)
      (type_child_callback bound f ce vt t tb rt args)
      (\v st. value_shape_ok st v)
Proof
  rpt strip_tac >>
  `type_child_callback bound f ce vt t tb rt args =
     if list_size expr_size args < bound then f ce vt t tb rt args
     else invalid_expr_call vt` by
    (Cases_on `list_size expr_size args < bound` >>
     simp[FUN_EQ_THM, exprCallBoundsTheory.type_child_callback_def]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `list_size expr_size args < bound` >> simp[] >>
  match_mp_tac shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. T`, `\v st. value_shape_ok st v`] >>
  simp[invalid_expr_call_shape]
QED

Theorem shape_step_emit_op_plain[local]:
  !internal R opc ops.
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
  (!st id outs. R st /\ EVERY (plain_operand st) ops ==>
     lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) ops) (emit_op opc ops)
    (\v st. R st /\ plain_operand st v)
Proof
  rpt gen_tac >> strip_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`internal`, `compiler_label`, `R`, `opc`, `ops`]
                  shape_step_emit_op) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[shape_step_def] >> disch_then irule >>
  simp[] >> gvs[EVERY_MEM, label_or_plain_def]
QED

Theorem shape_step_emit_inst_guarded_framed[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
  (!st id. R st /\ EVERY (label_or_plain st) ops ==>
     lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (label_or_plain st) ops) (emit_inst opc ops outs)
    (\v st. R st)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_emit_inst_guarded >>
  qexists_tac `\st. R st /\ EVERY (label_or_plain st) ops` >>
  qexists_tac `compiler_label` >> simp[] >> conj_tac
  >- (ho_match_mp_tac shape_stable_conj >> simp[shape_stable_label_or_plains]) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `st` >> simp[]
QED

Theorem shape_step_emit_void_plain[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
  (!st id. R st /\ EVERY (plain_operand st) ops ==>
     lowered_inst_ok internal (mk_inst id opc ops [])) ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) ops) (emit_void opc ops)
    (\v st. R st)
Proof
  `emit_void opc ops = emit_inst opc ops []` by
    simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  pop_assum SUBST1_TAC >> strip_tac >>
  irule shape_step_conseq >>
  irule_at Any shape_step_emit_inst_guarded_framed >>
  qexists_tac `\st. R st /\ EVERY (plain_operand st) ops` >>
  conj_tac
  >- (ho_match_mp_tac shape_stable_conj >>
      simp[shape_stable_plain_operands]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  simp[EVERY_MEM, label_or_plain_def]
QED

Theorem compile_alloc_buffer_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_alloc_buffer nbytes)
    (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  shape_framed_tac compile_alloc_buffer_shape
QED

Theorem compile_ptr_load_shape_framed[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st op)
    (compile_ptr_load is_ctor loc op)
    (\v st. R st /\ plain_operand st v)
Proof
  shape_framed_tac compile_ptr_load_shape
QED

(* Consequence adaptation is shared by plain-operand primitive consumers. *)
val shape_opcode_tac =
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, inst_jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
       plain_operand_def, label_or_plain_def,
       stackPlanTypesTheory.is_label_operand_def];

fun shape_under_tac rule frame =
  irule shape_step_conseq >>
  irule_at Any rule >>
  qexists_tac frame >> simp[];

Theorem compile_store_bytestring_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst_op /\ plain_operand st val_op)
    (compile_store_bytestring val_op dst_op) (\u st. R st)
Proof
  shape_framed_tac compile_store_bytestring_shape
QED

Theorem compile_ensure_in_memory_shape_framed[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st ptr_op)
    (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor)
    (\op st. R st /\ plain_operand st op)
Proof
  shape_framed_tac compile_ensure_in_memory_shape
QED

Theorem compile_store_memory_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st src /\ plain_operand st dst)
    (compile_store_memory cenv src dst dst_ty src_ty) (\u st. R st)
Proof
  shape_framed_tac compile_store_memory_shape
QED

Theorem compile_bytelike_literal_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_bytelike_literal bs max_len)
    (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  shape_framed_tac compile_bytelike_literal_shape
QED

val shape_name_invalid_tac =
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. T` >>
      simp[shape_stable_def] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def];

Theorem compile_name_vv_shape[local]:
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_name_vv cenv ty id) (\v st. value_shape_ok st v)
Proof
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[compile_name_vv_def]
  >- shape_name_invalid_tac >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[]
  >- (irule shape_step_return >>
      simp[value_shape_ok_def, mk_ptr_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def])
  >- shape_name_invalid_tac
  >- shape_name_invalid_tac
  >- shape_name_invalid_tac >>
  irule shape_step_return >>
  simp[value_shape_ok_def, mk_ptr_def] >> rpt strip_tac >>
  gvs[cenv_shape_ok_def] >> first_x_assum drule >> simp[loc_shape_ok_def]
QED

val shape_literal_return_tac =
  irule shape_step_return >>
  simp[value_shape_ok_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def];

val shape_literal_buffer_tac =
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. R st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_bytelike_literal_shape_framed >> simp[]) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, base_ptr_def];

Theorem compile_literal_vv_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_literal_vv ty lit)
    (\v st. R st /\ value_shape_ok st v)
Proof
  strip_tac >> Cases_on `lit`
  >~ [`compile_literal_vv ty (BoolL b)`]
  >- (Cases_on `b` >> simp[compile_literal_vv_def] >> shape_literal_return_tac)
  >~ [`compile_literal_vv ty (StringL s)`]
  >- (simp[compile_literal_vv_def] >> shape_literal_buffer_tac)
  >~ [`compile_literal_vv ty (IntL n)`]
  >- (simp[compile_literal_vv_def] >> shape_literal_return_tac)
  >~ [`compile_literal_vv ty (DecimalL n)`]
  >- (simp[compile_literal_vv_def] >> shape_literal_return_tac) >>
  Cases_on `ty` >> simp[compile_literal_vv_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
      FIRST [shape_literal_return_tac, shape_literal_buffer_tac]) >>
  shape_literal_return_tac
QED

Theorem compile_env_var_shape[local]:
  shape_stable R /\ item <> MsgGas ==>
  shape_step internal compiler_label R (compile_env_var item)
    (\op st. R st /\ plain_operand st op)
Proof
  strip_tac >> Cases_on `item` >> gvs[compile_env_var_def]
  >~ [`comp_bind (emit_op NUMBER []) _`]
  >- (match_mp_tac shape_step_bind >>
      qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >>
      shape_opcode_tac) >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

(* Fixed straight-line scalar sequences share only monadic plumbing. *)
fun shape_scalar_emit_bind_tac frame name normalize =
  match_mp_tac shape_step_bind >>
  qexists_tac ([QUOTE "\\v st. ("] @ frame @
               [QUOTE ") st /\\ plain_operand st v"]) >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain frame >> normalize >> shape_opcode_tac) >>
  qx_gen_tac name >> simp[];

fun shape_scalar_assert_tac frame =
  match_mp_tac shape_step_ignore_bind >> qexists_tac ([QUOTE "\\u st. ("] @ frame @ [QUOTE ") st"]) >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain frame >> shape_opcode_tac) >>
  gen_tac >> simp[];

Theorem compile_select_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [cond_op;then_op;else_op])
    (compile_select cond_op then_op else_op) (\v st. R st /\ plain_operand st v)
Proof
  shape_framed_tac compile_select_shape
QED

Theorem compile_neg_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_neg v ty) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> Cases_on `type_bounds ty` >> simp[compile_neg_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `P`]) >>
  shape_scalar_assert_tac `P` >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_invert_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_invert v ty cenv) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_invert_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_binop_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_binop op x y ty base_literal exp_literal) (\v st. R st /\ plain_operand st v)
Proof
  shape_framed_tac compile_binop_shape
QED

Theorem load_bytestring_as_word_shape[local]:
  shape_stable R /\ MEM shift_opc [SAR;SHR] ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (load_bytestring_as_word v shift_opc)
    (\p st. R st /\ plain_operand st (FST p) /\ plain_operand st (SND p))
Proof
  strip_tac >> simp[load_bytestring_as_word_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `L` `data_ptr` (simp[Abbr `L`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `L` `data_op` all_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `sub32` (simp[Abbr `D`, Abbr `L`]) >>
  shape_scalar_emit_bind_tac `D` `zero_bits` all_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[zero_bits]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. G st /\ plain_operand st op` >> conj_tac
  >- (gvs[] >> shape_under_tac shape_step_emit_op_plain `G` >>
      simp[Abbr `G`, Abbr `D`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[Abbr `G`, Abbr `D`, Abbr `L`, Abbr `P`]
QED

val shape_convert_return_tac =
  irule shape_step_return >> simp[Abbr `P`];

val shape_convert_upper_tac =
  shape_scalar_emit_bind_tac `P` `too_big` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `P`]) >>
  shape_scalar_assert_tac `P` >> shape_convert_return_tac;

val shape_convert_two_bounds_tac =
  shape_scalar_emit_bind_tac `P` `first_cmp` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `first_ok` all_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[first_ok]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `second_cmp` (simp[Abbr `G`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `G` `second_ok` all_tac >>
  shape_scalar_emit_bind_tac `P` `both_ok` (simp[Abbr `G`]) >>
  shape_scalar_assert_tac `P` >> shape_convert_return_tac;

Theorem compile_type_convert_shape:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_type_convert v conv_op) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `conv_op`
  >~ [`compile_type_convert v ConvToBool`]
  >- (simp[compile_type_convert_def] >>
      shape_scalar_emit_bind_tac `R` `z` (simp[Abbr `P`]) >>
      shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac)
  >~ [`compile_type_convert v ConvIdentity`]
  >- (simp[compile_type_convert_def] >> shape_convert_return_tac)
  >~ [`compile_type_convert v (ConvBoolToDecimal divisor)`]
  >- (simp[compile_type_convert_def] >> shape_under_tac shape_step_emit_op_plain `R` >>
      simp[Abbr `P`] >> shape_opcode_tac)
  >~ [`compile_type_convert v ConvToAddress`]
  >- (simp[compile_type_convert_def] >> shape_convert_upper_tac)
  >~ [`compile_type_convert v (ConvToFlag n_members)`]
  >- (simp[compile_type_convert_def] >>
      shape_scalar_emit_bind_tac `P` `inv_op` all_tac >>
      shape_scalar_emit_bind_tac `P` `extra_op` (simp[Abbr `P`]) >>
      shape_scalar_emit_bind_tac `P` `ok_op` all_tac >>
      shape_scalar_assert_tac `P` >> shape_convert_return_tac)
  >~ [`compile_type_convert v (ConvBytestringCast max_len)`]
  >- (simp[compile_type_convert_def] >>
      shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`]) >> shape_convert_upper_tac)
  >~ [`compile_type_convert v (ConvIntToInt in_s in_b out_s out_b)`]
  >- suspend "int_int"
  >~ [`compile_type_convert v (ConvBytesToInt m out_s out_b)`]
  >- suspend "bytes_int"
  >~ [`compile_type_convert v (ConvIntToBytesM in_s in_b m)`]
  >- suspend "int_bytes"
  >~ [`compile_type_convert v (ConvIntToDecimal in_s in_b divisor out_lo out_hi)`]
  >- suspend "int_decimal"
  >~ [`compile_type_convert v (ConvDecimalToInt divisor in_lo in_hi out_lo out_hi in_s)`]
  >- suspend "decimal_int"
  >~ [`compile_type_convert v (ConvBytesToAddress m)`]
  >- suspend "bytes_address"
  >~ [`compile_type_convert v (ConvBytesMToDecimal m divisor out_lo out_hi)`]
  >- suspend "bytes_decimal"
  >~ [`compile_type_convert v (ConvBytesMToBytesM in_m out_m)`]
  >- (simp[compile_type_convert_def] >> Cases_on `out_m < in_m` >> simp[]
      >- shape_convert_upper_tac >> shape_convert_return_tac)
  >~ [`compile_type_convert v ConvBytestringToBool`]
  >- suspend "bs_bool"
  >~ [`compile_type_convert v (ConvBytestringToInt is_signed out_b)`]
  >- suspend "bs_int"
  >~ [`compile_type_convert v ConvBytestringToAddress`]
  >- suspend "bs_address"
  >~ [`compile_type_convert v (ConvBytestringToDecimal divisor out_lo out_hi)`]
  >- suspend "bs_decimal"
  >~ [`compile_type_convert v (ConvBytestringToBytesM out_m)`]
  >- suspend "bs_bytes" >>
  suspend "fixed_bs"
QED

Resume compile_type_convert_shape[int_int]:
  Cases_on `in_s` >> Cases_on `out_s` >> simp[compile_type_convert_def]
  >- (Cases_on `out_b < in_b` >> simp[]
      >- shape_convert_two_bounds_tac >> shape_convert_return_tac)
  >- (Cases_on `out_b < in_b` >> simp[]
      >- shape_convert_two_bounds_tac >> shape_convert_upper_tac)
  >- shape_convert_upper_tac >>
  Cases_on `out_b < in_b` >> simp[]
  >- shape_convert_upper_tac >> shape_convert_return_tac
QED

fun shape_convert_reframe_tac ops =
  qpat_x_assum `shape_stable P` kall_tac >>
  qpat_x_assum `Abbrev (P = _)` kall_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC ops shape_stable_plain_operands) >> simp[]);

fun shape_convert_shift_clamp_tac clamp_tac =
  shape_scalar_emit_bind_tac `R` `shifted` (simp[Abbr `P`]) >>
  shape_convert_reframe_tac `[shifted]:operand list` >>
  IF_CASES_TAC >> simp[] >- clamp_tac >> shape_convert_return_tac;

Resume compile_type_convert_shape[bytes_int]:
  Cases_on `out_s` >> simp[compile_type_convert_def]
  >- shape_convert_shift_clamp_tac shape_convert_two_bounds_tac >>
  shape_convert_shift_clamp_tac shape_convert_upper_tac
QED

Resume compile_type_convert_shape[int_bytes]:
  simp[compile_type_convert_def] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
  >- (Cases_on `8 * m < in_b` >> simp[]
      >- (Cases_on `in_s` >> simp[] >> shape_convert_upper_tac) >>
      shape_convert_return_tac) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

val shape_convert_optional_bound_tac =
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (shape_scalar_emit_bind_tac `P` `cmp_op` (simp[Abbr `P`]) >>
          shape_scalar_emit_bind_tac `P` `ok_op` all_tac >>
          shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[];

val shape_convert_decimal_tac =
  shape_convert_optional_bound_tac >> shape_convert_optional_bound_tac >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac;

Resume compile_type_convert_shape[int_decimal]:
  Cases_on `in_s` >> simp[compile_type_convert_def] >> shape_convert_decimal_tac
QED

Resume compile_type_convert_shape[decimal_int]:
  Cases_on `in_s` >> simp[compile_type_convert_def] >> shape_convert_decimal_tac
QED

Resume compile_type_convert_shape[bytes_address]:
  simp[compile_type_convert_def] >> shape_convert_shift_clamp_tac shape_convert_upper_tac
QED

Resume compile_type_convert_shape[bytes_decimal]:
  simp[compile_type_convert_def] >> shape_convert_shift_clamp_tac shape_convert_two_bounds_tac
QED

val shape_convert_load_word_tac =
  match_mp_tac shape_step_bind >>
  qexists_tac `\p st. R st /\ plain_operand st (FST p) /\ plain_operand st (SND p)` >> conj_tac
  >- (shape_under_tac load_bytestring_as_word_shape `R` >> simp[Abbr `P`]) >>
  qx_gen_tac `pair_ops` >> PairCases_on `pair_ops` >> simp[] >>
  rename1 `\st. R st /\ plain_operand st shifted /\ plain_operand st zero_bits` >>
  shape_convert_reframe_tac `[shifted;zero_bits]:operand list`;

Resume compile_type_convert_shape[bs_bool]:
  simp[compile_type_convert_def] >> shape_convert_load_word_tac >>
  shape_scalar_emit_bind_tac `R` `z` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Resume compile_type_convert_shape[bs_int]:
  Cases_on `is_signed` >> simp[compile_type_convert_def] >>
  shape_convert_load_word_tac >>
  Cases_on `256 <= out_b` >> simp[]
  >- shape_convert_return_tac
  >- shape_convert_upper_tac
  >- shape_convert_return_tac >>
  shape_convert_upper_tac
QED

Resume compile_type_convert_shape[bs_address]:
  simp[compile_type_convert_def] >> shape_convert_load_word_tac >> shape_convert_upper_tac
QED

Resume compile_type_convert_shape[bs_decimal]:
  simp[compile_type_convert_def] >> shape_convert_load_word_tac >> shape_convert_two_bounds_tac
QED

Resume compile_type_convert_shape[bs_bytes]:
  simp[compile_type_convert_def] >> shape_convert_load_word_tac >>
  shape_scalar_emit_bind_tac `R` `shifted_l` (simp[Abbr `P`]) >>
  shape_convert_reframe_tac `[shifted_l]:operand list` >> shape_convert_upper_tac
QED

Resume compile_type_convert_shape[fixed_bs]:
  simp[compile_type_convert_def] >> match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. P st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `G` >> simp[Abbr `G`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `G` `data_ptr` (simp[Abbr `G`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `G` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `G`, Abbr `P`]
QED

Finalise compile_type_convert_shape[local]

Theorem compile_builtin_abs_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_builtin_abs v) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[builtinSimpleTheory.compile_builtin_abs_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `neg_v` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[neg_v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `negative_op` (simp[Abbr `G`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label H _ _` >>
  `shape_stable H` by
    (simp[Abbr `H`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[negative_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `H` `min_op` (simp[Abbr `H`, Abbr `G`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `H` `bad` (simp[Abbr `H`]) >>
  shape_scalar_emit_bind_tac `H` `ok_op` all_tac >>
  shape_scalar_assert_tac `H` >>
  shape_under_tac compile_select_shape_framed `R` >> simp[Abbr `H`, Abbr `G`, Abbr `P`]
QED

(* Decimal rounding differs only in its two fixed arithmetic opcodes. *)
fun shape_round_decimal_tac def =
  strip_tac >> simp[def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `sign_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[sign_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `adjusted` (simp[Abbr `G`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\w st. R st /\ plain_operand st w` >> conj_tac
  >- (shape_under_tac compile_select_shape_framed `R` >> simp[Abbr `G`, Abbr `P`]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac;

Theorem compile_floor_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_floor v divisor) (\w st. R st /\ plain_operand st w)
Proof
  shape_round_decimal_tac builtinMiscTheory.compile_floor_def
QED

Theorem compile_ceil_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_ceil v divisor) (\w st. R st /\ plain_operand st w)
Proof
  shape_round_decimal_tac builtinMiscTheory.compile_ceil_def
QED

Theorem compile_as_wei_value_decimal_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_as_wei_value_decimal v scale divisor) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `negative_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` all_tac >>
  shape_scalar_assert_tac `P` >>
  Cases_on `scale = 1` >> simp[]
  >- (shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  shape_scalar_emit_bind_tac `R` `product` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_as_wei_value_int_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_as_wei_value_int v scale signed) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_as_wei_value_int_def] >>
  Cases_on `scale = 1` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `product` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[product]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `quotient` (simp[Abbr `G`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `G` `safe_op` all_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label H _ _` >>
  `shape_stable H` by
    (simp[Abbr `H`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[safe_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `H` `zero_op` (simp[Abbr `H`, Abbr `G`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `G` `ok_op` (simp[Abbr `H`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\w st. G st /\ plain_operand st w` >> conj_tac
  >- (Cases_on `signed` >> simp[]
      >- (qmatch_goalsub_abbrev_tac `shape_step internal compiler_label J _ _` >>
          `shape_stable J` by
            (simp[Abbr `J`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
             mp_tac (Q.SPEC `[ok_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
          shape_scalar_emit_bind_tac `J` `negative_op` (simp[Abbr `J`, Abbr `G`, Abbr `P`]) >>
          shape_scalar_emit_bind_tac `J` `not_negative` all_tac >>
          shape_under_tac shape_step_emit_op_plain `G` >> simp[Abbr `J`] >> shape_opcode_tac) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >> shape_scalar_assert_tac `G` >>
  irule shape_step_return >> simp[Abbr `G`, Abbr `P`]
QED

Theorem compile_clamp_extract32_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_clamp_extract32 v clamp) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> Cases_on `clamp` >> simp[builtinBytesTheory.compile_clamp_extract32_def]
  >- (irule shape_step_return >> simp[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `bound_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `P`]) >>
  shape_scalar_assert_tac `P` >>
  irule shape_step_return >> simp[Abbr `P`]
QED

Theorem compile_builtin_len_shape[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st ptr_op)
    (compile_builtin_len is_ctor ptr_op loc) (\v st. R st /\ plain_operand st v)
Proof
  simp[builtinSimpleTheory.compile_builtin_len_def, compile_ptr_load_shape_framed]
QED

Theorem compile_builtin_calldatasize_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R compile_builtin_calldatasize
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinSimpleTheory.compile_builtin_calldatasize_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_zero_words_shape[local]:
  !n R base. shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st base)
    (compile_zero_words base n) (\u st. R st /\ plain_operand st base)
Proof
  Induct >> qx_gen_tac `R` >> qx_gen_tac `base_op` >> strip_tac >>
  simp[builtinSimpleTheory.compile_zero_words_def]
  >- (irule shape_step_return >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st base_op` >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  gen_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[base_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `dst` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac
QED

Theorem compile_builtin_empty_complex_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_builtin_empty_complex nbytes is_bs)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinSimpleTheory.compile_builtin_empty_complex_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. R st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (irule compile_alloc_buffer_shape_framed >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `buf_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `is_bs` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac)
  >- (gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `P`])
  >- (simp[Abbr `P`] >> irule compile_zero_words_shape >> simp[]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `P`]
QED

Theorem compile_keccak256_bytes_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_keccak256_bytes v) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[builtinHashingTheory.compile_keccak256_bytes_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `data_op` (simp[Abbr `G`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac
QED

(* The word/bytesM Keccak routines share the same staging sequence. *)
fun shape_keccak_staged_tac def =
  strip_tac >> simp[def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. P st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >>
  qx_gen_tac `buf` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\w st. P st /\ plain_operand st w` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `buf_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `G` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac;

Theorem compile_keccak256_word_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_keccak256_word v) (\w st. R st /\ plain_operand st w)
Proof
  shape_keccak_staged_tac builtinHashingTheory.compile_keccak256_word_def
QED

Theorem compile_keccak256_bytesm_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_keccak256_bytesm v m) (\w st. R st /\ plain_operand st w)
Proof
  shape_keccak_staged_tac builtinHashingTheory.compile_keccak256_bytesm_def
QED

Theorem compile_method_id_hash_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_method_id_hash ty v) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> Cases_on `?m. ty = BaseT (BytesT (Fixed m))`
  >- (gvs[builtinHashingTheory.compile_method_id_hash_def] >>
      irule compile_keccak256_bytesm_shape >> simp[]) >>
  `compile_method_id_hash ty v = compile_keccak256_bytes v` by
    (Cases_on `ty` >> simp[builtinHashingTheory.compile_method_id_hash_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[builtinHashingTheory.compile_method_id_hash_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[builtinHashingTheory.compile_method_id_hash_def]) >>
  simp[] >> irule compile_keccak256_bytes_shape >> simp[]
QED

Theorem compile_method_id_runtime_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_method_id_runtime ty v b) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[builtinHashingTheory.compile_method_id_runtime_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\w st. R st /\ plain_operand st w` >> conj_tac
  >- (irule compile_method_id_hash_shape >> simp[]) >>
  qx_gen_tac `hash_op` >> simp[] >>
  shape_scalar_emit_bind_tac `R` `sel_op` all_tac >>
  shape_scalar_emit_bind_tac `R` `word_op` all_tac >>
  qabbrev_tac `WordFrame = \st. R st /\ plain_operand st word_op` >>
  `shape_stable WordFrame` by
    (simp[Abbr `WordFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[word_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `b` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. WordFrame st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `WordFrame` >> simp[Abbr `WordFrame`]) >>
  qx_gen_tac `buf` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\w st. WordFrame st /\ plain_operand st w` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `buf_op` >> simp[] >>
  qabbrev_tac `BufFrame = \st. WordFrame st /\ plain_operand st buf_op` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `BufFrame` `data_ptr` (simp[Abbr `BufFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`, Abbr `WordFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `BufFrame`, Abbr `WordFrame`]
QED

(* ABI validators preserve the value whose canonical form they check. *)
val shape_abi_scalar_clamp_tac =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `canonical_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac;

Theorem compile_abi_int_clamp_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_int_clamp v bits signed) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `signed` >> simp[abiEncoderTheory.compile_abi_int_clamp_def] >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_abi_bytes_clamp_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_bytes_clamp v m) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_abi_bytes_clamp_def] >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_abi_clamp_basetype_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_clamp_basetype v clamp) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `clamp` >>
  simp[abiEncoderTheory.compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_shape_framed, compile_abi_bytes_clamp_shape_framed]
  >- (irule shape_step_return >> simp[]) >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_abi_encode_shape_framed[local]:
  (!dst child_ptr info is_dyn static_ofst dyn_ptr.
    !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;child_ptr;dyn_ptr])
      (compile_abi_encode_child dst child_ptr info is_dyn static_ofst dyn_ptr)
      (\v st. R st /\ plain_operand st v)) /\
  (!dst src info. !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src])
      (compile_abi_encode_to_buf dst src info)
      (\v st. R st /\ plain_operand st v)) /\
  (!dst src elems src_ofst head_ofst dyn_ptr.
    !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src;dyn_ptr])
      (compile_abi_encode_complex_elems dst src elems src_ofst head_ofst dyn_ptr)
      (\v st. R st /\ plain_operand st v)) /\
  (!dst src info abi_sz mem_sz len_op.
    !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src;len_op])
      (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op)
      (\v st. R st /\ plain_operand st v))
Proof
  rpt conj_tac >| map shape_framed_tac (CONJUNCTS compile_abi_encode_shape)
QED

Theorem lower_abi_encode_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st src_op)
    (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinAbiTheory.lower_abi_encode_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[]) >>
  qx_gen_tac `out_buf` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. v = out_buf.buf_operand /\ (P st /\ plain_operand st v)` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `buf_op` >> simp[] >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label BufFrame _ _` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `BufFrame` `data_op` (simp[Abbr `BufFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label DataFrame _ _` >>
  `shape_stable DataFrame` by
    (simp[Abbr `DataFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. DataFrame st` >> conj_tac
  >- (Cases_on `method_id_opt` >> simp[]
      >- (irule shape_step_return >> simp[]) >>
      shape_scalar_emit_bind_tac `DataFrame` `mid_op` (simp[Abbr `DataFrame`, Abbr `BufFrame`]) >>
      shape_under_tac shape_step_emit_void_plain `DataFrame` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. BufFrame st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac (cj 2 compile_abi_encode_shape_framed) `BufFrame` >> simp[Abbr `DataFrame`, Abbr `BufFrame`, Abbr `P`]) >>
  qx_gen_tac `encoded_len` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (Cases_on `method_id_opt` >> simp[]
      >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
      shape_scalar_emit_bind_tac `BufFrame` `total_len` all_tac >>
      shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `BufFrame`, Abbr `P`]
QED

Theorem compile_getelemptr_abi_shape_mload[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st src_op)
    (compile_getelemptr_abi src_op is_dyn abi_offset MLOAD)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_getelemptr_abi_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `head_op` (simp[Abbr `P`]) >>
  reverse (Cases_on `is_dyn`) >> simp[]
  >- (irule shape_step_return >> simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `offset_val` all_tac >>
  shape_scalar_emit_bind_tac `P` `actual_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ActualFrame _ _` >>
  `shape_stable ActualFrame` by
    (simp[Abbr `ActualFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[actual_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ActualFrame` `underflow` (simp[Abbr `ActualFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `ActualFrame` `ok_op` all_tac >>
  shape_scalar_assert_tac `ActualFrame` >>
  irule shape_step_return >> simp[Abbr `ActualFrame`, Abbr `P`]
QED

Theorem compile_abi_decode_dyn_elem_ptr_shape_mload[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [elem_src;src_data;hi_op])
    (compile_abi_decode_dyn_elem_ptr MLOAD elem_src src_data hi_op elem_abi_sz)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[elem_src;src_data;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `off_val` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ptr_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label PtrFrame _ _` >>
  `shape_stable PtrFrame` by
    (simp[Abbr `PtrFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[ptr_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `PtrFrame` `bad_op` (simp[Abbr `PtrFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `PtrFrame` `ok_op` all_tac >>
  shape_scalar_assert_tac `PtrFrame` >>
  shape_scalar_emit_bind_tac `PtrFrame` `end_op` (simp[Abbr `PtrFrame`]) >>
  shape_scalar_emit_bind_tac `PtrFrame` `oob_op` (simp[Abbr `PtrFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `PtrFrame` `ok2_op` all_tac >>
  shape_scalar_assert_tac `PtrFrame` >>
  irule shape_step_return >> simp[Abbr `PtrFrame`, Abbr `P`]
QED

(* Expression lowering decodes return buffers from memory, never code. *)
Theorem compile_abi_decode_shape_mload:
  (!dst src_op load_opc hi_op info.
    load_opc = MLOAD ==> !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src_op;hi_op])
      (compile_abi_decode_to_buf dst src_op load_opc hi_op info) (\u st. R st)) /\
  (!dst src_op load_opc hi_op elems abi_ofst mem_ofst.
    load_opc = MLOAD ==> !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src_op;hi_op])
      (compile_abi_decode_complex_elems dst src_op load_opc hi_op elems abi_ofst mem_ofst)
      (\u st. R st)) /\
  (!dst src_op load_opc hi_op info abi_sz mem_sz i_ptr cnt.
    load_opc = MLOAD ==> !R internal. shape_stable R ==>
    shape_step internal compiler_label
      (\st. R st /\ EVERY (plain_operand st) [dst;src_op;hi_op;i_ptr;cnt])
      (compile_abi_decode_dyn_loop dst src_op load_opc hi_op info abi_sz mem_sz i_ptr cnt)
      (\u st. R st))
Proof
  ho_match_mp_tac abiEncoderTheory.compile_abi_decode_to_buf_ind >>
  conj_tac >- suspend "primitive" >>
  conj_tac >- suspend "bytes" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "complex" >>
  conj_tac
  >- (rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
      irule shape_step_return >> simp[]) >>
  conj_tac >- suspend "elements" >>
  suspend "dynamic"
QED

Resume compile_abi_decode_shape_mload[primitive]:
  rpt strip_tac >> gvs[] >>
  simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def,
       abiEncoderTheory.compile_abi_decode_static_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `val_op` (simp[Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. P st /\ plain_operand st val_op` >> conj_tac
  >- (ho_match_mp_tac compile_abi_clamp_basetype_shape_framed >> simp[]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >>
  simp[Abbr `P`] >> shape_opcode_tac
QED

Resume compile_abi_decode_shape_mload[bytes]:
  rpt strip_tac >> gvs[] >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LenFrame` `too_long` (simp[Abbr `LenFrame`]) >>
  shape_scalar_emit_bind_tac `LenFrame` `ok_op` all_tac >>
  shape_scalar_assert_tac `LenFrame` >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (Cases_on `hi_op = Lit 0w` >> simp[]
      >- (irule shape_step_return >> simp[Abbr `LenFrame`]) >>
      shape_scalar_emit_bind_tac `LenFrame` `data_start` (simp[Abbr `LenFrame`, Abbr `P`]) >>
      shape_scalar_emit_bind_tac `LenFrame` `data_end` (simp[Abbr `LenFrame`]) >>
      shape_scalar_emit_bind_tac `LenFrame` `oob_op` (simp[Abbr `LenFrame`, Abbr `P`]) >>
      shape_scalar_emit_bind_tac `P` `ok2_op` (simp[Abbr `LenFrame`]) >>
      shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac
QED
Resume compile_abi_decode_shape_mload[array]:
  rpt strip_tac >> gvs[] >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `clamp_cnt` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label CntFrame _ _` >>
  `shape_stable CntFrame` by
    (simp[Abbr `CntFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[clamp_cnt]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `CntFrame` `too_many` (simp[Abbr `CntFrame`]) >>
  shape_scalar_emit_bind_tac `CntFrame` `ok_op` all_tac >>
  shape_scalar_assert_tac `CntFrame` >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (Cases_on `hi_op = Lit 0w` >> simp[]
      >- (irule shape_step_return >> simp[Abbr `CntFrame`]) >>
      shape_scalar_emit_bind_tac `CntFrame` `payload_sz` (simp[Abbr `CntFrame`]) >>
      shape_scalar_emit_bind_tac `CntFrame` `payload_hdr` all_tac >>
      shape_scalar_emit_bind_tac `CntFrame` `payload_end` (simp[Abbr `CntFrame`, Abbr `P`]) >>
      shape_scalar_emit_bind_tac `CntFrame` `oob_op` (simp[Abbr `CntFrame`, Abbr `P`]) >>
      shape_scalar_emit_bind_tac `P` `ok2_op` (simp[Abbr `CntFrame`]) >>
      shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `P` `cnt_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LoopFrame _ _` >>
  `shape_stable LoopFrame` by
    (simp[Abbr `LoopFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[cnt_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LoopFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LoopFrame` >> simp[Abbr `LoopFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> IF_CASES_TAC
  >- (shape_scalar_emit_bind_tac `LoopFrame` `copy_sz` (simp[Abbr `LoopFrame`]) >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label CopyFrame _ _` >>
      `shape_stable CopyFrame` by
        (simp[Abbr `CopyFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[copy_sz]` shape_stable_plain_operands) >> simp[]) >>
      shape_scalar_emit_bind_tac `CopyFrame` `src_data` (simp[Abbr `CopyFrame`, Abbr `LoopFrame`, Abbr `P`]) >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
      `shape_stable SrcFrame` by
        (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
      shape_scalar_emit_bind_tac `SrcFrame` `dst_data` (simp[Abbr `SrcFrame`, Abbr `CopyFrame`, Abbr `LoopFrame`, Abbr `P`]) >>
      shape_under_tac shape_step_emit_void_plain `R` >>
      simp[Abbr `SrcFrame`, Abbr `CopyFrame`, Abbr `LoopFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gnvs[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\b st. LoopFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[SF ETA_ss]) >>
  qx_gen_tac `idx_buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label IdxFrame _ _` >>
  `shape_stable IdxFrame` by
    (simp[Abbr `IdxFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. IdxFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `IdxFrame` >> simp[Abbr `IdxFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  qpat_x_assum `!b cnt R' i. _` (qspec_then `idx_buf` assume_tac) >>
  first_assum (fn th => shape_under_tac th `R`) >>
  simp[Abbr `IdxFrame`, Abbr `LoopFrame`, Abbr `P`]
QED
Resume compile_abi_decode_shape_mload[complex]:
  rpt strip_tac >> gnvs[] >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  Cases_on `hi_op = Lit 0w` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `item_end` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `oob_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` all_tac >>
  shape_scalar_assert_tac `P` >>
  first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED
Resume compile_abi_decode_shape_mload[elements]:
  rpt strip_tac >> gvs[] >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_getelemptr_abi_shape_mload `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `elem_src` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[elem_src]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `SrcFrame` `elem_dst` (simp[Abbr `SrcFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `P`) >> simp[Abbr `SrcFrame`, Abbr `P`]) >>
  gen_tac >> simp[] >>
  qpat_x_assum `!R i. _` (mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_SYM]) >>
  disch_then (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED
Resume compile_abi_decode_shape_mload[dynamic]:
  rpt strip_tac >> gvs[] >>
  simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op;i_ptr;cnt]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `hdr_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >>
  suspend "decode_header"
QED
Resume compile_abi_decode_shape_mload[decode_header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `C` `idx` (simp[Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label IdxFrame _ _` >>
  `shape_stable IdxFrame` by
    (simp[Abbr `IdxFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `IdxFrame` `cnt_hdr` (simp[Abbr `IdxFrame`, Abbr `C`]) >>
  shape_scalar_emit_bind_tac `C` `cmp_op` (simp[Abbr `IdxFrame`]) >>
  shape_scalar_emit_bind_tac `C` `done_op` all_tac >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed
        `\st. C st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> suspend "decode_body"
QED
Resume compile_abi_decode_shape_mload[decode_body]:
  shape_scalar_emit_bind_tac `C` `idx_op` (simp[Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LoopFrame _ _` >>
  `shape_stable LoopFrame` by
    (simp[Abbr `LoopFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LoopFrame` `src_data` (simp[Abbr `LoopFrame`, Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `SrcFrame` `src_off` (simp[Abbr `SrcFrame`, Abbr `LoopFrame`]) >>
  shape_scalar_emit_bind_tac `SrcFrame` `elem_src` (simp[Abbr `SrcFrame`]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. LoopFrame st /\ plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_under_tac compile_abi_decode_dyn_elem_ptr_shape_mload `LoopFrame` >>
          simp[Abbr `SrcFrame`, Abbr `LoopFrame`, Abbr `C`]) >>
      irule shape_step_return >> simp[Abbr `SrcFrame`]) >>
  qx_gen_tac `actual_src` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ActualFrame _ _` >>
  `shape_stable ActualFrame` by
    (simp[Abbr `ActualFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[actual_src]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ActualFrame` `dst_data` (simp[Abbr `ActualFrame`, Abbr `LoopFrame`, Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label DstFrame _ _` >>
  `shape_stable DstFrame` by
    (simp[Abbr `DstFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `DstFrame` `dst_off` (simp[Abbr `DstFrame`, Abbr `ActualFrame`, Abbr `LoopFrame`]) >>
  shape_scalar_emit_bind_tac `ActualFrame` `elem_dst` (simp[Abbr `DstFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LoopFrame st` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `LoopFrame`) >>
      simp[Abbr `ActualFrame`, Abbr `LoopFrame`, Abbr `C`]) >>
  gen_tac >> simp[] >> suspend "decode_finish"
QED
Resume compile_abi_decode_shape_mload[decode_finish]:
  shape_scalar_emit_bind_tac `C` `new_i` (simp[Abbr `LoopFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `C`]
QED
Finalise compile_abi_decode_shape_mload[local]

Theorem lower_abi_decode_shape:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st data_op)
    (lower_abi_decode data_op dec_info abi_min abi_max output_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinAbiTheory.lower_abi_decode_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `data_len` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_len]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LenFrame` `data_ptr` (simp[Abbr `LenFrame`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label DataFrame _ _` >>
  `shape_stable DataFrame` by
    (simp[Abbr `DataFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. DataFrame st` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_scalar_emit_bind_tac `DataFrame` `valid` (simp[Abbr `DataFrame`, Abbr `LenFrame`]) >>
          shape_under_tac shape_step_emit_void_plain `DataFrame` >> shape_opcode_tac) >>
      shape_scalar_emit_bind_tac `DataFrame` `lt_min` (simp[Abbr `DataFrame`, Abbr `LenFrame`]) >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label MinFrame _ _` >>
      `shape_stable MinFrame` by
        (simp[Abbr `MinFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[lt_min]` shape_stable_plain_operands) >> simp[]) >>
      shape_scalar_emit_bind_tac `DataFrame` `ge_min` (simp[Abbr `MinFrame`]) >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label GeFrame _ _` >>
      `shape_stable GeFrame` by
        (simp[Abbr `GeFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[ge_min]` shape_stable_plain_operands) >> simp[]) >>
      shape_scalar_emit_bind_tac `GeFrame` `gt_max` (simp[Abbr `GeFrame`, Abbr `DataFrame`, Abbr `LenFrame`]) >>
      shape_scalar_emit_bind_tac `GeFrame` `le_max` all_tac >>
      shape_scalar_emit_bind_tac `DataFrame` `valid` (simp[Abbr `GeFrame`]) >>
      shape_under_tac shape_step_emit_void_plain `DataFrame` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> suspend "decode_wrapper_finish"
QED
Resume lower_abi_decode_shape[decode_wrapper_finish]:
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. DataFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[SF ETA_ss]) >>
  qx_gen_tac `out_buf_alloc` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. v = out_buf_alloc.buf_operand /\ (DataFrame st /\ plain_operand st v)` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `out_buf` >> simp[] >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label BufFrame _ _` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf_alloc.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `BufFrame` `hi_op` (simp[Abbr `BufFrame`, Abbr `DataFrame`, Abbr `LenFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac (cj 1 compile_abi_decode_shape_mload) `BufFrame` >>
      simp[Abbr `BufFrame`, Abbr `DataFrame`]) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[Abbr `BufFrame`, Abbr `DataFrame`, Abbr `LenFrame`, Abbr `P`]
QED
Finalise lower_abi_decode_shape[local]

(* Inline unwrap reasoning shared by callback consumers; the separately owned
   unwrap_value_shape theorem below is deliberately not duplicated here. *)
fun shape_unwrap_value_tac frame =
  BETA_TAC >> qmatch_goalsub_rename_tac `unwrap_value _ unwrap_vv` >>
  Cases_on `unwrap_vv` >> simp[unwrap_value_def, value_shape_ok_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `is_word_type val_ty` >> rename1 `compile_ptr_load _ locptr.ptr_location _` >>
  Cases_on `locptr.ptr_location = LocCode` >> simp[]
  >- simp[shape_step_def] >>
  IF_CASES_TAC
  >- (shape_under_tac compile_ptr_load_shape_framed frame >> simp[]) >>
  Cases_on `locptr.ptr_location` >> gvs[]
  >- (irule shape_step_return >> simp[]) >>
  shape_under_tac compile_ensure_in_memory_shape_framed frame >> simp[];

Theorem lower_value_callback_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root e /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (lower_value cfn cenv ty e) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[lower_value_def] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ value_shape_ok st v` >> conj_tac
  >- (ho_match_mp_tac shape_step_frame >> simp[]) >>
  gen_tac >> shape_unwrap_value_tac `R`
QED

Theorem compile_pow_mod256_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st a /\ plain_operand st b)
    (compile_pow_mod256 a b) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMathTheory.compile_pow_mod256_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_addmod_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [a;b;c])
    (compile_addmod a b c) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMathTheory.compile_addmod_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[a;b;c]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_mulmod_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [a;b;c])
    (compile_mulmod a b c) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMathTheory.compile_mulmod_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[a;b;c]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_multi_exprs_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !es R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (compile_multi_exprs cfn cenv es)
    (\vs st. R st /\ EVERY (plain_operand st) vs)
Proof
  strip_tac >> Induct >> rpt strip_tac >>
  gvs[supported_exprs_exists_every] >> simp[compile_multi_exprs_def]
  >- (irule shape_step_return >> simp[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >>
     simp[cenv_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_callback_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `head_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label HeadFrame _ _` >>
  `shape_stable HeadFrame` by
    (simp[Abbr `HeadFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[head_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\vs st. HeadFrame st /\ EVERY (plain_operand st) vs` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `HeadFrame`) >>
      simp[supported_exprs_exists_every, Abbr `HeadFrame`, Abbr `P`]) >>
  qx_gen_tac `tail_ops` >> simp[] >> irule shape_step_return >>
  simp[Abbr `HeadFrame`, Abbr `P`]
QED

Theorem compile_concat_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !es infos offset_op R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ cenv_shape_ok st cenv /\ EVERY (plain_operand st) [data_ptr;offset_op])
    (compile_concat cfn cenv es data_ptr infos offset_op)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Induct >> rpt strip_tac >>
  gvs[supported_exprs_exists_every]
  >- (simp[compile_concat_def] >> irule shape_step_return >> simp[]) >>
  Cases_on `infos`
  >- (simp[compile_concat_def] >> irule shape_step_return >> simp[]) >>
  rename1 `compile_concat _ _ _ _ (info::_) _` >>
  PairCases_on `info` >> simp[compile_concat_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[data_ptr;offset_op]` shape_stable_plain_operands) >> simp[]) >>
  IF_CASES_TAC >- suspend "bytestring" >> suspend "fixed"
QED
Resume compile_concat_shape[bytestring]:
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_callback_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `mem_ptr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label MemFrame _ _` >>
  `shape_stable MemFrame` by
    (simp[Abbr `MemFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[mem_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `MemFrame` `arg_len` (simp[Abbr `MemFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[arg_len]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LenFrame` `arg_data` (simp[Abbr `LenFrame`, Abbr `MemFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ArgFrame _ _` >>
  `shape_stable ArgFrame` by
    (simp[Abbr `ArgFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[arg_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ArgFrame` `dst_op` (simp[Abbr `ArgFrame`, Abbr `LenFrame`, Abbr `MemFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >> simp[Abbr `ArgFrame`, Abbr `LenFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `P` `new_offset` (simp[Abbr `LenFrame`, Abbr `MemFrame`, Abbr `P`]) >>
  first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED
Resume compile_concat_shape[fixed]:
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_callback_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `value_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ValFrame _ _` >>
  `shape_stable ValFrame` by
    (simp[Abbr `ValFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[value_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ValFrame` `dst_op` (simp[Abbr `ValFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `ValFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_scalar_emit_bind_tac `P` `new_offset` (simp[Abbr `P`]) >>
  first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED
Finalise compile_concat_shape[local]

Theorem compile_multi_vvs_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !es R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (compile_multi_vvs cfn cenv es)
    (\vs st. R st /\ EVERY (value_shape_ok st) vs)
Proof
  strip_tac >> Induct >> rpt strip_tac >>
  gvs[supported_exprs_exists_every] >> simp[compile_multi_vvs_def]
  >- (irule shape_step_return >> simp[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ value_shape_ok st v` >> conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. P st /\ cenv_shape_ok st cenv`,
                    `\v st. P st /\ value_shape_ok st v`] >>
      simp[Abbr `P`] >> ho_match_mp_tac shape_step_frame >> simp[]) >>
  qx_gen_tac `head_vv` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label HeadFrame _ _` >>
  `shape_stable HeadFrame` by
    (simp[Abbr `HeadFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[value_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\vs st. HeadFrame st /\ EVERY (value_shape_ok st) vs` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `HeadFrame`) >>
      simp[supported_exprs_exists_every, Abbr `HeadFrame`, Abbr `P`]) >>
  qx_gen_tac `tail_vvs` >> simp[] >> irule shape_step_return >> simp[Abbr `HeadFrame`, Abbr `P`]
QED

(* Tuple, array, and struct builders have the same callback/destination/store
   sequencing. Keep this shared proof plumbing local to that family. *)
fun shape_collection_cons_tac () =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[buf_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ value_shape_ok st v` >> conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. P st /\ cenv_shape_ok st cenv`,
                    `\v st. P st /\ value_shape_ok st v`] >>
      simp[Abbr `P`] >> ho_match_mp_tac shape_step_frame >> simp[]) >>
  qx_gen_tac `child_vv` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label VVFrame _ _` >>
  `shape_stable VVFrame` by
    (simp[Abbr `VVFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[value_shape_ok_stable]) >>
  shape_scalar_emit_bind_tac `VVFrame` `dst_op` (simp[Abbr `VVFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st dst_op /\ plain_operand st v` >> conj_tac
  >- suspend "unwrap" >>
  qx_gen_tac `value_op` >> simp[] >> suspend "store";

fun shape_collection_unwrap_tac () =
  qabbrev_tac `DestFrame = \st. P st /\ plain_operand st dst_op` >>
  `shape_stable DestFrame` by
    (simp[Abbr `DestFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. DestFrame st /\ value_shape_ok st child_vv`,
                `\v st. DestFrame st /\ plain_operand st v`] >>
  conj_tac >- simp[Abbr `DestFrame`] >>
  conj_tac >- simp[Abbr `DestFrame`, Abbr `VVFrame`] >>
  simp[] >> shape_unwrap_value_tac `DestFrame`;

fun shape_collection_store_tac () =
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac compile_store_memory_shape_framed `P` >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >> first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`];

Theorem compile_make_tuple_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !es cur_offset R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ cenv_shape_ok st cenv /\ plain_operand st buf_op)
    (compile_make_tuple cfn cenv es buf_op cur_offset)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Induct >> rpt strip_tac >> gvs[supported_exprs_exists_every] >>
  simp[compile_make_tuple_def]
  >- (irule shape_step_return >> simp[]) >>
  shape_collection_cons_tac ()
QED
Resume compile_make_tuple_shape[unwrap]:
  shape_collection_unwrap_tac ()
QED
Resume compile_make_tuple_shape[store]:
  shape_collection_store_tac ()
QED
Finalise compile_make_tuple_shape[local]

Theorem compile_make_array_elems_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !es cur_idx R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ cenv_shape_ok st cenv /\ plain_operand st buf_op)
    (compile_make_array_elems cfn cenv es elem_ty elem_size length_word buf_op cur_idx)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Induct >> rpt strip_tac >> gvs[supported_exprs_exists_every] >>
  simp[compile_make_array_elems_def]
  >- (irule shape_step_return >> simp[]) >>
  shape_collection_cons_tac ()
QED
Resume compile_make_array_elems_shape[unwrap]:
  shape_collection_unwrap_tac ()
QED
Resume compile_make_array_elems_shape[store]:
  shape_collection_store_tac ()
QED
Finalise compile_make_array_elems_shape[local]

Theorem compile_make_array_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ cenv_shape_ok st cenv /\ plain_operand st buf_op)
    (compile_make_array cfn cenv es elem_ty elem_size length_word buf_op)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_make_array_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[buf_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (Cases_on `length_word` >> simp[]
      >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >> shape_under_tac compile_make_array_elems_shape `R` >> simp[Abbr `P`]
QED

Theorem compile_struct_lit_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !fields cur_offset R. ~supported_fields_exists expr_shape_root fields /\ shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ cenv_shape_ok st cenv /\ plain_operand st buf_op)
    (compile_struct_lit cfn cenv ty fields buf_op cur_offset)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Induct >> rpt strip_tac >> gvs[supported_fields_exists_every]
  >- (simp[compile_struct_lit_def] >> irule shape_step_return >> simp[]) >>
  PairCases_on `h` >> gvs[] >> simp[compile_struct_lit_def] >>
  shape_collection_cons_tac ()
QED
Resume compile_struct_lit_shape[unwrap]:
  shape_collection_unwrap_tac ()
QED
Resume compile_struct_lit_shape[store]:
  shape_collection_store_tac ()
QED
Finalise compile_struct_lit_shape[local]

Theorem cenv_lookup_shape[local]:
  cenv_shape_ok st cenv /\ FLOOKUP cenv.ce_vars name = SOME loc ==>
  loc_shape_ok st loc
Proof
  simp[cenv_shape_ok_def] >> metis_tac[]
QED

Theorem infer_array_location_shape[local]:
  cenv_shape_ok st cenv ==> infer_array_location cenv e <> LocCode
Proof
  Cases_on `e` >> simp[infer_array_location_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `FLOOKUP cenv.ce_vars var_name` >>
  Cases_on `FLOOKUP cenv.ce_vars var_name` >> simp[] >>
  rename1 `FLOOKUP cenv.ce_vars var_name = SOME loc` >>
  drule_all cenv_lookup_shape >> Cases_on `loc` >> simp[loc_shape_ok_def]
QED

Theorem compile_tuple_subscript_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st base_op)
    (compile_tuple_subscript base_op offset) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_tuple_subscript_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_mapping_subscript_shape_framed[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [base_slot; key_op])
    (compile_mapping_subscript base_slot key_op) (\v st. R st /\ plain_operand st v)
Proof
  shape_framed_tac compile_mapping_subscript_shape
QED

Theorem compile_array_subscript_shape_framed[local]:
  shape_stable R /\ MEM load_opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [base_op; idx_op])
    (compile_array_subscript base_op idx_op dynamic_array static_count
       scale elem_size is_signed_idx load_opc)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >>
  `?loc. loc <> LocCode /\ load_opc = load_opc_for loc` by
    (qpat_x_assum `MEM _ _` (strip_assume_tac o SIMP_RULE list_ss []) >>
     gvs[] >|
     [qexists_tac `LocMemory`, qexists_tac `LocStorage`,
      qexists_tac `LocTransient`, qexists_tac `LocCalldata`] >>
     simp[load_opc_for_def]) >>
  qpat_x_assum `MEM _ _` kall_tac >> gvs[] >>
  shape_framed_tac compile_array_subscript_shape
QED

Theorem compile_attribute_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root base_e ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_attribute cfn cenv ret_ty ty base_e field_name)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> simp[compile_attribute_def] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. value_shape_ok st v` >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  qx_gen_tac `base_vv` >> simp[] >>
  qmatch_goalsub_abbrev_tac `Lit (n2w fld_offset)` >>
  assume_tac (Q.SPEC `base_vv` value_shape_ok_stable) >>
  shape_scalar_emit_bind_tac `\st. value_shape_ok st base_vv` `ptr_op`
    (Cases_on `base_vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  irule shape_step_return >> Cases_on `base_vv` >>
  simp[value_shape_ok_def, vv_location_def, mk_ptr_def]
QED


Theorem compile_acc_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root addr_e /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (compile_acc cfn cenv addr_e acc) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `acc` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_acc_def] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >~ [`shape_step _ _ _ (lower_value _ _ _ _) _`]
  >- (ho_match_mp_tac lower_value_callback_shape >> simp[])
  >~ [`shape_step _ _ _ (\st. UNCURRY _ (emit_inst INVALID [] [] st)) _`]
  >- suspend "invalid" >>
  (irule shape_step_uncurry >>
   qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
   >- (gen_tac >> simp[] >>
       FIRST [
         (irule shape_step_uncurry >>
          qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
          >- (gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
          shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac),
         (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac)]) >>
   ho_match_mp_tac lower_value_callback_shape >> simp[])
QED
Resume compile_acc_shape[invalid]:
  irule shape_step_uncurry >> qexists_tac `\u st. R st` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl] >> shape_opcode_tac) >>
  shape_under_tac shape_step_emit_inst `R` >> shape_opcode_tac >>
  qexists_tac `compiler_label` >> simp[]
QED
Finalise compile_acc_shape[local]

Theorem compile_dynarray_pop_shape[local]:
  shape_stable R /\ MEM load_opc [MLOAD; SLOAD; TLOAD] /\
  MEM store_opc [MSTORE; SSTORE; TSTORE] ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st base_op)
    (compile_dynarray_pop base_op scale elem_size load_opc store_opc)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_dynarray_pop_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[base_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`] >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `L` `nz` (simp[Abbr `L`]) >>
  shape_scalar_emit_bind_tac `L` `valid` all_tac >>
  shape_scalar_assert_tac `L` >>
  shape_scalar_emit_bind_tac `P` `new_len` (simp[Abbr `L`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label N _ _` >>
  `shape_stable N` by
    (simp[Abbr `N`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[new_len]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. N st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `N` >> simp[Abbr `N`, Abbr `P`] >> gvs[] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `N` `data_ptr` (simp[Abbr `N`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `offset_op` (simp[Abbr `D`, Abbr `N`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `D`, Abbr `N`, Abbr `P`] >> shape_opcode_tac
QED

(* Preserve the current comparison while compiling the remaining membership list. *)
fun shape_membership_tail_tac result =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label E _ _` >>
  `shape_stable E` by
    (simp[Abbr `E`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC ([QUOTE "["] @ result @ [QUOTE "]:operand list"]) shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. E st /\ plain_operand st v` >> conj_tac
  >- (first_x_assum (fn th => shape_under_tac th `E`) >> simp[Abbr `E`, Abbr `P`]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >>
  simp[Abbr `E`, Abbr `P`] >> shape_opcode_tac;

Theorem compile_list_membership_in_shape[local]:
  !ops R. shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st needle /\ EVERY (plain_operand st) ops)
    (compile_list_membership_in needle ops) (\v st. R st /\ plain_operand st v)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[compile_list_membership_in_def] >> irule shape_step_return >> shape_opcode_tac) >>
  Cases_on `ops` >> simp[compile_list_membership_in_def]
  >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  rename1 `compile_list_membership_in needle (next::rest)` >>
  rename1 `emit_op EQ [needle;elem]` >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `needle::elem::next::rest` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `eq_op` (simp[Abbr `P`]) >>
  shape_membership_tail_tac `eq_op`
QED

Theorem compile_list_membership_notin_shape[local]:
  !ops R. shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st needle /\ EVERY (plain_operand st) ops)
    (compile_list_membership_notin needle ops) (\v st. R st /\ plain_operand st v)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[compile_list_membership_notin_def] >> irule shape_step_return >> shape_opcode_tac) >>
  Cases_on `ops` >> simp[compile_list_membership_notin_def]
  >- (shape_scalar_emit_bind_tac `R` `eq_op` all_tac >>
      shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  rename1 `compile_list_membership_notin needle (next::rest)` >>
  rename1 `emit_op EQ [needle;elem]` >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `needle::elem::next::rest` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `eq_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `neq_op` all_tac >>
  shape_membership_tail_tac `neq_op`
QED

Theorem compile_keccak256_key_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st key_op)
    (compile_keccak256_key key_op bytes32_key) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_keccak256_key_def] >> Cases_on `bytes32_key` >> simp[]
  >- (match_mp_tac shape_step_bind >>
      qexists_tac `\b st. R st /\ plain_operand st key_op /\ plain_operand st b.buf_operand` >> conj_tac
      >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. R st /\ plain_operand st key_op` >>
          ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[key_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
      qx_gen_tac `buf` >> simp[] >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
      `shape_stable P` by
        (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[key_op;buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
      match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[key_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `data_ptr` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `len_op` (simp[Abbr `D`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `D`, Abbr `P`] >> shape_opcode_tac
QED

val shape_subscript_tuple_tac =
  rename1 `compile_tuple_subscript _ _` >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. value_shape_ok st v` >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  qx_gen_tac `base_vv` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `compile_tuple_subscript _ fld_offset` >>
  assume_tac (Q.SPEC `base_vv` value_shape_ok_stable) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. value_shape_ok st base_vv /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_tuple_subscript_shape `\st. value_shape_ok st base_vv` >>
      Cases_on `base_vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >> Cases_on `base_vv` >>
  simp[value_shape_ok_def, vv_location_def, mk_ptr_def];

val shape_subscript_array_tac =
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ value_shape_ok st v` >> conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable] >>
      first_assum (irule_at Any) >> simp[]) >>
  qx_gen_tac `base_vv` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  assume_tac (Q.SPEC `base_vv` value_shape_ok_stable) >>
  `shape_stable (\st. cenv_shape_ok st cenv /\ value_shape_ok st base_vv)` by
    (ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. (cenv_shape_ok st cenv /\ value_shape_ok st base_vv) /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_callback_shape `\st. cenv_shape_ok st cenv /\ value_shape_ok st base_vv` >> simp[]) >>
  qx_gen_tac `idx_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_array_subscript_shape_framed `\st. cenv_shape_ok st cenv` >>
      simp[cenv_shape_ok_stable] >> conj_tac
      >- (Cases_on `infer_array_location cenv base_e` >> simp[]) >>
      Cases_on `base_vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, mk_ptr_def] >> rpt strip_tac >>
  drule infer_array_location_shape >> disch_then (qspec_then `base_e` mp_tac) >> simp[];

Theorem compile_subscript_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root base_e /\
  ~supported_expr_exists expr_shape_root idx_e ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_subscript cfn cenv ret_ty ty base_e idx_e)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  qmatch_goalsub_abbrev_tac `cenv.ce_is_hashmap var_name` >>
  IF_CASES_TAC >- suspend "mapping" >>
  Cases_on `cenv.ce_var_type var_name` >> simp[]
  >- shape_subscript_array_tac >>
  rename1 `SOME base_ty` >> Cases_on `base_ty` >> simp[]
  >~ [`compile_tuple_subscript _ _`] >- shape_subscript_tuple_tac
  >~ [`compile_tuple_subscript _ _`] >- shape_subscript_tuple_tac >>
  shape_subscript_array_tac
QED
Resume compile_subscript_shape[mapping]:
  match_mp_tac shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_callback_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `key_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (shape_under_tac compile_keccak256_key_shape `\st. T` >> simp[shape_stable_def]) >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `hashed_key` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_mapping_subscript_shape_framed `\st. T` >> simp[shape_stable_def] >>
      Cases_on `FLOOKUP cenv.ce_vars var_name` >> simp[]
      >- shape_opcode_tac >>
      rename1 `SOME local_loc` >> Cases_on `local_loc` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, mk_ptr_def]
QED
Finalise compile_subscript_shape[local]

Theorem compile_array_membership_loop_shape:
  shape_stable R /\ MEM load_opc [MLOAD; SLOAD; TLOAD] ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [needle; arr_op; len_op])
    (compile_array_membership_loop needle arr_op len_op elem_size offset_base load_opc is_in)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_array_membership_loop_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[needle; arr_op; len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st (Var v)` >> conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >> simp[]) >>
  qx_gen_tac `result_var` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var result_var]` shape_stable_plain_operands) >> simp[]) >>
  map_every (fn lbl =>
    match_mp_tac shape_step_bind >>
    qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
    >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
    qx_gen_tac lbl >> simp[] >>
    ho_match_mp_tac shape_step_pure_pre >> strip_tac)
    [`entry_lbl`, `cond_lbl`, `body_lbl`, `found_lbl`, `incr_lbl`, `exit_lbl`] >>
  suspend "header"
QED
Resume compile_array_membership_loop_shape[header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `C` >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. C st /\ plain_operand st (Var v)` >> conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >> simp[SF ETA_ss]) >>
  qx_gen_tac `idx_var` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var idx_var]` shape_stable_plain_operands) >> simp[]) >>
  ntac 3
    (match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
     >- (shape_under_tac shape_step_emit_inst_guarded_framed `D` >>
         simp[Abbr `D`, Abbr `C`] >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
     gen_tac >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `D` `done_op` (simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. D st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> suspend "body"
QED
Resume compile_array_membership_loop_shape[body]:
  shape_scalar_emit_bind_tac `D` `idx_offset` (simp[Abbr `D`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. D st /\ plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_under_tac shape_step_emit_op_plain `\st. D st /\ plain_operand st idx_offset` >>
          conj_tac
          >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
              mp_tac (Q.SPEC `[idx_offset]` shape_stable_plain_operands) >> simp[]) >>
          shape_opcode_tac) >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `total_offset` >> simp[] >>
  shape_scalar_emit_bind_tac `D` `elem_addr` (simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. D st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `\st. D st /\ plain_operand st elem_addr` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[elem_addr]` shape_stable_plain_operands) >> simp[]) >>
      gvs[] >> shape_opcode_tac) >>
  qx_gen_tac `elem_val` >> simp[] >>
  shape_scalar_emit_bind_tac `D` `match_op` (simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. D st /\ plain_operand st match_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[match_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> suspend "finish"
QED
Resume compile_array_membership_loop_shape[finish]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  ntac 2
    (match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
     >- (shape_under_tac shape_step_emit_inst_guarded_framed `D` >>
         simp[Abbr `D`, Abbr `C`] >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
     gen_tac >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `D` `new_idx` (simp[Abbr `D`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. D st /\ plain_operand st new_idx` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[new_idx]` shape_stable_plain_operands) >> simp[]) >>
      simp[Abbr `D`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `D` >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `D`, Abbr `C`, Abbr `P`] >> shape_opcode_tac
QED
Finalise compile_array_membership_loop_shape[local]

Theorem compile_var_array_membership_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st needle /\ value_shape_ok st arr_vv)
    (compile_var_array_membership cenv needle arr_vv rhs_ty is_in)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_var_array_membership_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  assume_tac (Q.SPEC `arr_vv` value_shape_ok_stable) >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[needle]` shape_stable_plain_operands) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `emit_op load_opc _` >>
  `MEM load_opc [MLOAD; SLOAD; TLOAD]` by
    (simp[Abbr `load_opc`] >> Cases_on `vv_location arr_vv` >> simp[] >>
     rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_under_tac shape_step_emit_op_plain `P` >>
          gvs[] >> Cases_on `arr_vv` >> simp[Abbr `P`, value_shape_ok_def, vv_operand_def] >> shape_opcode_tac) >>
      Cases_on `rhs_ty` >> simp[]
      >~ [`ArrayT elem_ty bd`]
      >- (Cases_on `bd` >> simp[] >> irule shape_step_return >> shape_opcode_tac) >>
      irule shape_step_return >> shape_opcode_tac) >>
  qx_gen_tac `len_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (IF_CASES_TAC
      >- (Cases_on `rhs_ty` >> gvs[] >> rename1 `case bd of Fixed _ => F | Dynamic _ => T` >>
          Cases_on `bd` >> gvs[] >>
          (shape_scalar_emit_bind_tac `C` `inv_op` (simp[Abbr `C`]) >>
          shape_scalar_emit_bind_tac `C` `valid` all_tac >>
          shape_under_tac shape_step_emit_inst_guarded_framed `\st. C st /\ plain_operand st valid` >>
          conj_tac
          >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
              mp_tac (Q.SPEC `[valid]` shape_stable_plain_operands) >> simp[]) >>
          shape_opcode_tac)) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >>
  shape_under_tac compile_array_membership_loop_shape `R` >> simp[Abbr `C`, Abbr `P`] >>
  Cases_on `arr_vv` >> simp[value_shape_ok_def, vv_operand_def]
QED

Theorem compile_assert_slice_bounds_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [start_op; length_op; src_len_op])
    (compile_assert_slice_bounds start_op length_op src_len_op) (\u st. R st)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_assert_slice_bounds_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op; length_op; src_len_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `end_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label E _ _` >>
  `shape_stable E` by
    (simp[Abbr `E`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[end_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `E` `overflow_op` (simp[Abbr `E`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label OverflowFrame _ _` >>
  `shape_stable OverflowFrame` by
    (simp[Abbr `OverflowFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[overflow_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `OverflowFrame` `oob_op` (simp[Abbr `OverflowFrame`, Abbr `E`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `R` `bad_op` (simp[Abbr `OverflowFrame`, Abbr `E`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `R` `ok_op` all_tac >>
  shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED

Theorem compile_bytestring_src_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st src_ptr)
    (compile_bytestring_src src_ptr)
    (\v st. R st /\ EVERY (plain_operand st) [FST v; SND v])
Proof
  strip_tac >> simp[builtinBytesTheory.compile_bytestring_src_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `src_len` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_len]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `L` `src_data` (simp[Abbr `L`, Abbr `P`]) >>
  irule shape_step_return >> simp[Abbr `L`, Abbr `P`]
QED

Theorem compile_slice_out_buf_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_slice_out_buf out_size)
    (\v st. R st /\ EVERY (plain_operand st) [FST v; SND v])
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_out_buf_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. R st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `R`) >>
  qx_gen_tac `buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `out_data` (simp[Abbr `P`]) >>
  irule shape_step_return >> simp[Abbr `P`]
QED

Theorem compile_slice_data_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [src_len; src_data; start_op; length_op])
    (compile_slice_data src_len src_data start_op length_op out_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_data_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_len; src_data; start_op; length_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac compile_assert_slice_bounds_shape `P` >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >>
  qx_gen_tac `buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `B` `out_data` (simp[Abbr `B`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `copy_src` (simp[Abbr `D`, Abbr `B`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `\st. D st /\ plain_operand st copy_src` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[copy_src]` shape_stable_plain_operands) >> simp[]) >>
      simp[Abbr `D`, Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >>
      simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  irule shape_step_return >> simp[Abbr `B`, Abbr `P`]
QED

Theorem compile_slice_memory_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [src_ptr; start_op; length_op])
    (compile_slice_memory src_ptr start_op length_op out_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_memory_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_ptr; start_op; length_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ EVERY (plain_operand st) [FST v; SND v]` >> conj_tac
  >- (shape_under_tac compile_bytestring_src_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `src` >> PairCases_on `src` >> simp[] >>
  shape_under_tac compile_slice_data_shape `R` >> simp[Abbr `P`]
QED

Theorem compile_slice_extcode_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [addr_op; start_op; length_op; out_buf; out_data])
    (compile_slice_extcode addr_op start_op length_op out_buf out_data)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_extcode_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[addr_op; start_op; length_op; out_buf; out_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `src_len` (simp[Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac compile_assert_slice_bounds_shape `P` >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `P`]
QED

Theorem compile_slice_calldata_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [start_op; length_op])
    (compile_slice_calldata start_op length_op out_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_calldata_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op; length_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ EVERY (plain_operand st) [FST v; SND v]` >> conj_tac
  >- (shape_under_tac compile_slice_out_buf_shape `P`) >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out0; out1]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `B` `src_len` all_tac >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac compile_assert_slice_bounds_shape `B` >> simp[Abbr `B`, Abbr `P`]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `B`, Abbr `P`]
QED

Theorem compile_slice_code_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [start_op; length_op])
    (compile_slice_code start_op length_op out_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_slice_code_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op; length_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ EVERY (plain_operand st) [FST v; SND v]` >> conj_tac
  >- (shape_under_tac compile_slice_out_buf_shape `P`) >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out0; out1]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `B` `src_len` all_tac >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac compile_assert_slice_bounds_shape `B` >> simp[Abbr `B`, Abbr `P`]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `B`, Abbr `P`]
QED

Theorem compile_extract32_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [src_ptr; start_op])
    (compile_extract32 src_ptr start_op)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinBytesTheory.compile_extract32_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_ptr; start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `src_len` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_len]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `L` `src_data` (simp[Abbr `L`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `end_op` (simp[Abbr `D`, Abbr `L`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `D` `oob_op` (simp[Abbr `D`, Abbr `L`]) >>
  shape_scalar_emit_bind_tac `D` `ok_op` all_tac >>
  shape_scalar_assert_tac `D` >>
  shape_scalar_emit_bind_tac `R` `load_ptr` (simp[Abbr `D`, Abbr `L`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem shape_step_emit_op_call_guarded[local]:
  shape_stable R /\ MEM opc [CALL; STATICCALL] /\
  (!st id outs. R st /\ (gas_operand st g \/ plain_operand st g) /\
                EVERY (plain_operand st) rest ==>
     lowered_inst_ok internal (mk_inst id opc (g::rest) outs)) ==>
  shape_step internal compiler_label
    (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
          EVERY (plain_operand st) rest)
    (emit_op opc (g::rest)) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`internal`, `compiler_label`, `R`, `opc`, `g`, `rest`]
                  shape_step_emit_op_call) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[shape_step_def] >> metis_tac[]
QED

Theorem compile_sha256_bytes_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st ptr_op)
    (compile_sha256_bytes ptr_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinHashingTheory.compile_sha256_bytes_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[ptr_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `length_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[length_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `L` `data_ptr` (simp[Abbr `L`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. D st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `D`) >>
  qx_gen_tac `buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\g st. B st /\ gas_operand st g` >> conj_tac
  >- (irule shape_step_emit_op_gas >> simp[]) >>
  qx_gen_tac `gas_op` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_call_guarded `B` >>
      simp[Abbr `B`, Abbr `D`, Abbr `L`, Abbr `P`] >>
      shape_opcode_tac >> rpt strip_tac >>
      gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >> shape_scalar_assert_tac `B` >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `B`, Abbr `D`, Abbr `L`, Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_sha256_bytesm_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_sha256_bytesm val_op m) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinHashingTheory.compile_sha256_bytesm_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >>
  qx_gen_tac `in_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label InputFrame _ _` >>
  `shape_stable InputFrame` by
    (simp[Abbr `InputFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[in_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\b st. InputFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `InputFrame`) >>
  qx_gen_tac `out_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\g st. B st /\ gas_operand st g` >> conj_tac
  >- (irule shape_step_emit_op_gas >> simp[]) >>
  qx_gen_tac `gas_op` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_call_guarded `B` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >>
      shape_opcode_tac >> rpt strip_tac >> gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >> shape_scalar_assert_tac `B` >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_sha256_word_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_sha256_word val_op) (\v st. R st /\ plain_operand st v)
Proof
  simp[builtinHashingTheory.compile_sha256_word_def,
       GSYM builtinHashingTheory.compile_sha256_bytesm_def,
       compile_sha256_bytesm_shape]
QED

Theorem compile_ecrecover_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [hash_op; v_op; r_op; s_op])
    (compile_ecrecover hash_op v_op r_op s_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_ecrecover_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[hash_op; v_op; r_op; s_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >> qx_gen_tac `in_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label InputFrame _ _` >>
  `shape_stable InputFrame` by
    (simp[Abbr `InputFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[in_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `InputFrame` `off1` (simp[Abbr `InputFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `InputFrame` `off2` (simp[Abbr `InputFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `InputFrame` `off3` (simp[Abbr `InputFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\b st. InputFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `InputFrame`) >> qx_gen_tac `out_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\g st. B st /\ gas_operand st g` >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule shape_step_emit_op_gas >> simp[]) >> qx_gen_tac `gas_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_call_guarded `B` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >>
      shape_opcode_tac >> rpt strip_tac >> gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >> shape_scalar_assert_tac `B` >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac
QED

(* Interleaved point load/store used by the EC precompile generators. *)
fun shape_point_word_tac frame normalize =
  shape_scalar_emit_bind_tac frame `source_ptr` normalize >>
  shape_scalar_emit_bind_tac frame `word_op` all_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label WordFrame _ _` >>
  `shape_stable WordFrame` by
    (simp[Abbr `WordFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[word_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `WordFrame` `dest_ptr` (simp[Abbr `WordFrame`] >> normalize) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac ([QUOTE "\\u st. ("] @ frame @ [QUOTE ") st"]) >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `WordFrame` >>
      simp[Abbr `WordFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  qpat_x_assum `Abbrev (WordFrame = _)` kall_tac >>
  qpat_x_assum `shape_stable WordFrame` kall_tac;

Theorem compile_ecadd_points_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ EVERY (plain_operand st) [p1; p2])
    (compile_ecadd_points p1 p2) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_ecadd_points_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[p1; p2]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >> qx_gen_tac `in_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label InputFrame _ _` >>
  `shape_stable InputFrame` by
    (simp[Abbr `InputFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[in_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. InputFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `InputFrame`) >> qx_gen_tac `out_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\g st. B st /\ gas_operand st g` >> conj_tac
  >- (irule shape_step_emit_op_gas >> simp[]) >> qx_gen_tac `gas_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_call_guarded `B` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >>
      shape_opcode_tac >> rpt strip_tac >> gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >> shape_scalar_assert_tac `B` >>
  irule shape_step_return >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`]
QED

Theorem compile_ecmul_point_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ EVERY (plain_operand st) [p; scalar])
    (compile_ecmul_point p scalar) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_ecmul_point_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[p; scalar]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P`) >> qx_gen_tac `in_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label InputFrame _ _` >>
  `shape_stable InputFrame` by
    (simp[Abbr `InputFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[in_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  shape_point_word_tac `InputFrame` (simp[Abbr `InputFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `InputFrame` `i2` (simp[Abbr `InputFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. InputFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `InputFrame` >> simp[Abbr `InputFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. InputFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `InputFrame`) >> qx_gen_tac `out_buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\g st. B st /\ gas_operand st g` >> conj_tac
  >- (irule shape_step_emit_op_gas >> simp[]) >> qx_gen_tac `gas_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_call_guarded `B` >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`] >>
      shape_opcode_tac >> rpt strip_tac >> gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >> shape_scalar_assert_tac `B` >>
  irule shape_step_return >> simp[Abbr `B`, Abbr `InputFrame`, Abbr `P`]
QED

Theorem store_multi_results_shape[local]:
  !ops offset. shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st buf_op /\ EVERY (plain_operand st) ops)
    (store_multi_results buf_op ops offset) (\u st. R st)
Proof
  Induct_on `ops`
  >- (simp[store_multi_results_def] >> rpt strip_tac >> irule shape_step_return >> simp[]) >>
  rpt gen_tac >> strip_tac >> simp[store_multi_results_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `buf_op::h::ops` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `dst` (simp[Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_conseq >> first_x_assum (irule_at Any) >>
  simp[Abbr `P`]
QED

Theorem compile_stage_intcall_args_shape:
  !cenv vals flags tys R. shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ EVERY (value_shape_ok st) vals)
    (compile_stage_intcall_args cenv vals flags tys)
    (\vs st. R st /\ EVERY (plain_operand st) vs)
Proof
  recInduct compile_stage_intcall_args_ind >> rpt strip_tac
  >- (simp[compile_stage_intcall_args_def] >> irule shape_step_return >> simp[]) >>
  all_tac
  >~ [`compile_stage_intcall_args cenv (vv::vals) (F::flags) (ty::tys)`]
  >- suspend "buffer" >>
  simp[Once compile_stage_intcall_args_def] >>
  (qabbrev_tac `TailFrame = \st. R st /\ EVERY (value_shape_ok st) vals` >>
   `shape_stable TailFrame` by
     (simp[Abbr `TailFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
      simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
      rename1 `shape_extends i LP st st'` >>
      mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
      disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
   match_mp_tac shape_step_bind >>
   qexists_tac `\v st. TailFrame st /\ plain_operand st v` >> conj_tac
   >- (irule shape_step_conseq >>
       qexistsl_tac [`compiler_label`, `\st. TailFrame st /\ value_shape_ok st vv`,
                     `\v st. TailFrame st /\ plain_operand st v`] >>
       conj_tac >- simp[] >>
       conj_tac >- simp[Abbr `TailFrame`] >>
       conj_tac >- simp[] >> shape_unwrap_value_tac `TailFrame`) >>
   qx_gen_tac `val_op` >> simp[] >>
   qabbrev_tac `HeadFrame = \st. R st /\ plain_operand st val_op` >>
   `shape_stable HeadFrame` by
     (simp[Abbr `HeadFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
      mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
   match_mp_tac shape_step_bind >>
   qexists_tac `\vs st. HeadFrame st /\ EVERY (plain_operand st) vs` >> conj_tac
   >- (first_assum (fn th => shape_under_tac th `HeadFrame`) >>
       simp[Abbr `HeadFrame`, Abbr `TailFrame`]) >>
   qx_gen_tac `rest` >> simp[] >> irule shape_step_return >> simp[Abbr `HeadFrame`])
QED

Resume compile_stage_intcall_args_shape[buffer]:
  first_x_assum (qspecl_then
    [`type_memory_bytes cenv ty`,
     `case ty of BaseT (BytesT (Dynamic _)) => T | BaseT (StringT _) => T | _ => F`,
     `buf_alloc.buf_operand`, `buf_alloc`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  qabbrev_tac `TailFrame = \st. R st /\ EVERY (value_shape_ok st) vals` >>
  `shape_stable TailFrame` by
    (simp[Abbr `TailFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
     rename1 `shape_extends i LP st st'` >>
     mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
     disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. TailFrame st /\ plain_operand st v` >> conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. TailFrame st /\ value_shape_ok st vv`,
                    `\v st. TailFrame st /\ plain_operand st v`] >>
      conj_tac >- simp[] >> conj_tac >- simp[Abbr `TailFrame`] >>
      conj_tac >- simp[] >> shape_unwrap_value_tac `TailFrame`) >>
  qx_gen_tac `val_op` >> simp[] >>
  qabbrev_tac `ValFrame = \st. TailFrame st /\ plain_operand st val_op` >>
  `shape_stable ValFrame` by
    (simp[Abbr `ValFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. ValFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `ValFrame`) >>
  qx_gen_tac `buf_alloc` >> simp[] >>
  qabbrev_tac `BufFrame = \st. ValFrame st /\ plain_operand st buf_alloc.buf_operand` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_alloc.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >>
          simp[Abbr `BufFrame`, Abbr `ValFrame`] >> shape_opcode_tac) >>
      IF_CASES_TAC
      >- (match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
          >- (shape_under_tac compile_store_bytestring_shape_framed `BufFrame` >>
              simp[Abbr `BufFrame`, Abbr `ValFrame`]) >>
          gen_tac >> irule shape_step_return >> simp[]) >>
      shape_under_tac shape_step_emit_void_plain `BufFrame` >>
      simp[Abbr `BufFrame`, Abbr `ValFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  qabbrev_tac `HeadFrame = \st. R st /\ plain_operand st buf_alloc.buf_operand` >>
  `shape_stable HeadFrame` by
    (simp[Abbr `HeadFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_alloc.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\vs st. HeadFrame st /\ EVERY (plain_operand st) vs` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `HeadFrame`) >>
      simp[Abbr `HeadFrame`, Abbr `BufFrame`, Abbr `ValFrame`, Abbr `TailFrame`]) >>
  qx_gen_tac `rest` >> simp[] >> irule shape_step_return >> simp[Abbr `HeadFrame`]
QED
Finalise compile_stage_intcall_args_shape[local]

Theorem compile_materialize_vv_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ value_shape_ok st vv)
    (compile_materialize_vv cenv ty vv) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_materialize_vv_def] >>
  qabbrev_tac `VVFrame = \st. R st /\ value_shape_ok st vv` >>
  `shape_stable VVFrame` by
    (simp[Abbr `VVFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[value_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. VVFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `VVFrame`) >>
  qx_gen_tac `tmp` >> simp[] >>
  qabbrev_tac `BufFrame = \st. R st /\ plain_operand st tmp.buf_operand` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[tmp.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. BufFrame st /\ plain_operand st v` >> conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. BufFrame st /\ value_shape_ok st vv`,
                    `\v st. BufFrame st /\ plain_operand st v`] >>
      conj_tac >- simp[] >> conj_tac >- simp[Abbr `BufFrame`, Abbr `VVFrame`] >>
      conj_tac >- simp[] >> shape_unwrap_value_tac `BufFrame`) >>
  qx_gen_tac `src` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac compile_store_memory_shape_framed `BufFrame` >> simp[Abbr `BufFrame`]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `BufFrame`]
QED

Theorem compile_ext_call_kwarg_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root e /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (compile_ext_call_kwarg cfn cenv return_type k e)
    (\v st. R st /\ plain_operand st (FST v))
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (match_mp_tac shape_step_bind >>
      qexists_tac `\v st. R st /\ value_shape_ok st v` >> conj_tac
      >- (ho_match_mp_tac shape_step_frame >> simp[]) >>
      qx_gen_tac `vv` >> simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
      >- (irule compile_materialize_vv_shape >> simp[]) >>
      gen_tac >> simp[] >> irule shape_step_return >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (irule lower_value_callback_shape >> simp[]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

Theorem compile_ext_call_kwargs_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) ==>
  !ks es R. ~supported_exprs_exists expr_shape_root es /\ shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ cenv_shape_ok st cenv)
    (compile_ext_call_kwargs cfn cenv return_type ks es)
    (\vs st. R st /\
       EVERY (plain_operand st)
         ((case FST vs of NONE => [] | SOME v => [v]) ++
          (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
          (case SND (SND vs) of NONE => [] | SOME v => [FST v])))
Proof
  strip_tac >> Induct >> rpt gen_tac >> strip_tac
  >- (simp[compile_ext_call_kwargs_def] >> irule shape_step_return >> simp[]) >>
  Cases_on `es`
  >- (simp[compile_ext_call_kwargs_def] >> irule shape_step_return >> simp[]) >>
  gvs[supported_exprs_exists_every] >> simp[compile_ext_call_kwargs_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st (FST v)` >> conj_tac
  >- (shape_under_tac compile_ext_call_kwarg_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `op_ty` >> PairCases_on `op_ty` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label HeadFrame _ _` >>
  `shape_stable HeadFrame` by
    (simp[Abbr `HeadFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[op_ty0]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\vs st. HeadFrame st /\
       EVERY (plain_operand st)
         ((case FST vs of NONE => [] | SOME v => [v]) ++
          (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
          (case SND (SND vs) of NONE => [] | SOME v => [FST v]))` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `HeadFrame`) >>
      simp[supported_exprs_exists_every, Abbr `HeadFrame`, Abbr `P`]) >>
  qx_gen_tac `opts` >> PairCases_on `opts` >> simp[] >>
  irule shape_step_return >> simp[Abbr `HeadFrame`, Abbr `P`] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem compile_extcall_store_values_shape[local]:
  !vs offset R. shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st buf_op /\ EVERY (value_shape_ok st o FST) vs)
    (compile_extcall_store_values cenv vs buf_op offset) (\u st. R st)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[compile_extcall_store_values_def] >> irule shape_step_return >> simp[]) >>
  PairCases_on `h` >> simp[compile_extcall_store_values_def] >>
  qabbrev_tac `P = \st. R st /\ plain_operand st buf_op /\
                        EVERY (value_shape_ok st o FST) vs` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> conj_tac
     >- (mp_tac (Q.SPEC `[buf_op]` shape_stable_plain_operands) >> simp[]) >>
     simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
     rename1 `shape_extends i LP st st'` >>
     mp_tac (Q.SPEC `FST (e : vyper_value # type)` value_shape_ok_stable) >> simp[shape_stable_def] >>
     disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  qabbrev_tac `V = \st. P st /\ value_shape_ok st h0` >>
  `shape_stable V` by
    (simp[Abbr `V`] >> ho_match_mp_tac shape_stable_conj >> simp[value_shape_ok_stable]) >>
  shape_scalar_emit_bind_tac `V` `dst` (simp[Abbr `V`, Abbr `P`]) >>
  qabbrev_tac `D = \st. P st /\ plain_operand st dst` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. D st /\ plain_operand st v` >> conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. D st /\ value_shape_ok st h0`,
                    `\v st. D st /\ plain_operand st v`] >>
      conj_tac >- simp[] >> conj_tac >- simp[Abbr `D`, Abbr `V`] >>
      conj_tac >- simp[] >> shape_unwrap_value_tac `D`) >>
  qx_gen_tac `src` >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. P st` >> conj_tac
  >- (IF_CASES_TAC
      >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `D`] >> shape_opcode_tac) >>
      IF_CASES_TAC
      >- (shape_under_tac compile_store_bytestring_shape_framed `P` >> simp[Abbr `D`]) >>
      shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `D`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED

Theorem compile_extcodesize_check_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st addr_op)
    (compile_extcodesize_check addr_op) (\u st. R st)
Proof
  strip_tac >> simp[compile_extcodesize_check_def] >>
  shape_scalar_emit_bind_tac `R` `codesize` all_tac >>
  shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED

Theorem compile_return_value_decode_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st buf_op)
    (compile_return_value_decode buf_op min_return_size max_return_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_return_value_decode_def] >>
  qabbrev_tac `P = \st. R st /\ plain_operand st buf_op` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `rds` all_tac >>
  qabbrev_tac `D = \st. P st /\ plain_operand st rds` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[rds]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `too_small` (simp[Abbr `D`]) >>
  shape_scalar_emit_bind_tac `D` `ok` all_tac >> shape_scalar_assert_tac `D` >>
  shape_scalar_emit_bind_tac `D` `is_smaller` (simp[Abbr `D`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_select_shape_framed `P` >>
      simp[Abbr `D`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >>
  simp[Abbr `P`] >> shape_opcode_tac
QED

fun shape_call_label_tac frame name =
  match_mp_tac shape_step_bind >>
  qexists_tac ([QUOTE "\\l st. compiler_label l /\\ ("] @ frame @ [QUOTE ") st"]) >> conj_tac
  >- (shape_under_tac shape_step_fresh_label frame >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac name >> simp[] >> ho_match_mp_tac shape_step_pure_pre >> strip_tac;

fun shape_call_effect_tac frame effect =
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac ([QUOTE "\\u st. ("] @ frame @ [QUOTE ") st"]) >> conj_tac
  >- effect >> gen_tac >> simp[];

fun shape_call_jump_tac frame =
  shape_call_effect_tac frame
    (shape_under_tac shape_step_emit_inst_guarded_framed frame >>
     shape_opcode_tac >> simp[jump_label_ok_def]);

fun shape_call_block_tac frame =
  shape_call_effect_tac frame
    (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]);

Theorem compile_uint2str_shape:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_uint2str val_op n_digits buf_size)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinStringsTheory.compile_uint2str_def] >>
  qabbrev_tac `P = \st. R st /\ plain_operand st val_op` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P` >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qabbrev_tac `B = \st. P st /\ plain_operand st buf.buf_operand` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. B st /\ plain_operand st (Var v)` >> conj_tac
  >- (shape_under_tac shape_step_fresh_var `B` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `val_var` >> simp[] >>
  qabbrev_tac `V = \st. B st /\ plain_operand st (Var val_var)` >>
  `shape_stable V` by
    (simp[Abbr `V`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var val_var]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `V`
    (shape_under_tac shape_step_emit_inst_guarded_framed `V` >> simp[Abbr `V`, Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
  suspend "setup"
QED
Resume compile_uint2str_shape[setup]:
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. V st /\ plain_operand st (Var v)` >> conj_tac
  >- (shape_under_tac shape_step_fresh_var `V` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `i_var` >> simp[] >>
  qabbrev_tac `IndexFrame = \st. V st /\ plain_operand st (Var i_var)` >>
  `shape_stable IndexFrame` by
    (simp[Abbr `IndexFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var i_var]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `IndexFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `IndexFrame` >> simp[Abbr `IndexFrame`] >> shape_opcode_tac) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. IndexFrame st /\ plain_operand st (Var v)` >> conj_tac
  >- (shape_under_tac shape_step_fresh_var `IndexFrame` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `result_var` >> simp[] >>
  qabbrev_tac `ResultFrame = \st. IndexFrame st /\ plain_operand st (Var result_var)` >>
  `shape_stable ResultFrame` by
    (simp[Abbr `ResultFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var result_var]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `ResultFrame` >>
     simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`] >> shape_opcode_tac) >>
  shape_call_label_tac `ResultFrame` `check_lbl` >>
  shape_call_label_tac `ResultFrame` `cond_lbl` >>
  shape_call_label_tac `ResultFrame` `body_lbl` >>
  shape_call_label_tac `ResultFrame` `zero_lbl` >>
  shape_call_label_tac `ResultFrame` `final_lbl` >>
  shape_call_label_tac `ResultFrame` `exit_lbl` >>
  shape_call_jump_tac `ResultFrame` >> shape_call_block_tac `ResultFrame` >>
  suspend "blocks"
QED
Resume compile_uint2str_shape[blocks]:
  shape_scalar_emit_bind_tac `ResultFrame` `is_zero`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`]) >>
  qabbrev_tac `Z = \st. ResultFrame st /\ plain_operand st is_zero` >>
  `shape_stable Z` by
    (simp[Abbr `Z`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[is_zero]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `Z` >> simp[Abbr `Z`] >> shape_opcode_tac >>
     rpt strip_tac >> gvs[jump_label_ok_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]) >>
  shape_call_block_tac `ResultFrame` >>
  shape_scalar_emit_bind_tac `ResultFrame` `done_op`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`]) >>
  qabbrev_tac `D = \st. ResultFrame st /\ plain_operand st done_op` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `D` >> simp[Abbr `D`] >> shape_opcode_tac >>
     rpt strip_tac >> gvs[jump_label_ok_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]) >>
  shape_call_block_tac `ResultFrame` >>
  suspend "body"
QED
Resume compile_uint2str_shape[body]:
  shape_scalar_emit_bind_tac `ResultFrame` `digit_op`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`]) >>
  shape_scalar_emit_bind_tac `ResultFrame` `char_val` all_tac >>
  qabbrev_tac `C = \st. ResultFrame st /\ plain_operand st char_val` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[char_val]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `C` `buf_plus_nd`
    (simp[Abbr `C`, Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`]) >>
  shape_scalar_emit_bind_tac `C` `pos`
    (simp[Abbr `C`, Abbr `ResultFrame`, Abbr `IndexFrame`]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  shape_scalar_emit_bind_tac `ResultFrame` `new_val`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`]) >>
  qabbrev_tac `N = \st. ResultFrame st /\ plain_operand st new_val` >>
  `shape_stable N` by
    (simp[Abbr `N`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[new_val]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `N` >>
     simp[Abbr `N`, Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`] >> shape_opcode_tac) >>
  shape_scalar_emit_bind_tac `ResultFrame` `new_i`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`]) >>
  qabbrev_tac `NextIndex = \st. ResultFrame st /\ plain_operand st new_i` >>
  `shape_stable NextIndex` by
    (simp[Abbr `NextIndex`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[new_i]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `NextIndex` >>
     simp[Abbr `NextIndex`, Abbr `ResultFrame`, Abbr `IndexFrame`] >> shape_opcode_tac) >>
  shape_call_jump_tac `ResultFrame` >> shape_call_block_tac `ResultFrame` >>
  suspend "finish"
QED
Resume compile_uint2str_shape[finish]:
  shape_scalar_emit_bind_tac `ResultFrame` `zd_pos`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`]) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_void_plain `ResultFrame` >> shape_opcode_tac) >>
  shape_scalar_emit_bind_tac `ResultFrame` `zd_pos2`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`]) >>
  shape_scalar_emit_bind_tac `ResultFrame` `zr_ptr` all_tac >>
  qabbrev_tac `ZeroFrame = \st. ResultFrame st /\ plain_operand st zr_ptr` >>
  `shape_stable ZeroFrame` by
    (simp[Abbr `ZeroFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[zr_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `ZeroFrame`
    (shape_under_tac shape_step_emit_void_plain `ZeroFrame` >> simp[Abbr `ZeroFrame`] >> shape_opcode_tac) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `ZeroFrame` >>
     simp[Abbr `ZeroFrame`, Abbr `ResultFrame`] >> shape_opcode_tac) >>
  shape_call_jump_tac `ResultFrame` >> shape_call_block_tac `ResultFrame` >>
  shape_scalar_emit_bind_tac `ResultFrame` `buf_nd_f`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`]) >>
  shape_scalar_emit_bind_tac `ResultFrame` `nz_ptr`
    (simp[Abbr `ResultFrame`, Abbr `IndexFrame`]) >>
  qabbrev_tac `NonzeroFrame = \st. ResultFrame st /\ plain_operand st nz_ptr` >>
  `shape_stable NonzeroFrame` by
    (simp[Abbr `NonzeroFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[nz_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `NonzeroFrame`
    (shape_under_tac shape_step_emit_void_plain `NonzeroFrame` >>
     simp[Abbr `NonzeroFrame`, Abbr `ResultFrame`, Abbr `IndexFrame`] >> shape_opcode_tac) >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `NonzeroFrame` >>
     simp[Abbr `NonzeroFrame`, Abbr `ResultFrame`] >> shape_opcode_tac) >>
  shape_call_jump_tac `ResultFrame` >> shape_call_block_tac `ResultFrame` >>
  irule shape_step_return >>
  simp[Abbr `ResultFrame`, Abbr `IndexFrame`, Abbr `V`, Abbr `B`, Abbr `P`]
QED
Finalise compile_uint2str_shape[local]

Theorem compile_default_return_path_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [buf_op; result_op; default_op; addr_op])
    (compile_default_return_path cenv return_type default_ty buf_op result_op
      default_op addr_op skip_contract_check min_return_size max_return_size ret_dec_info)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_default_return_path_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf_op;result_op;default_op;addr_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `rds` all_tac >>
  shape_scalar_emit_bind_tac `P` `is_zero` all_tac >>
  qabbrev_tac `Z = \st. P st /\ plain_operand st is_zero` >>
  `shape_stable Z` by
    (simp[Abbr `Z`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[is_zero]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_label_tac `Z` `default_lbl` >>
  shape_call_label_tac `Z` `decode_lbl` >>
  shape_call_label_tac `Z` `exit_lbl` >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `Z` >> shape_opcode_tac >>
      rpt strip_tac >> gvs[Abbr `Z`, jump_label_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
      gvs[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >>
  shape_call_block_tac `P` >>
  shape_call_effect_tac `P`
    (shape_under_tac compile_store_memory_shape_framed `P` >> simp[Abbr `P`]) >>
  shape_call_effect_tac `P`
    (IF_CASES_TAC >> simp[]
     >- (irule shape_step_return >> simp[]) >>
     shape_under_tac compile_extcodesize_check_shape `P` >> simp[Abbr `P`]) >>
  shape_call_jump_tac `P` >> shape_call_block_tac `P` >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_return_value_decode_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `hi` >> simp[] >>
  shape_call_effect_tac `P`
    (shape_under_tac (cj 1 compile_abi_decode_shape_mload) `P` >> simp[Abbr `P`]) >>
  shape_call_jump_tac `P` >> shape_call_block_tac `P` >>
  irule shape_step_return >> simp[Abbr `P`]
QED

Theorem compile_external_call_kwargs_shape:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (value_shape_ok st) arg_vals /\
      EVERY (plain_operand st) [addr_op; call_value; default_op] /\
      (gas_operand st gas_op \/ plain_operand st gas_op))
    (compile_external_call_kwargs cenv addr_op arg_vals arg_types args_mem_size
      args_abi_size method_id_val return_abi_size min_return_size ret_mem_bytes
      use_staticcall call_value gas_op skip_check has_default default_op
      return_type default_ty args_enc_info ret_dec_info)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  qabbrev_tac `V = \st. EVERY (value_shape_ok st) arg_vals` >>
  `shape_stable V` by
    (simp[Abbr `V`, shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
     mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
     disch_then (qspecl_then [`internal`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  qabbrev_tac `G = \st. gas_operand st gas_op \/ plain_operand st gas_op` >>
  `shape_stable G` by
    (simp[Abbr `G`, shape_stable_def] >> metis_tac[gas_operand_mono, plain_operand_mono]) >>
  qabbrev_tac `P = \st. R st /\ V st /\
                     EVERY (plain_operand st) [addr_op;call_value;default_op] /\ G st` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[addr_op;call_value;default_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `P` >> simp[Abbr `P`]) >> qx_gen_tac `buf` >> simp[] >>
  qabbrev_tac `B = \st. P st /\ plain_operand st buf.buf_operand` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `B`
    (shape_under_tac shape_step_emit_void_plain `B` >> simp[Abbr `B`] >> shape_opcode_tac) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- suspend "store_args" >>
  gen_tac >> simp[] >> suspend "call"
QED
Resume compile_external_call_kwargs_shape[store_args]:
  IF_CASES_TAC >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. B st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `B`) >> qx_gen_tac `args_buf` >> simp[] >>
  qabbrev_tac `A = \st. B st /\ plain_operand st args_buf.buf_operand` >>
  `shape_stable A` by
    (simp[Abbr `A`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[args_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. A st` >> conj_tac
  >- (shape_under_tac compile_extcall_store_values_shape `A` >> simp[Abbr `A`] >>
     `!xs (ys : type list) st. EVERY (value_shape_ok st) xs ==>
        EVERY (value_shape_ok st o FST) (ZIP (xs,ys))` by
       (Induct >> Cases_on `ys` >> simp[ZIP_def]) >>
     rpt strip_tac >> first_x_assum irule >> gvs[Abbr `B`, Abbr `P`, Abbr `V`]) >>
  gen_tac >> simp[] >> shape_scalar_emit_bind_tac `A` `args_dst` (simp[Abbr `A`, Abbr `B`]) >>
  shape_call_effect_tac `B`
    (shape_under_tac (cj 2 compile_abi_encode_shape_framed) `A` >> simp[Abbr `A`]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_external_call_kwargs_shape[call]:
  shape_scalar_emit_bind_tac `B` `call_offset` (simp[Abbr `B`]) >>
  qabbrev_tac `C = \st. B st /\ plain_operand st call_offset` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[call_offset]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_effect_tac `C`
    (IF_CASES_TAC >> simp[]
     >- (shape_under_tac compile_extcodesize_check_shape `C` >> simp[Abbr `C`, Abbr `B`, Abbr `P`]) >>
     irule shape_step_return >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. B st /\ plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      shape_under_tac shape_step_emit_op_call_guarded `B` >>
      simp[Abbr `C`, Abbr `B`, Abbr `P`, Abbr `G`] >>
      shape_opcode_tac >> rpt strip_tac >> gvs[gas_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> simp[] >>
  qabbrev_tac `SuccessFrame = \st. B st /\ plain_operand st success` >>
  `shape_stable SuccessFrame` by
    (simp[Abbr `SuccessFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[success]` shape_stable_plain_operands) >> simp[]) >>
  shape_call_label_tac `SuccessFrame` `fail_lbl` >> shape_call_label_tac `SuccessFrame` `cont_lbl` >>
  shape_call_effect_tac `B`
    (shape_under_tac shape_step_emit_inst_guarded_framed `SuccessFrame` >> shape_opcode_tac >>
     rpt strip_tac >> gvs[Abbr `SuccessFrame`, jump_label_ok_def, plain_operand_def,
                         stackPlanTypesTheory.is_label_operand_def]) >>
  shape_call_block_tac `B` >> suspend "propagate"
QED
Resume compile_external_call_kwargs_shape[propagate]:
  shape_scalar_emit_bind_tac `B` `rds` all_tac >>
  qabbrev_tac `D = \st. B st /\ plain_operand st rds` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[rds]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. D st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `D`) >> qx_gen_tac `fail_buf` >> simp[] >>
  qabbrev_tac `FailFrame = \st. D st /\ plain_operand st fail_buf.buf_operand` >>
  `shape_stable FailFrame` by
    (simp[Abbr `FailFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[fail_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
  >- (match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. FailFrame st` >> conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `FailFrame` >> simp[Abbr `FailFrame`, Abbr `D`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >>
      shape_under_tac shape_step_emit_inst_guarded_framed `FailFrame` >> simp[Abbr `FailFrame`, Abbr `D`] >> shape_opcode_tac >>
      rpt strip_tac >> metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >>
  shape_call_block_tac `B` >> suspend "return_value"
QED
Resume compile_external_call_kwargs_shape[return_value]:
  IF_CASES_TAC >> simp[]
  >- (irule shape_step_return >> simp[Abbr `B`, Abbr `P`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  IF_CASES_TAC >> simp[]
  >- (match_mp_tac shape_step_bind >> qexists_tac `\b st. B st /\ plain_operand st b.buf_operand` >> conj_tac
      >- (shape_under_tac compile_alloc_buffer_shape_framed `B`) >> gen_tac >> simp[] >>
      shape_under_tac compile_default_return_path_shape `R` >> simp[Abbr `B`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\b st. B st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `B`) >> qx_gen_tac `result_buf` >> simp[] >>
  qabbrev_tac `ResultFrame = \st. B st /\ plain_operand st result_buf.buf_operand` >>
  `shape_stable ResultFrame` by
    (simp[Abbr `ResultFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[result_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. ResultFrame st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_return_value_decode_shape `ResultFrame` >> simp[Abbr `ResultFrame`, Abbr `B`]) >>
  gen_tac >> simp[] >>
  shape_call_effect_tac `ResultFrame`
    (shape_under_tac (cj 1 compile_abi_decode_shape_mload) `ResultFrame` >> simp[Abbr `ResultFrame`, Abbr `B`]) >>
  irule shape_step_return >> simp[Abbr `ResultFrame`, Abbr `B`, Abbr `P`]
QED
Finalise compile_external_call_kwargs_shape[local]

val shape_external_result_tac =
  irule shape_step_uncurry >> qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac compile_external_call_kwargs_shape `\st. T` >> simp[shape_stable_def] >>
      `!ts vs st. EVERY (value_shape_ok st) vs ==>
         EVERY (value_shape_ok st) (MAP2 ext_call_arg_value ts vs)` by
        (Induct >> namedCases_on `vs` ["", "vv tail"] >> simp[MAP2_DEF] >> rpt gen_tac >> strip_tac >>
         Cases_on `vv` >> gvs[ext_call_arg_value_def, value_shape_ok_def]) >>
      Cases_on `options0` >>
      simp[Abbr `KwFrame`, Abbr `ValuesFrame`, Abbr `AddrFrame`,
           plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  gen_tac >> Cases_on `abi_size_bound cenv.ce_struct_fields wrapped_return = 0` >>
  simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
       mk_ptr_def, loc_shape_ok_def];

val shape_external_gas_tac =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label KwFrame _ _` >>
  `shape_stable KwFrame` by
    (simp[Abbr `KwFrame`] >>
     qpat_assum `shape_stable ValuesFrame` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `options0` >> Cases_on `options1` >> simp[shape_stable_def] >>
     metis_tac[plain_operand_mono]) >>
  Cases_on `options1` >> simp[]
  >- (irule shape_step_uncurry >>
      qexists_tac `\g st. KwFrame st /\ gas_operand st g` >> reverse conj_tac
      >- (shape_under_tac shape_step_emit_op_gas `KwFrame` >> qexists_tac `compiler_label` >> simp[]) >>
      qx_gen_tac `gas_op` >> simp[] >> shape_external_result_tac) >>
  rename1 `SOME gas_op` >> shape_external_result_tac;

Theorem compile_call_ext_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty
      (ExtCall static_flag skip_check (func_name,arg_types,return_type) opts) args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e rest"]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_uncurry >> qexists_tac `\u st. T` >> reverse conj_tac
      >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. T` >>
          simp[shape_stable_def] >> shape_opcode_tac) >>
      gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
                       plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gvs[supported_exprs_exists_every] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `addr_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `ext_call_arg_types cenv arg_types pos_args` >>
  qmatch_goalsub_abbrev_tac `MAP2 ext_call_arg_value call_types` >>
  qmatch_goalsub_abbrev_tac `abi_size_bound cenv.ce_struct_fields wrapped_return` >>
  qabbrev_tac `AddrFrame = \st. cenv_shape_ok st cenv /\ plain_operand st addr_op` >>
  `shape_stable AddrFrame` by
    (simp[Abbr `AddrFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. AddrFrame st /\ EVERY (value_shape_ok st) vs` >> reverse conj_tac
  >- (shape_under_tac compile_multi_vvs_shape `AddrFrame` >> simp[Abbr `AddrFrame`, Abbr `pos_args`, supported_exprs_exists_every] >>
      irule rich_listTheory.EVERY_TAKE >> simp[]) >>
  qx_gen_tac `vals` >> simp[] >>
  qabbrev_tac `ValuesFrame = \st. AddrFrame st /\ EVERY (value_shape_ok st) vals` >>
  `shape_stable ValuesFrame` by
    (simp[Abbr `ValuesFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
     rename1 `shape_extends i LP st st'` >>
     mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
     disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. ValuesFrame st /\
       EVERY (plain_operand st)
         ((case FST vs of NONE => [] | SOME v => [v]) ++
          (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
          (case SND (SND vs) of NONE => [] | SOME v => [FST v]))` >> reverse conj_tac
  >- (drule compile_ext_call_kwargs_shape >> disch_then (fn th => shape_under_tac th `ValuesFrame`) >>
      simp[Abbr `ValuesFrame`, Abbr `AddrFrame`, supported_exprs_exists_every] >>
      irule rich_listTheory.EVERY_DROP >> simp[]) >>
  qx_gen_tac `options` >> PairCases_on `options` >> simp[] >>
  Cases_on `options2`
  >- (simp[] >> suspend "no_default") >>
  rename1 `SOME dflt` >> PairCases_on `dflt` >> simp[] >> suspend "default"
QED
Resume compile_call_ext_shape[no_default]:
  shape_external_gas_tac
QED
Resume compile_call_ext_shape[default]:
  shape_external_gas_tac
QED
Finalise compile_call_ext_shape[local]

Theorem shape_step_emit_multi_op_guarded[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
  (!st id outs. R st /\ EVERY (label_or_plain st) ops ==>
     lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (label_or_plain st) ops) (emit_multi_op opc ops n)
    (\xs st. R st /\ EVERY (plain_operand st) xs)
Proof
  rpt gen_tac >> strip_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `internal` shape_step_emit_multi_op) >>
  disch_then (qspecl_then [`compiler_label`, `R`, `opc`, `ops`, `n`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[shape_step_def] >> disch_then drule_all >> simp[]
QED

Theorem compile_call_int_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty (IntCall func_id) args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >>
  qabbrev_tac `info = cenv.ce_func_info (nsid_to_string func_id)` >>
  PairCases_on `info` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qpat_x_assum `Abbrev _` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[compile_call_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >> qexists_tac `\vs st. EVERY (value_shape_ok st) vs` >> reverse conj_tac
  >- (shape_under_tac compile_multi_vvs_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `vals` >> simp[] >>
  Cases_on `info0 > 0` >> simp[]
  >- suspend "stack_returns" >>
  Cases_on `info1 > 0` >> simp[]
  >- suspend "buffer_return" >> suspend "void_return"
QED
Resume compile_call_int_shape[stack_returns]:
  simp[Once pairTheory.UNCURRY_RAND, combinTheory.o_DEF] >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. EVERY (value_shape_ok st) vals /\ plain_operand st b.buf_operand` >>
  reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. EVERY (value_shape_ok st) vals` >>
      simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
      rename1 `shape_extends i LP st st'` >>
      mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
      disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  qx_gen_tac `rbuf` >> simp[] >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. plain_operand st rbuf.buf_operand /\ EVERY (plain_operand st) vs` >>
  reverse conj_tac
  >- (shape_under_tac compile_stage_intcall_args_shape `\st. plain_operand st rbuf.buf_operand` >>
      simp[] >> mp_tac (Q.SPEC `[rbuf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `invoke_args` >> simp[] >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. plain_operand st rbuf.buf_operand /\ EVERY (plain_operand st) vs` >>
  reverse conj_tac
  >- (shape_under_tac shape_step_emit_multi_op_guarded
        `\st. plain_operand st rbuf.buf_operand /\ EVERY (plain_operand st) invoke_args` >>
      conj_tac
      >- (mp_tac (Q.SPEC `rbuf.buf_operand::invoke_args` shape_stable_plain_operands) >> simp[]) >>
      conj_tac
      >- (shape_opcode_tac >> rpt strip_tac >> gvs[EVERY_MEM] >>
          metis_tac[plain_operand_def, label_or_plain_def]) >>
      simp[EVERY_MEM, label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >>
      metis_tac[]) >>
  qx_gen_tac `results` >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\u st. plain_operand st rbuf.buf_operand` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl,
      value_shape_ok_def, loc_shape_ok_def, base_ptr_def]) >>
  shape_under_tac store_multi_results_shape `\st. plain_operand st rbuf.buf_operand` >>
  mp_tac (Q.SPEC `[rbuf.buf_operand]` shape_stable_plain_operands) >> simp[]
QED
Resume compile_call_int_shape[buffer_return]:
  simp[Once pairTheory.UNCURRY_RAND, combinTheory.o_DEF] >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. EVERY (value_shape_ok st) vals /\ plain_operand st b.buf_operand` >>
  reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. EVERY (value_shape_ok st) vals` >>
      simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac >>
      rename1 `shape_extends i LP st st'` >>
      mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
      disch_then (qspecl_then [`i`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
  qx_gen_tac `rbuf` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\vs st. plain_operand st rbuf.buf_operand /\ EVERY (plain_operand st) vs` >>
  reverse conj_tac
  >- (shape_under_tac compile_stage_intcall_args_shape `\st. plain_operand st rbuf.buf_operand` >>
      mp_tac (Q.SPEC `[rbuf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `invoke_args` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\u st. plain_operand st rbuf.buf_operand` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl,
                     value_shape_ok_def, loc_shape_ok_def, base_ptr_def]) >>
  `!ops. emit_void INVOKE ops = emit_inst INVOKE ops []` by
    simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  shape_under_tac shape_step_emit_inst_guarded_framed
    `\st. plain_operand st rbuf.buf_operand /\ EVERY (plain_operand st) invoke_args` >>
  conj_tac
  >- (mp_tac (Q.SPEC `rbuf.buf_operand::invoke_args` shape_stable_plain_operands) >> simp[]) >>
  conj_tac
  >- (shape_opcode_tac >> rpt strip_tac >> gvs[EVERY_MEM] >>
      metis_tac[plain_operand_def, label_or_plain_def]) >>
  simp[EVERY_MEM, label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]
QED
Resume compile_call_int_shape[void_return]:
  irule shape_step_uncurry >> qexists_tac `\vs st. EVERY (plain_operand st) vs` >>
  reverse conj_tac
  >- (shape_under_tac compile_stage_intcall_args_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `invoke_args` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
                     plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  `!ops. emit_void INVOKE ops = emit_inst INVOKE ops []` by
    simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  shape_under_tac shape_step_emit_inst_guarded_framed `\st. EVERY (plain_operand st) invoke_args` >>
  simp[shape_stable_plain_operands] >> conj_tac
  >- (shape_opcode_tac >> rpt strip_tac >> gvs[EVERY_MEM] >>
      metis_tac[plain_operand_def, label_or_plain_def]) >>
  simp[EVERY_MEM, label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]
QED
Finalise compile_call_int_shape[local]

(* The invalid and CALL/ASSERT tails are shared by the Send argument cases. *)
val shape_send_invalid_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >> qexists_tac `\u st. cenv_shape_ok st cenv` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def, plain_operand_def,
                       stackPlanTypesTheory.is_label_operand_def]) >>
  shape_under_tac shape_step_emit_inst `\st. cenv_shape_ok st cenv` >> shape_opcode_tac >>
  qexists_tac `compiler_label` >> simp[cenv_shape_ok_stable];

val shape_send_call_tac =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label CallFrame _ _` >>
  `shape_stable CallFrame` by
    (simp[Abbr `CallFrame`] >>
     ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[gas_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. CallFrame st /\ plain_operand st v` >> conj_tac
  >- (gen_tac >> simp[] >> irule shape_step_uncurry >>
      qexists_tac `\u st. T` >> conj_tac
      >- (gen_tac >> simp[shape_step_def, shape_extends_refl] >> shape_opcode_tac >>
          simp[value_shape_ok_def] >> shape_opcode_tac) >>
      shape_under_tac shape_step_emit_void_plain `CallFrame` >> shape_opcode_tac) >>
  shape_under_tac shape_step_emit_op_plain `CallFrame` >>
  simp[Abbr `CallFrame`, Abbr `ValFrame`, Abbr `AddrFrame`] >> shape_opcode_tac;

Theorem compile_call_send_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty (Send has_gas) args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e tail"]
  >- shape_send_invalid_tac >> namedCases_on `tail` ["", "val_e gas_es"]
  >- shape_send_invalid_tac >>
  reverse (Cases_on `LENGTH gas_es = (if has_gas then 1 else 0)`)
  >- shape_send_invalid_tac >>
  gvs[supported_exprs_exists_every] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `addr_op` >> simp[] >>
  qabbrev_tac `AddrFrame = \st. cenv_shape_ok st cenv /\ plain_operand st addr_op` >>
  `shape_stable AddrFrame` by
    (simp[Abbr `AddrFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. AddrFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `AddrFrame` >> simp[Abbr `AddrFrame`]) >>
  qx_gen_tac `val_op` >> simp[] >>
  qabbrev_tac `ValFrame = \st. AddrFrame st /\ plain_operand st val_op` >>
  `shape_stable ValFrame` by
    (simp[Abbr `ValFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  reverse (Cases_on `has_gas`) >> gvs[LENGTH_EQ_1]
  >- shape_send_call_tac >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. ValFrame st /\ plain_operand st v` >> conj_tac
  >- (qx_gen_tac `gas_op` >> simp[] >> shape_send_call_tac) >>
  shape_under_tac lower_value_callback_shape `ValFrame` >> simp[Abbr `ValFrame`, Abbr `AddrFrame`]
QED

(* LOG accepts ordinary operands, including the reversed raw topic list. *)
Theorem stmt_log_emit_shape[local]:
  !internal ops.
    shape_step internal compiler_label (\st. EVERY (plain_operand st) ops)
      (emit_inst LOG ops []) (\u st. T)
Proof
  rpt gen_tac >> stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
    simp[shape_stable_plain_operands] >> conj_tac
    >- (simp[EVERY_MEM, label_or_plain_def] >> metis_tac[]) >>
    stmt_shape_emit_simp >>
    simp[EVERY_MEM, plain_operand_def] >>
    rpt strip_tac >> res_tac >> gvs[stackPlanTypesTheory.is_label_operand_def])
QED

Theorem raw_log_topic_exprs_shape[local]:
  ~supported_expr_exists expr_shape_root e ==>
  ~supported_exprs_exists expr_shape_root (raw_log_topic_exprs e)
Proof
  Cases_on `e` >> simp[raw_log_topic_exprs_def, supported_expr_exists_def] >>
  rename1 `Builtin ann bi es` >> Cases_on `bi` >>
  simp[raw_log_topic_exprs_def, supported_expr_exists_def]
QED

Theorem compile_raw_revert_shape[local]:
  shape_step internal compiler_label (\st. plain_operand st data)
    (builtinSystem$compile_raw_revert data) (\u st. T)
Proof
  simp[builtinSystemTheory.compile_raw_revert_def] >>
  irule shape_step_bind >>
  qexists_tac `\n st. plain_operand st n /\ plain_operand st data` >> conj_tac
  >- (qx_gen_tac `n` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st p /\ plain_operand st n` >> conj_tac
      >- (gen_tac >> BETA_TAC >> stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
          simp[stmt_shape_stable_plain, shape_stable_conj, label_or_plain_def] >>
          stmt_shape_emit_simp >>
          simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
          rpt strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def])) >>
      shape_under_tac shape_step_emit_op_plain `\st. plain_operand st n` >>
      simp[stmt_shape_stable_plain] >> shape_opcode_tac) >>
  shape_under_tac shape_step_emit_op_plain `\st. plain_operand st data` >>
  simp[stmt_shape_stable_plain] >> shape_opcode_tac
QED

val shape_raw_return_zero_tac =
  gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def] >>
  shape_opcode_tac;

Theorem compile_call_raw_revert_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty RawRevert args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> namedCases_on `args` ["", "data_e tail"]
  >- shape_send_invalid_tac >> Cases_on `tail`
  >| [ALL_TAC, shape_send_invalid_tac] >>
  gvs[supported_exprs_exists_every] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >> qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `data` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\u st. T` >> conj_tac
  >- shape_raw_return_zero_tac >> irule compile_raw_revert_shape
QED

val shape_raw_log_finish_tac =
  irule shape_step_uncurry >> qexists_tac `\u st. T` >> conj_tac
  >- shape_raw_return_zero_tac >>
  irule shape_step_conseq >> irule_at Any stmt_log_emit_shape >> simp[EVERY_REVERSE] >>
  shape_opcode_tac;

Theorem compile_call_raw_log_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty RawLog args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> namedCases_on `args` ["", "topics_e rest"]
  >- shape_send_invalid_tac >> namedCases_on `rest` ["", "data_e tail"]
  >- shape_send_invalid_tac >> Cases_on `tail`
  >| [ALL_TAC, shape_send_invalid_tac] >>
  gvs[supported_exprs_exists_every] >>
  `~supported_exprs_exists expr_shape_root (raw_log_topic_exprs topics_e)` by
    (irule raw_log_topic_exprs_shape >> simp[]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) vs` >> reverse conj_tac
  >- (shape_under_tac compile_multi_exprs_shape `\st. cenv_shape_ok st cenv` >>
      simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `topic_ops` >> simp[] >>
  qabbrev_tac `TopicFrame = \st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) topic_ops` >>
  `shape_stable TopicFrame` by
    (simp[Abbr `TopicFrame`, shape_stable_conj, cenv_shape_ok_stable,
          shape_stable_plain_operands]) >>
  Cases_on `expr_type data_e = BaseT (BytesT (Fixed 32))` >> simp[]
  >- suspend "word" >> suspend "bytes"
QED
Resume compile_call_raw_log_shape[word]:
  irule shape_step_uncurry >>
  qexists_tac `\b st. TopicFrame st /\ plain_operand st b.buf_operand` >> reverse conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qabbrev_tac `BufFrame = \st. TopicFrame st /\ plain_operand st buf.buf_operand` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. BufFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `BufFrame` >>
      simp[Abbr `BufFrame`, Abbr `TopicFrame`]) >>
  qx_gen_tac `data` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\u st. BufFrame st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >>
      simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_raw_log_finish_tac >>
  simp[Abbr `BufFrame`, Abbr `TopicFrame`, plain_operand_def]
QED
Resume compile_call_raw_log_shape[bytes]:
  irule shape_step_uncurry >>
  qexists_tac `\v st. TopicFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `TopicFrame` >> simp[Abbr `TopicFrame`]) >>
  qx_gen_tac `data` >> simp[] >>
  qabbrev_tac `DataFrame = \st. TopicFrame st /\ plain_operand st data` >>
  `shape_stable DataFrame` by
    (simp[Abbr `DataFrame`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. DataFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `DataFrame` >>
      simp[Abbr `DataFrame`] >> shape_opcode_tac) >>
  qx_gen_tac `data_len` >> simp[] >>
  qabbrev_tac `LenFrame = \st. DataFrame st /\ plain_operand st data_len` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`, shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. LenFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `DataFrame`] >> shape_opcode_tac) >>
  qx_gen_tac `data_ptr` >> simp[] >> shape_raw_log_finish_tac >>
  simp[Abbr `LenFrame`, Abbr `DataFrame`, Abbr `TopicFrame`, plain_operand_def]
QED
Finalise compile_call_raw_log_shape[local]

fun shape_raw_effect_tac frame effect =
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\u st. ("] @ frame @ [QUOTE ") st"]) >> reverse conj_tac
  >- effect >> gen_tac >> simp[];

fun shape_raw_label_tac frame name =
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\l st. compiler_label l /\\ ("] @ frame @ [QUOTE ") st"]) >> reverse conj_tac
  >- (shape_under_tac shape_step_fresh_label frame >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac name >> simp[] >> ho_match_mp_tac shape_step_pure_pre >> strip_tac;

Theorem compile_ifexp_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root cond_e /\
  ~supported_expr_exists expr_shape_root then_e /\
  ~supported_expr_exists expr_shape_root else_e ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_expr_body cfn bfn tfn cenv ty (IfExp annot cond_e then_e else_e))
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `cond_op` >> simp[] >>
  qabbrev_tac `CondFrame = \st. cenv_shape_ok st cenv /\ plain_operand st cond_op` >>
  `shape_stable CondFrame` by
    (simp[Abbr `CondFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[cond_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\x st. CondFrame st /\ plain_operand st (Var x)` >> reverse conj_tac
  >- (shape_under_tac shape_step_fresh_var `CondFrame` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `result_var` >> simp[] >>
  qabbrev_tac `ResultFrame = \st. CondFrame st /\ plain_operand st (Var result_var)` >>
  `shape_stable ResultFrame` by
    (simp[Abbr `ResultFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var result_var]` shape_stable_plain_operands) >> simp[]) >>
  shape_raw_label_tac `ResultFrame` `then_lbl` >>
  shape_raw_label_tac `ResultFrame` `else_lbl` >>
  shape_raw_label_tac `ResultFrame` `exit_lbl` >>
  irule shape_step_uncurry >> qexists_tac `\u st. ResultFrame st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `ResultFrame` >>
      simp[Abbr `ResultFrame`, Abbr `CondFrame`] >> shape_opcode_tac >>
      simp[jump_label_ok_def] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> suspend "branches"
QED

Resume compile_ifexp_shape[branches]:
  shape_raw_effect_tac `ResultFrame`
    (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. ResultFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `ResultFrame` >>
      simp[Abbr `ResultFrame`, Abbr `CondFrame`]) >>
  qx_gen_tac `then_op` >> simp[] >>
  qabbrev_tac `ThenFrame = \st. ResultFrame st /\ plain_operand st then_op` >>
  `shape_stable ThenFrame` by
    (simp[Abbr `ThenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[then_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >> qexists_tac `\u st. ResultFrame st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded_framed `ThenFrame` >>
      simp[Abbr `ThenFrame`, Abbr `ResultFrame`, Abbr `CondFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_raw_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `ResultFrame` >>
     shape_opcode_tac >> simp[jump_label_ok_def]) >>
  shape_raw_effect_tac `ResultFrame`
    (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. ResultFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `ResultFrame` >>
      simp[Abbr `ResultFrame`, Abbr `CondFrame`]) >>
  qx_gen_tac `else_op` >> simp[] >>
  qabbrev_tac `ElseFrame = \st. ResultFrame st /\ plain_operand st else_op` >>
  `shape_stable ElseFrame` by
    (simp[Abbr `ElseFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[else_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_raw_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `ElseFrame` >>
     simp[Abbr `ElseFrame`, Abbr `ResultFrame`, Abbr `CondFrame`] >> shape_opcode_tac) >>
  shape_raw_effect_tac `ResultFrame`
    (shape_under_tac shape_step_emit_inst_guarded_framed `ResultFrame` >>
     shape_opcode_tac >> simp[jump_label_ok_def]) >>
  shape_raw_effect_tac `ResultFrame`
    (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  Cases_on `is_word_type annot` >>
  simp[shape_step_def, shape_extends_refl, value_shape_ok_def, mk_ptr_def,
       Abbr `ResultFrame`, loc_shape_ok_def]
QED

Finalise compile_ifexp_shape[local]

fun shape_raw_name_tac frame tidy vvname opname =
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\v st. ("] @ frame @ [QUOTE ") st /\\ value_shape_ok st v"]) >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any compile_name_vv_shape >> qexists_tac frame >> simp[cenv_shape_ok_stable] >> tidy) >>
  qx_gen_tac vvname >> simp[] >> irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\v st. ("] @ frame @ [QUOTE ") st /\\ plain_operand st v"]) >> reverse conj_tac
  >- shape_unwrap_value_tac frame >>
  qx_gen_tac opname >> simp[];


Theorem shape_step_as_stack_val[local]:
  shape_step internal compiler_label P m (\op st. plain_operand st op) ==>
  shape_step internal compiler_label P (\st. as_stack_val ty (m st))
    (\v st. value_shape_ok st v)
Proof
  simp[shape_step_def] >> rpt strip_tac >> Cases_on `m st` >>
  gvs[as_stack_val_def, value_shape_ok_def] >> first_x_assum drule_all >> simp[]
QED

fun shape_mod_names_prefix_tac def =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  shape_raw_name_tac `\st. cenv_shape_ok st cenv` all_tac `av` `va` >>
  qabbrev_tac `AFrame = \st. cenv_shape_ok st cenv /\ plain_operand st va` >>
  `shape_stable AFrame` by
    (simp[Abbr `AFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[va]` shape_stable_plain_operands) >> simp[]) >>
  shape_raw_name_tac `AFrame` (simp[Abbr `AFrame`]) `bv` `vb`;

val shape_mod_names_third_tac =
  qabbrev_tac `BFrame = \st. AFrame st /\ plain_operand st vb` >>
  `shape_stable BFrame` by
    (simp[Abbr `BFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[vb]` shape_stable_plain_operands) >> simp[]) >>
  shape_raw_name_tac `BFrame` (simp[Abbr `BFrame`, Abbr `AFrame`]) `mv` `vm`;

Theorem compile_mod_names_shape:
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_addmod_names cenv ret_ty aty a bty b mty m) (\v st. value_shape_ok st v) /\
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_mulmod_names cenv ret_ty aty a bty b mty m) (\v st. value_shape_ok st v) /\
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_powmod256_names cenv ret_ty aty a bty b) (\v st. value_shape_ok st v)
Proof
  conj_tac >- (shape_mod_names_prefix_tac compile_addmod_names_def >> suspend "add_tail") >>
  conj_tac >- (shape_mod_names_prefix_tac compile_mulmod_names_def >> suspend "mul_tail") >>
  shape_mod_names_prefix_tac compile_powmod256_names_def >> suspend "pow_tail"
QED

Resume compile_mod_names_shape[add_tail]:
  shape_mod_names_third_tac >> irule shape_step_as_stack_val >>
  irule shape_step_conseq >> irule_at Any compile_addmod_shape >>
  qexists_tac `\st. T` >> simp[shape_stable_def, Abbr `BFrame`, Abbr `AFrame`]
QED
Resume compile_mod_names_shape[mul_tail]:
  shape_mod_names_third_tac >> irule shape_step_as_stack_val >>
  irule shape_step_conseq >> irule_at Any compile_mulmod_shape >>
  qexists_tac `\st. T` >> simp[shape_stable_def, Abbr `BFrame`, Abbr `AFrame`]
QED
Resume compile_mod_names_shape[pow_tail]:
  irule shape_step_as_stack_val >>
  irule shape_step_conseq >> irule_at Any compile_pow_mod256_shape >>
  qexists_tac `\st. T` >> simp[shape_stable_def, Abbr `AFrame`]
QED
Finalise compile_mod_names_shape[local]

val shape_pop_case_tac =
  ntac 3 (qpat_x_assum `!ce. _` kall_tac) >>
  irule shape_step_uncurry >>
  qexists_tac `\op st. cenv_shape_ok st cenv /\ plain_operand st op` >> reverse conj_tac
  >- (shape_under_tac compile_dynarray_pop_shape `\st. cenv_shape_ok st cenv` >>
      simp[cenv_shape_ok_stable, compile_target_base_shape] >>
      rpt conj_tac >> rpt strip_tac >> gvs[] >> CASE_TAC >> simp[]) >>
  gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def, mk_ptr_def] >>
  rpt strip_tac >> metis_tac[infer_array_location_shape];

Theorem shape_step_as_memory_val[local]:
  shape_step internal compiler_label P m (\op st. plain_operand st op) ==>
  shape_step internal compiler_label P (\st. as_ptr_val ty LocMemory (m st))
    (\v st. value_shape_ok st v)
Proof
  simp[shape_step_def] >> rpt strip_tac >> Cases_on `m st` >>
  gvs[as_ptr_val_def, value_shape_ok_def, mk_ptr_def] >> first_x_assum drule_all >> simp[]
QED

Theorem compile_blockhash_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st n_op)
    (compile_blockhash n_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinMiscTheory.compile_blockhash_def] >>
  qabbrev_tac `P = \st. R st /\ plain_operand st n_op` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[n_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `current` all_tac >>
  qabbrev_tac `C = \st. P st /\ plain_operand st current` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[current]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `C` `lower` (simp[Abbr `C`]) >>
  shape_scalar_emit_bind_tac `C` `too_old` (simp[Abbr `C`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `C` `ok` all_tac >>
  shape_scalar_assert_tac `C` >>
  shape_scalar_emit_bind_tac `C` `range_op` (simp[Abbr `C`, Abbr `P`]) >>
  shape_scalar_assert_tac `C` >>
  shape_under_tac shape_step_emit_op_plain `R` >>
  simp[Abbr `C`, Abbr `P`] >> shape_opcode_tac
QED

fun shape_dispatch_unary_start_tac arity_def body_def =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> simp[] >> gvs[arity_def]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `op` >> simp[];

val shape_dispatch_unary_prefix_tac =
  shape_dispatch_unary_start_tac builtin_arity_def compile_builtin_dispatch_body_def;

fun shape_dispatch_unary_tac rule =
  shape_dispatch_unary_prefix_tac >> irule shape_step_as_stack_val >>
  shape_under_tac rule `\st. T` >> simp[shape_stable_def];

fun shape_dispatch_lower_tac frame name tidy =
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\op st. ("] @ frame @ [QUOTE ") st /\\ plain_operand st op"]) >> reverse conj_tac
  >- (shape_under_tac lower_value_callback_shape frame >> simp[] >> tidy) >>
  qx_gen_tac name >> simp[];

fun shape_dispatch_binary_start_tac arity_def body_def =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 1 args)` by
    (irule expr_shape_list_el >> gvs[arity_def]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `va` all_tac >>
  qabbrev_tac `AFrame = \st. cenv_shape_ok st cenv /\ plain_operand st va` >>
  `shape_stable AFrame` by
    (simp[Abbr `AFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[va]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `AFrame` `vb` (simp[Abbr `AFrame`]);

val shape_dispatch_binary_prefix_tac =
  shape_dispatch_binary_start_tac builtin_arity_def compile_builtin_dispatch_body_def;

fun shape_dispatch_modular_tac rule =
  `~supported_expr_exists expr_shape_root (EL 2 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  shape_dispatch_binary_prefix_tac >>
  qabbrev_tac `BFrame = \st. AFrame st /\ plain_operand st vb` >>
  `shape_stable BFrame` by
    (simp[Abbr `BFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[vb]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `BFrame` `vc` (simp[Abbr `BFrame`, Abbr `AFrame`]) >>
  irule shape_step_as_stack_val >> shape_under_tac rule `\st. T` >>
  simp[shape_stable_def, Abbr `BFrame`, Abbr `AFrame`];

fun shape_dispatch_hash_tac bytes_rule bytesm_rule word_rule =
  Cases_on `is_bytestring_type (expr_type (HD args))`
  >- shape_dispatch_unary_tac bytes_rule >>
  Cases_on `expr_type (HD args)`
  >~ [`expr_type (HD args) = BaseT bt`]
  >- (Cases_on `bt`
      >~ [`expr_type (HD args) = BaseT (BytesT sz)`]
      >- (Cases_on `sz`
          >~ [`expr_type (HD args) = BaseT (BytesT (Fixed n))`]
          >- shape_dispatch_unary_tac bytesm_rule >>
          shape_dispatch_unary_tac word_rule) >>
      shape_dispatch_unary_tac word_rule) >>
  shape_dispatch_unary_tac word_rule;

val shape_dispatch_raw_unwrap_tac =
  `shape_stable (\st:compile_state. T)` by simp[shape_stable_def] >>
  irule shape_step_uncurry >> qexists_tac `\v st. value_shape_ok st v` >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  qx_gen_tac `vv` >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (shape_unwrap_value_tac `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `src_op` >> simp[];

Theorem compile_type_builtin_dispatch_body_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> Cases_on `tb`
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Convert _ _`]
  >- suspend "convert"
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Empty _ _`]
  >- suspend "empty"
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Extract32 _ _`]
  >- suspend "extract"
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiEncode ensure mid) _ _`]
  >- suspend "encode"
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiDecode mt) _ _`]
  >- suspend "decode" >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def] >>
  Cases_on `type_bounds ret_ty` >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def] >>
  shape_opcode_tac
QED

Resume compile_type_builtin_dispatch_body_shape[convert]:
  shape_dispatch_unary_start_tac type_builtin_arity_def compile_type_builtin_dispatch_body_def >>
  Cases_on `ret_ty` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_as_stack_val >>
  shape_under_tac compile_type_convert_shape `\st. T` >> simp[shape_stable_def]
QED
Resume compile_type_builtin_dispatch_body_shape[empty]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def] >>
  Cases_on `is_word_type ret_ty` >> simp[]
  >- (simp[shape_step_def, shape_extends_refl, value_shape_ok_def] >> shape_opcode_tac) >>
  irule shape_step_uncurry >> qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (shape_under_tac compile_builtin_empty_complex_shape `\st. T` >> simp[shape_stable_def]) >>
  gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def, mk_ptr_def]
QED
Resume compile_type_builtin_dispatch_body_shape[extract]:
  shape_dispatch_binary_start_tac type_builtin_arity_def compile_type_builtin_dispatch_body_def >>
  irule shape_step_uncurry >> qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (shape_under_tac compile_extract32_shape `\st. T` >> simp[shape_stable_def, Abbr `AFrame`]) >>
  gen_tac >> simp[] >> irule shape_step_as_stack_val >>
  shape_under_tac compile_clamp_extract32_shape `\st. T` >> simp[shape_stable_def]
QED
Resume compile_type_builtin_dispatch_body_shape[encode]:
  Cases_on `is_word_type (expr_type (HD args))`
  >- (shape_dispatch_unary_start_tac type_builtin_arity_def compile_type_builtin_dispatch_body_def >>
      qabbrev_tac `P = \st. plain_operand st op` >>
      `shape_stable P` by
        (mp_tac (Q.SPEC `[op]` shape_stable_plain_operands) >> simp[Abbr `P`]) >>
      irule shape_step_uncurry >>
      qexists_tac `\buf st. P st /\ plain_operand st buf.buf_operand` >> reverse conj_tac
      >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[]) >>
      qx_gen_tac `buf` >> simp[] >>
      `shape_stable (\st. plain_operand st buf.buf_operand)` by
        (mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
      irule shape_step_uncurry >>
      qexists_tac `\u st. plain_operand st buf.buf_operand` >> reverse conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `\st. plain_operand st buf.buf_operand` >>
          simp[Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> irule shape_step_as_memory_val >>
      shape_under_tac lower_abi_encode_shape `\st. T` >> simp[shape_stable_def]) >>
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[type_builtin_arity_def]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_raw_unwrap_tac >> irule shape_step_as_memory_val >>
  shape_under_tac lower_abi_encode_shape `\st. T` >> simp[shape_stable_def]
QED
Resume compile_type_builtin_dispatch_body_shape[decode]:
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[type_builtin_arity_def]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_type_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_raw_unwrap_tac >> irule shape_step_as_memory_val >>
  shape_under_tac lower_abi_decode_shape `\st. T` >> simp[shape_stable_def]
QED
Finalise compile_type_builtin_dispatch_body_shape[local]

fun shape_dispatch_raw_child_tac frame name tidy =
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\v st. ("] @ frame @ [QUOTE ") st /\\ value_shape_ok st v"]) >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      qexists_tac frame >> simp[] >>
      qexistsl_tac [`\v st. value_shape_ok st v`, `\st. cenv_shape_ok st cenv`, `compiler_label`] >>
      simp[] >> tidy) >>
  qx_gen_tac `raw_vv` >> simp[] >>
  irule shape_step_uncurry >>
  qexists_tac ([QUOTE "\\v st. ("] @ frame @ [QUOTE ") st /\\ plain_operand st v"]) >> reverse conj_tac
  >- shape_unwrap_value_tac frame >>
  qx_gen_tac name >> simp[];

Theorem compile_bytestring_hash_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st ptr_op)
    (compile_bytestring_hash ptr_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[ptr_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `data_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `len_op` (simp[Abbr `G`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac
QED

local
val shape_dispatch_len_tac =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  Cases_on `is_msg_data (HD args)` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >- (irule shape_step_as_stack_val >>
      shape_under_tac compile_builtin_calldatasize_shape `\st. T` >> simp[shape_stable_def]) >>
  irule shape_step_uncurry >> qexists_tac `\v st. value_shape_ok st v` >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  qx_gen_tac `vv` >> simp[] >> irule shape_step_as_stack_val >>
  Cases_on `vv` >> simp[value_shape_ok_def, vv_operand_def, vv_location_def]
  >- (shape_under_tac compile_builtin_len_shape `\st. T` >> simp[shape_stable_def]) >>
  rename1 `plain_operand _ locptr.ptr_operand` >>
  Cases_on `locptr.ptr_location = LocCode`
  >- simp[shape_step_def] >>
  shape_under_tac compile_builtin_len_shape `\st. T` >> simp[shape_stable_def]
;
val shape_dispatch_ecrecover_tac =
  `~supported_expr_exists expr_shape_root (EL 2 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 3 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  shape_dispatch_binary_prefix_tac >>
  qabbrev_tac `BFrame = \st. AFrame st /\ plain_operand st vb` >>
  `shape_stable BFrame` by
    (simp[Abbr `BFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[vb]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `BFrame` `vc` (simp[Abbr `BFrame`, Abbr `AFrame`]) >>
  qabbrev_tac `CFrame = \st. BFrame st /\ plain_operand st vc` >>
  `shape_stable CFrame` by
    (simp[Abbr `CFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[vc]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `CFrame` `vd` (simp[Abbr `CFrame`, Abbr `BFrame`, Abbr `AFrame`]) >>
  irule shape_step_as_stack_val >> shape_under_tac compile_ecrecover_shape `\st. T` >>
  simp[shape_stable_def, Abbr `CFrame`, Abbr `BFrame`, Abbr `AFrame`]
;
val shape_dispatch_maketuple_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. cenv_shape_ok st cenv /\ plain_operand st b.buf_operand` >> reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. cenv_shape_ok st cenv` >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >> irule shape_step_as_memory_val >>
  shape_under_tac compile_make_tuple_shape `\st. T` >> simp[shape_stable_def]
;
val shape_dispatch_makehomogeneous_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. cenv_shape_ok st cenv /\ plain_operand st b.buf_operand` >> reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. cenv_shape_ok st cenv` >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >> irule shape_step_as_memory_val >>
  shape_under_tac compile_make_array_shape `\st. T` >> simp[shape_stable_def]
;
val shape_dispatch_concat_tac =
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. cenv_shape_ok st cenv /\ plain_operand st b.buf_operand` >> reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `\st. cenv_shape_ok st cenv` >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qabbrev_tac `P = \st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >> qexists_tac `\v st. P st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `data_ptr` >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\v st. P st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac compile_concat_shape `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `offset_op` >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\u st. P st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[shape_step_def, shape_extends_refl, Abbr `P`, value_shape_ok_def, base_ptr_def]
;
val shape_dispatch_ecadd_tac =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 1 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_raw_child_tac `\st. cenv_shape_ok st cenv` `va` all_tac >>
  qabbrev_tac `AFrame = \st. cenv_shape_ok st cenv /\ plain_operand st va` >>
  `shape_stable AFrame` by
    (simp[Abbr `AFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[va]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_raw_child_tac `AFrame` `vb` (simp[Abbr `AFrame`]) >>
  irule shape_step_as_memory_val >> shape_under_tac compile_ecadd_points_shape `\st. T` >>
  simp[shape_stable_def, Abbr `AFrame`]
;
val shape_dispatch_ecmul_tac =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 1 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_raw_child_tac `\st. cenv_shape_ok st cenv` `va` all_tac >>
  qabbrev_tac `AFrame = \st. cenv_shape_ok st cenv /\ plain_operand st va` >>
  `shape_stable AFrame` by
    (simp[Abbr `AFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[va]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `AFrame` `vb` (simp[Abbr `AFrame`]) >>
  irule shape_step_as_memory_val >> shape_under_tac compile_ecmul_point_shape `\st. T` >>
  simp[shape_stable_def, Abbr `AFrame`]
;
val shape_dispatch_bytescompare_tac =
  `HD (TL args) = EL 1 args` by
    REWRITE_TAC[arithmeticTheory.ONE, listTheory.EL] >>
  gvs[] >> (shape_dispatch_binary_prefix_tac >>
  qabbrev_tac `BFrame = \st. AFrame st /\ plain_operand st vb` >>
  `shape_stable BFrame` by
    (simp[Abbr `BFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[vb]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\h st. BFrame st /\ plain_operand st h` >> reverse conj_tac
  >- (shape_under_tac compile_bytestring_hash_shape `BFrame` >> simp[Abbr `BFrame`, Abbr `AFrame`]) >>
  qx_gen_tac `h1` >> simp[] >>
  qabbrev_tac `HFrame = \st. plain_operand st h1` >>
  `shape_stable HFrame` by
    (mp_tac (Q.SPEC `[h1]` shape_stable_plain_operands) >> simp[Abbr `HFrame`]) >>
  irule shape_step_uncurry >>
  qexists_tac `\h st. HFrame st /\ plain_operand st h` >> reverse conj_tac
  >- (shape_under_tac compile_bytestring_hash_shape `HFrame` >> simp[Abbr `BFrame`, Abbr `HFrame`]) >>
  qx_gen_tac `h2` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  FIRST [
    irule shape_step_as_stack_val >> shape_under_tac shape_step_emit_op_plain `\st. T` >>
      simp[shape_stable_def, Abbr `HFrame`] >> shape_opcode_tac,
  irule shape_step_uncurry >> qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `\st. T` >> simp[shape_stable_def, Abbr `HFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_as_stack_val >>
  shape_under_tac shape_step_emit_op_plain `\st. T` >> simp[shape_stable_def] >> shape_opcode_tac])
;
val dispatch_member_variable_tac = (
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (HD (TL args))` by
    (irule expr_shape_list_hd >> Cases_on `args` >> gvs[builtin_arity_def, supported_expr_exists_def]) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `needle` all_tac >>
  qabbrev_tac `NeedleFrame = \st. cenv_shape_ok st cenv /\ plain_operand st needle` >>
  `shape_stable NeedleFrame` by
    (simp[Abbr `NeedleFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[needle]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. NeedleFrame st /\ value_shape_ok st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      qexists_tac `NeedleFrame` >> simp[] >>
      qexistsl_tac [`\v st. value_shape_ok st v`, `\st. cenv_shape_ok st cenv`, `compiler_label`] >>
      simp[Abbr `NeedleFrame`] >> first_x_assum irule >> gvs[]) >>
  qx_gen_tac `arr_vv` >> simp[] >> irule shape_step_as_stack_val >>
  shape_under_tac compile_var_array_membership_shape `\st. T` >>
  simp[shape_stable_def, Abbr `NeedleFrame`])
;
val dispatch_member_literal_tac =
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (HD (TL args))` by
    (irule expr_shape_list_hd >> Cases_on `args` >> gvs[builtin_arity_def, supported_expr_exists_def]) >>
  `~supported_exprs_exists expr_shape_root elems` by gvs[expr_shape_builtin] >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `needle` all_tac >>
  qabbrev_tac `NeedleFrame = \st. plain_operand st needle` >>
  `shape_stable NeedleFrame` by
    (mp_tac (Q.SPEC `[needle]` shape_stable_plain_operands) >> simp[Abbr `NeedleFrame`]) >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. NeedleFrame st /\ EVERY (plain_operand st) vs` >> reverse conj_tac
  >- (shape_under_tac compile_multi_exprs_shape `NeedleFrame` >> simp[Abbr `NeedleFrame`]) >>
  qx_gen_tac `ops` >> simp[] >> Cases_on `b = In` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (irule shape_step_as_stack_val >>
   FIRST [shape_under_tac compile_list_membership_in_shape `\st. T`,
          shape_under_tac compile_list_membership_notin_shape `\st. T`] >>
   simp[shape_stable_def, Abbr `NeedleFrame`])
;
val dispatch_slice_calldata_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `start_op` all_tac >>
  qabbrev_tac `StartFrame = \st. cenv_shape_ok st cenv /\ plain_operand st start_op` >>
  `shape_stable StartFrame` by
    (simp[Abbr `StartFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `StartFrame` `len_op` (simp[Abbr `StartFrame`]) >>
  irule shape_step_as_memory_val >> shape_under_tac compile_slice_calldata_shape `\st. T` >>
  simp[shape_stable_def, Abbr `StartFrame`]
;
val dispatch_slice_code_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `start_op` all_tac >>
  qabbrev_tac `StartFrame = \st. cenv_shape_ok st cenv /\ plain_operand st start_op` >>
  `shape_stable StartFrame` by
    (simp[Abbr `StartFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `StartFrame` `len_op` (simp[Abbr `StartFrame`]) >>
  irule shape_step_as_memory_val >> shape_under_tac compile_slice_code_shape `\st. T` >>
  simp[shape_stable_def, Abbr `StartFrame`]
;
val dispatch_slice_extcode_tac =
  `~supported_expr_exists expr_shape_root (extcode_addr_expr (HD args))` by
    (irule expr_shape_extcode_addr >> simp[]) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `addr_op` all_tac >>
  qabbrev_tac `AddrFrame = \st. cenv_shape_ok st cenv /\ plain_operand st addr_op` >>
  `shape_stable AddrFrame` by
    (simp[Abbr `AddrFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `AddrFrame` `start_op` (simp[Abbr `AddrFrame`]) >>
  qabbrev_tac `StartFrame = \st. AddrFrame st /\ plain_operand st start_op` >>
  `shape_stable StartFrame` by
    (simp[Abbr `StartFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `StartFrame` `len_op` (simp[Abbr `StartFrame`, Abbr `AddrFrame`]) >>
  qabbrev_tac `LenFrame = \st. StartFrame st /\ plain_operand st len_op` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. LenFrame st /\ EVERY (plain_operand st) [FST v; SND v]` >> reverse conj_tac
  >- (shape_under_tac compile_slice_out_buf_shape `LenFrame` >> simp[Abbr `LenFrame`]) >>
  Cases >> simp[] >> irule shape_step_as_memory_val >>
  shape_under_tac compile_slice_extcode_shape `\st. T` >>
  simp[shape_stable_def, Abbr `LenFrame`, Abbr `StartFrame`, Abbr `AddrFrame`]
;
val dispatch_slice_bytes_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `src_op` all_tac >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [FST v; SND v]` >> reverse conj_tac
  >- (shape_under_tac compile_bytestring_src_shape `\st. cenv_shape_ok st cenv` >> simp[]) >>
  Cases >> simp[] >> rename1 `compile_slice_data src_len src_data` >>
  qabbrev_tac `SrcFrame = \st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [src_len;src_data]` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[src_len;src_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `SrcFrame` `start_op` (simp[Abbr `SrcFrame`]) >>
  qabbrev_tac `StartFrame = \st. SrcFrame st /\ plain_operand st start_op` >>
  `shape_stable StartFrame` by
    (simp[Abbr `StartFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `StartFrame` `len_op` (simp[Abbr `StartFrame`, Abbr `SrcFrame`]) >>
  irule shape_step_as_memory_val >> shape_under_tac compile_slice_data_shape `\st. T` >>
  simp[shape_stable_def, Abbr `StartFrame`, Abbr `SrcFrame`]
;
val dispatch_slice_fixed_tac =
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  shape_dispatch_lower_tac `\st. cenv_shape_ok st cenv` `src_op` all_tac >>
  qabbrev_tac `SrcFrame = \st. cenv_shape_ok st cenv /\ plain_operand st src_op` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[src_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `SrcFrame` `start_op` (simp[Abbr `SrcFrame`]) >>
  qabbrev_tac `StartFrame = \st. SrcFrame st /\ plain_operand st start_op` >>
  `shape_stable StartFrame` by
    (simp[Abbr `StartFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[start_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_dispatch_lower_tac `StartFrame` `len_op` (simp[Abbr `StartFrame`, Abbr `SrcFrame`]) >>
  qabbrev_tac `LenFrame = \st. StartFrame st /\ plain_operand st len_op` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\b st. LenFrame st /\ plain_operand st b.buf_operand` >> reverse conj_tac
  >- (shape_under_tac compile_alloc_buffer_shape_framed `LenFrame` >> simp[Abbr `LenFrame`]) >>
  qx_gen_tac `buf` >> simp[] >>
  qabbrev_tac `BufFrame = \st. LenFrame st /\ plain_operand st buf.buf_operand` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >> qexists_tac `\u st. BufFrame st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\v st. BufFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  qx_gen_tac `data_ptr` >> simp[] >>
  irule shape_step_uncurry >> qexists_tac `\u st. BufFrame st` >> reverse conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >>
      simp[Abbr `BufFrame`, Abbr `LenFrame`, Abbr `StartFrame`, Abbr `SrcFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_as_memory_val >>
  shape_under_tac compile_slice_memory_shape `\st. T` >>
  simp[shape_stable_def, Abbr `BufFrame`, Abbr `LenFrame`, Abbr `StartFrame`, Abbr `SrcFrame`]
;
in
Theorem compile_builtin_dispatch_body_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  bi <> Env MsgGas /\ builtin_arity bi <= LENGTH args /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> Cases_on `bi`
  >~ [`compile_builtin_dispatch_body _ _ _ _ Abs _`]
  >- shape_dispatch_unary_tac compile_builtin_abs_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ Neg _`]
  >- shape_dispatch_unary_tac compile_neg_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ Ceil _`]
  >- shape_dispatch_unary_tac compile_ceil_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ Floor _`]
  >- shape_dispatch_unary_tac compile_floor_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ CalldataLen _`]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_as_stack_val >> shape_under_tac compile_builtin_calldatasize_shape `\st. T` >>
      simp[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Env item) _`]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_as_stack_val >> shape_under_tac compile_env_var_shape `\st. T` >>
      gvs[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Not _`]
  >- (shape_dispatch_unary_prefix_tac >> Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule shape_step_as_stack_val
      >- (shape_under_tac shape_step_emit_op_plain `\st. T` >> simp[shape_stable_def] >> shape_opcode_tac) >>
      shape_under_tac compile_invert_shape `\st. T` >> simp[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue denom) _`]
  >- (shape_dispatch_unary_prefix_tac >> Cases_on `is_decimal_type (expr_type (HD args))` >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule shape_step_as_stack_val
      >- (shape_under_tac compile_as_wei_value_decimal_shape `\st. T` >> simp[shape_stable_def]) >>
      shape_under_tac compile_as_wei_value_int_shape `\st. T` >> simp[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ AddMod _`]
  >- shape_dispatch_modular_tac compile_addmod_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ MulMod _`]
  >- shape_dispatch_modular_tac compile_mulmod_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ PowMod256 _`]
  >- (shape_dispatch_binary_prefix_tac >> irule shape_step_as_stack_val >>
      shape_under_tac compile_pow_mod256_shape `\st. T` >> simp[shape_stable_def, Abbr `AFrame`])
  >~ [`compile_builtin_dispatch_body _ _ _ _ BlockHash _`]
  >- shape_dispatch_unary_tac compile_blockhash_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ BlobHash _`]
  >- (shape_dispatch_unary_prefix_tac >> irule shape_step_as_stack_val >>
      simp[builtinMiscTheory.compile_blobhash_def] >>
      shape_under_tac shape_step_emit_op_plain `\st. T` >> simp[shape_stable_def] >> shape_opcode_tac)
  >~ [`compile_builtin_dispatch_body _ _ _ _ MethodId _`]
  >- (`~supported_expr_exists expr_shape_root (HD args)` by
        (irule expr_shape_list_hd >> simp[] >> gvs[builtin_arity_def]) >>
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_builtin_dispatch_body_def] >>
      Cases_on `method_id_literal (HD args)` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
      >- (irule shape_step_uncurry >>
          qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
          >- (shape_under_tac lower_value_callback_shape `\st. T` >> simp[shape_stable_def]) >>
          qx_gen_tac `op` >> simp[] >>
          Cases_on `ret_ty = BaseT (BytesT (Fixed 4))` >> simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV)
          >- (irule shape_step_as_stack_val >>
              shape_under_tac compile_method_id_runtime_shape `\st. T` >> simp[shape_stable_def]) >>
          irule shape_step_as_memory_val >>
          shape_under_tac compile_method_id_runtime_shape `\st. T` >> simp[shape_stable_def]) >>
      irule shape_step_conseq >> irule_at Any compile_literal_vv_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (CalldataSlice n) _`]
  >- (shape_dispatch_unary_prefix_tac >> irule shape_step_as_memory_val >>
      shape_under_tac compile_slice_calldata_shape `\st. T` >> simp[shape_stable_def] >> shape_opcode_tac)
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc item) _`]
  >- (`~supported_expr_exists expr_shape_root (HD args)` by
        (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_builtin_dispatch_body_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_as_stack_val >> shape_under_tac compile_acc_shape `\st. T` >> simp[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Keccak256 _`]
  >- shape_dispatch_hash_tac compile_keccak256_bytes_shape compile_keccak256_bytesm_shape compile_keccak256_word_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ Sha256 _`]
  >- shape_dispatch_hash_tac compile_sha256_bytes_shape compile_sha256_bytesm_shape compile_sha256_word_shape
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Uint2Str max_len) _`]
  >- (shape_dispatch_unary_prefix_tac >> irule shape_step_as_memory_val >>
      shape_under_tac compile_uint2str_shape `\st. T` >> simp[shape_stable_def])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Len _`]
  >- shape_dispatch_len_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ ECRecover _`]
  >- shape_dispatch_ecrecover_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray elem_ty_opt bnd) _`]
  >- (assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >> Cases_on `elem_ty_opt`
      >- shape_dispatch_maketuple_tac >> shape_dispatch_makehomogeneous_tac)
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Concat max_len) _`]
  >- shape_dispatch_concat_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ ECAdd _`]
  >- shape_dispatch_ecadd_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ ECMul _`]
  >- shape_dispatch_ecmul_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop b) _`]
  >- (Cases_on `(b = In \/ b = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
      >- (Cases_on `HD (TL args)`
          >~ [`HD (TL args) = Builtin ann bi elems`]
          >- (Cases_on `bi`
              >~ [`HD (TL args) = Builtin ann (MakeArray opt bnd) elems`]
              >- dispatch_member_literal_tac >> dispatch_member_variable_tac) >>
          dispatch_member_variable_tac) >>
      Cases_on `is_bytestring_type (expr_type (HD args)) /\ (b = Eq \/ b = NotEq)`
      >- shape_dispatch_bytescompare_tac >>
      `HD (TL args) = EL 1 args` by
        REWRITE_TAC[arithmeticTheory.ONE, listTheory.EL] >>
      gvs[] >> shape_dispatch_binary_prefix_tac >> irule shape_step_as_stack_val >>
      shape_under_tac compile_binop_shape_framed `\st. T` >> simp[shape_stable_def, Abbr `AFrame`]) >>
  `~supported_expr_exists expr_shape_root (HD args)` by
    (irule expr_shape_list_hd >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 1 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  `~supported_expr_exists expr_shape_root (EL 2 args)` by
    (irule expr_shape_list_el >> gvs[builtin_arity_def]) >>
  assume_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
  Cases_on `is_msg_data (HD args)` >- dispatch_slice_calldata_tac >>
  Cases_on `is_self_code (HD args)` >- dispatch_slice_code_tac >>
  Cases_on `is_extcode (HD args)` >- dispatch_slice_extcode_tac >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >- dispatch_slice_bytes_tac >>
  dispatch_slice_fixed_tac
QED
end

Theorem compile_expr_body_addmod_names[local]:
  compile_expr_body cfn bfn tfn ce ty
    (Builtin ann AddMod [Name at a; Name bt b; Name mt m]) =
  compile_addmod_names ce ann at a bt b mt m
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def]
QED

Theorem compile_expr_body_mulmod_names[local]:
  compile_expr_body cfn bfn tfn ce ty
    (Builtin ann MulMod [Name at a; Name bt b; Name mt m]) =
  compile_mulmod_names ce ann at a bt b mt m
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def]
QED

Theorem compile_expr_body_powmod_names[local]:
  compile_expr_body cfn bfn tfn ce ty
    (Builtin ann PowMod256 [Name at a; Name bt b]) =
  compile_powmod256_names ce ann at a bt b
Proof
  simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def]
QED

Theorem compile_expr_body_builtin_default[local]:
  ~(?at a bt b mt m. bi = AddMod /\ es = [Name at a; Name bt b; Name mt m]) /\
  ~(?at a bt b mt m. bi = MulMod /\ es = [Name at a; Name bt b; Name mt m]) /\
  ~(?at a bt b. bi = PowMod256 /\ es = [Name at a; Name bt b]) ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi es) = bfn ce ann ty bi es
Proof
  strip_tac >> Cases_on `es`
  >- simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >>
  rename1 `h::rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest`
  >- simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >>
  rename1 `Name at a :: h :: rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest`
  >- (Cases_on `bi` >> gvs[FUN_EQ_THM, compile_expr_body_def, expr_type_def]) >>
  rename1 `Name at a :: Name bt b :: h :: rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest` >> Cases_on `bi` >> gvs[FUN_EQ_THM, compile_expr_body_def, expr_type_def]
QED

Theorem compile_expr_body_shape:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  (!ce ret t bi es. bi <> Env MsgGas /\ builtin_arity bi <= LENGTH es /\
     ~supported_exprs_exists expr_shape_root es ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (bfn ce ret t bi es) (\v st. value_shape_ok st v)) /\
  (!ce vv t tb ret es. type_builtin_arity tb <= LENGTH es /\
     ~supported_exprs_exists expr_shape_root es ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (tfn ce vv t tb ret es) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root e ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_expr_body cfn bfn tfn cenv ty e) (\v st. value_shape_ok st v)
Proof
  strip_tac >> Cases_on `e`
  >~ [`compile_expr_body _ _ _ _ _ (Literal ann lit)`]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_conseq >> irule_at Any compile_literal_vv_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable])
  >~ [`compile_expr_body _ _ _ _ _ (Name ann id)`]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule compile_name_vv_shape)
  >~ [`compile_expr_body _ _ _ _ _ (IfExp ann c t e)`]
  >- (irule compile_ifexp_shape >>
      gvs[supported_expr_exists_def, expr_shape_root_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin ann bi es)`]
  >- suspend "builtin"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin ann tb ret es)`]
  >- (gvs[expr_shape_type_builtin] >>
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      first_x_assum irule >> simp[])
  >~ [`compile_expr_body _ _ _ _ _ (Subscript ann base_e idx_e)`]
  >- suspend "subscript"
  >~ [`compile_expr_body _ _ _ _ _ (Attribute ann base_e fld)`]
  >- suspend "attribute"
  >~ [`compile_expr_body _ _ _ _ _ (StructLit ann name fields)`]
  >- suspend "struct"
  >~ [`compile_expr_body _ _ _ _ _ (FlagMember ann ns mem)`]
  >- suspend "flag"
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName ann ns)`]
  >- suspend "top_name"
  >~ [`compile_expr_body _ _ _ _ _ (Call ann target args default_ret)`]
  >- suspend "call"
  >> suspend "pop"
QED

Resume compile_expr_body_shape[subscript]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule compile_subscript_shape >> gvs[supported_expr_exists_def, expr_shape_root_def]
QED

Resume compile_expr_body_shape[attribute]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule compile_attribute_shape >> gvs[supported_expr_exists_def, expr_shape_root_def]
QED

Resume compile_expr_body_shape[struct]:
  gvs[supported_expr_exists_def, expr_shape_root_def] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\buf st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand` >> reverse conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `buf` >> simp[] >> irule shape_step_uncurry >>
  qexists_tac `\v st. plain_operand st buf.buf_operand` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any compile_struct_lit_shape >>
      qexists_tac `\st. plain_operand st buf.buf_operand` >> simp[] >>
      mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def, base_ptr_def]
QED

Resume compile_expr_body_shape[flag]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def, shape_step_def, shape_extends_refl,
       value_shape_ok_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_expr_body_shape[top_name]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP cenv.ce_vars key` >>
  Cases_on `FLOOKUP cenv.ce_vars key` >> simp[]
  >- (irule shape_step_uncurry >> qexists_tac `\u st. T` >> reverse conj_tac
      >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. T` >>
          simp[shape_stable_def] >> shape_opcode_tac) >>
      gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def] >> shape_opcode_tac) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  TRY (irule shape_step_uncurry >> qexists_tac `\u st. T` >> reverse conj_tac
       >- (shape_under_tac shape_step_emit_inst_guarded_framed `\st. T` >>
           simp[shape_stable_def] >> shape_opcode_tac) >>
       gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def] >> shape_opcode_tac >> NO_TAC) >>
  simp[shape_step_def, shape_extends_refl, value_shape_ok_def, mk_ptr_def,
       plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  drule_all cenv_lookup_shape >> simp[loc_shape_ok_def]
QED

Resume compile_expr_body_shape[call]:
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[supported_expr_exists_def, expr_shape_root_def] >> Cases_on `target` >> gvs[]
  >~ [`compile_call _ _ _ _ (ExtCall _ _ sig opts)`]
  >- (PairCases_on `sig` >> irule compile_call_ext_shape >> simp[])
  >~ [`compile_call _ _ _ _ (IntCall name)`]
  >- (irule compile_call_int_shape >> simp[])
  >~ [`compile_call _ _ _ _ (Send has_gas)`]
  >- (irule compile_call_send_shape >> simp[])
  >~ [`compile_call _ _ _ _ RawLog _ _`]
  >- (irule compile_call_raw_log_shape >> simp[])
  >~ [`compile_call _ _ _ _ RawRevert _ _`]
  >- (irule compile_call_raw_revert_shape >> simp[])
  >~ [`compile_call _ _ _ _ (RawCallTarget _) _ _`]
  >- shape_send_invalid_tac
  >~ [`compile_call _ _ _ _ (CreateTarget _ _ _) _ _`]
  >- shape_send_invalid_tac
  (* INACTIVE EXPLORATION: SELFDESTRUCT is excluded by expr_shape_root,
     so gvs above closes this case. The attempted proof is preserved below;
     its emission cannot satisfy the current instruction shape policy.
  >~ [`compile_call _ _ _ _ SelfDestructTarget _ _`]
  >- (namedCases_on `args` ["", "to_e tail"]
      >- shape_send_invalid_tac >> Cases_on `tail`
      >| [ALL_TAC, shape_send_invalid_tac] >>
      gvs[supported_exprs_exists_every] >>
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_uncurry >> qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
      >- (shape_under_tac lower_value_callback_shape `\st. T` >> simp[shape_stable_def]) >>
      qx_gen_tac `to_op` >> simp[] >> irule shape_step_uncurry >>
      qexists_tac `\u st. T` >> conj_tac
      >- shape_raw_return_zero_tac >>
      simp[builtinSystemTheory.compile_selfdestruct_def] >>
      shape_under_tac shape_step_emit_void_plain `\st. T` >>
      simp[shape_stable_def] >> shape_opcode_tac)
  *) >>
  gvs[] >> shape_send_invalid_tac
QED

Resume compile_expr_body_shape[pop]:
  rename1 `Pop ann target` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  Cases_on `target` >> simp[] >> shape_pop_case_tac
QED

Resume compile_expr_body_shape[builtin]:
  Cases_on `?at a bt b mt m. bi = AddMod /\ es = [Name at a; Name bt b; Name mt m]`
  >- (gvs[] >> simp[compile_expr_body_addmod_names, cj 1 compile_mod_names_shape]) >>
  Cases_on `?at a bt b mt m. bi = MulMod /\ es = [Name at a; Name bt b; Name mt m]`
  >- (gvs[] >> simp[compile_expr_body_mulmod_names, cj 2 compile_mod_names_shape]) >>
  Cases_on `?at a bt b. bi = PowMod256 /\ es = [Name at a; Name bt b]`
  >- (gvs[] >> simp[compile_expr_body_powmod_names, cj 3 compile_mod_names_shape]) >>
  drule_all compile_expr_body_builtin_default >> disch_then (fn th => rewrite_tac[th]) >>
  first_x_assum irule >> gvs[expr_shape_builtin]
QED

Finalise compile_expr_body_shape[local]

Theorem compile_expr_shape_pointwise[local]:
  (!ce ty e st. !internal v st'.
    ~supported_expr_exists expr_shape_root e /\
    compile_expr ce ty e st = (v,st') /\ cenv_shape_ok st ce /\ shape_state st ==>
    shape_extends internal compiler_label st st' /\ shape_state st' /\ value_shape_ok st' v) /\
  (!ce rt ty bi args st. !internal v st'.
    bi <> Env MsgGas /\ builtin_arity bi <= LENGTH args /\
    ~supported_exprs_exists expr_shape_root args /\
    compile_builtin_dispatch ce rt ty bi args st = (v,st') /\ cenv_shape_ok st ce /\ shape_state st ==>
    shape_extends internal compiler_label st st' /\ shape_state st' /\ value_shape_ok st' v) /\
  (!ce vt ty tb rt args st. !internal v st'.
    type_builtin_arity tb <= LENGTH args /\ ~supported_exprs_exists expr_shape_root args /\
    compile_type_builtin_dispatch ce vt ty tb rt args st = (v,st') /\ cenv_shape_ok st ce /\ shape_state st ==>
    shape_extends internal compiler_label st st' /\ shape_state st' /\ value_shape_ok st' v)
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt gen_tac >> strip_tac >> mp_tac (Q.INST [
        `cfn` |-> `expr_child_callback (expr_size e) compile_expr`,
        `bfn` |-> `builtin_child_callback (expr_size e) compile_builtin_dispatch`,
        `tfn` |-> `type_child_callback (expr_size e) compile_type_builtin_dispatch`,
        `cenv` |-> `ce`] compile_expr_body_shape) >>
      impl_tac
      >- (rpt conj_tac
          >- (rpt strip_tac >> irule expr_child_callback_shape >> fs[shape_step_def] >> metis_tac[])
          >- (rpt strip_tac >> irule builtin_child_callback_shape >> fs[shape_step_def] >> metis_tac[])
          >- (rpt strip_tac >> irule type_child_callback_shape >> fs[shape_step_def] >> metis_tac[]) >>
          simp[]) >>
      simp[shape_step_def] >> disch_then irule >>
      qpat_x_assum `compile_expr ce ty e st = _` mp_tac >>
      simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      mp_tac (Q.INST [`cfn` |-> `expr_child_callback (list_size expr_size args) compile_expr`,
                     `cenv` |-> `ce`, `ret_ty` |-> `rt`] compile_builtin_dispatch_body_shape) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> irule expr_child_callback_shape >> fs[shape_step_def] >> metis_tac[]) >>
          simp[]) >>
      simp[shape_step_def] >> disch_then irule >>
      qpat_x_assum `compile_builtin_dispatch ce rt ty bi args st = _` mp_tac >>
      simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`cfn` |-> `expr_child_callback (list_size expr_size args) compile_expr`,
                 `cenv` |-> `ce`, `vv_ty` |-> `vt`, `ret_ty` |-> `rt`] compile_type_builtin_dispatch_body_shape) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> irule expr_child_callback_shape >> fs[shape_step_def] >> metis_tac[]) >>
      simp[]) >>
  simp[shape_step_def] >> disch_then irule >>
  qpat_x_assum `compile_type_builtin_dispatch ce vt ty tb rt args st = _` mp_tac >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* compile_expr_shape_pointwise in shape_step form.  Under value_shape_ok no
   value is in LocCode, so DLOAD/DLOADBYTES are unreachable; GAS is emitted
   only as the gas operand of the call right after it. *)
Theorem compile_expr_shape:
  (!cenv ty e internal.
     ~supported_expr_exists expr_shape_root e ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
       (compile_expr cenv ty e) (\v st. value_shape_ok st v)) /\
  (!cenv ret_ty ty bi args internal.
     bi <> Env MsgGas /\ builtin_arity bi <= LENGTH args /\
     ~supported_exprs_exists expr_shape_root args ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
       (compile_builtin_dispatch cenv ret_ty ty bi args)
       (\v st. value_shape_ok st v)) /\
  (!cenv vv_ty ty tb ret_ty args internal.
     type_builtin_arity tb <= LENGTH args /\
     ~supported_exprs_exists expr_shape_root args ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
       (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args)
       (\v st. value_shape_ok st v))
Proof
  mp_tac compile_expr_shape_pointwise >>
  simp[shape_step_def] >> metis_tac[]
QED

Theorem lower_value_shape[local]:
  !cenv ty e internal.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (lower_value compile_expr cenv ty e)
      (\op st. plain_operand st op)
Proof
  rpt strip_tac >> simp[lower_value_def] >> irule shape_step_bind >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ value_shape_ok st v` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule unwrap_value_shape) >>
  drule (cj 1 compile_expr_shape) >>
  disch_then (qspecl_then [`cenv`, `ty`, `internal`] assume_tac) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. cenv_shape_ok st cenv` mp_tac) >>
  simp[cenv_shape_ok_stable]
QED

Theorem lower_value_with_loc_shape[local]:
  !cenv ty e internal.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (lower_value_with_loc compile_expr cenv ty e)
      (\r st. plain_operand st (FST r))
Proof
  rpt strip_tac >> simp[lower_value_with_loc_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ value_shape_ok st v` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\op st. plain_operand st op` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      irule unwrap_value_shape) >>
  drule (cj 1 compile_expr_shape) >>
  disch_then (qspecl_then [`cenv`, `ty`, `internal`] assume_tac) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. cenv_shape_ok st cenv` mp_tac) >>
  simp[cenv_shape_ok_stable]
QED

Theorem compile_get_target_ptr_shape:
  !bt cenv internal.
    ~supported_target_exists expr_shape_root bt ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_get_target_ptr cenv bt)
      (\r st. plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode)
Proof
  Induct >> rpt gen_tac >> simp[supported_expr_exists_def, Once compile_get_target_ptr_def]
  >- suspend "name"
  >- suspend "toplevel"
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume compile_get_target_ptr_shape[name]:
  BasicProvers.TOP_CASE_TAC
  >- (irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  rename1 `FLOOKUP _ _ = SOME vloc` >> Cases_on `vloc` >> simp[] >>
  irule shape_step_return >> BETA_TAC >> rpt strip_tac >>
  drule_all cenv_shape_ok_lookup >>
  gvs[loc_shape_ok_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_get_target_ptr_shape[toplevel]:
  BasicProvers.TOP_CASE_TAC
  >- (irule shape_step_return >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  rename1 `FLOOKUP _ _ = SOME vloc` >> Cases_on `vloc` >> simp[] >>
  irule shape_step_return >> BETA_TAC >> rpt strip_tac >>
  drule_all cenv_shape_ok_lookup >>
  gvs[loc_shape_ok_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_get_target_ptr_shape[subscript]:
  strip_tac >> IF_CASES_TAC
  >- suspend "mapping" >>
  irule shape_step_bind >>
  qexists_tac `\r st. (plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode) /\
                     cenv_shape_ok st cenv` >>
  conj_tac
  >- (qx_gen_tac `r` >> BETA_TAC >> simp[stmt_return_bind] >>
      suspend "array") >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
  simp[cenv_shape_ok_stable] >> first_x_assum irule >> simp[]
QED
Resume compile_get_target_ptr_shape[attribute]:
  strip_tac >> irule shape_step_bind >>
  qexists_tac `\r st. plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode` >>
  conj_tac
  >- (qx_gen_tac `r` >> BETA_TAC >> simp[stmt_return_bind] >>
      qmatch_goalsub_abbrev_tac `emit_op ADD [FST r; Lit field_off]` >>
      irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st p /\ FST (SND r) <> SOME LocCode` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st (FST r)` >>
      simp[stmt_shape_stable_const] >> stmt_plain_emit) >>
  first_x_assum irule >> simp[]
QED
Resume compile_get_target_ptr_shape[mapping]:
  irule shape_step_bind >>
  qexists_tac `\key st. plain_operand st key /\ cenv_shape_ok st cenv` >>
  conj_tac
  >- (qx_gen_tac `key` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\base st. plain_operand st base /\ plain_operand st key` >>
      conj_tac
      >- (qx_gen_tac `mapping_base_op` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\slot st. plain_operand st slot` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          irule compile_mapping_subscript_shape) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. cenv_shape_ok st cenv` >>
      simp[stmt_shape_stable_plain] >> Cases_on `bt` >> simp[]
      >- (irule shape_step_return >> BETA_TAC >> rpt strip_tac >>
          BasicProvers.TOP_CASE_TAC >> simp[plain_operand_def,
            stackPlanTypesTheory.is_label_operand_def] >>
          rename1 `FLOOKUP _ _ = SOME vloc` >> Cases_on `vloc` >>
          simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
      (irule shape_step_bind >>
       qexists_tac `\r st. plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode` >>
       conj_tac
       >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
       first_x_assum irule >> simp[])) >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. cenv_shape_ok st cenv` >>
  simp[cenv_shape_ok_stable] >> irule lower_value_shape >> simp[]
QED
Resume compile_get_target_ptr_shape[array]:
  reverse (Cases_on `FST (SND r) <> SOME LocCode`)
  >- simp[shape_step_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_array_subscript _ _ dyn_flag arr_count arr_ws arr_elem_size idx_signed arr_load` >>
  irule shape_step_bind >>
  qexists_tac `\idx st. plain_operand st idx /\ plain_operand st (FST r)` >>
  conj_tac
  >- (qx_gen_tac `idx` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st p` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st (FST r) /\ plain_operand st idx`,
        `\p st. plain_operand st p`] >> simp[] >>
      Cases_on `FST (SND r)` >> gvs[Abbr `arr_load`]
      >- (irule (SRULE[load_opc_for_def]
            (Q.INST [`loc` |-> `LocMemory`] (SPEC_ALL compile_array_subscript_shape)))) >>
      rename1 `array_loc <> LocCode` >>
      Cases_on `array_loc` >> gvs[] >>
      FIRST [irule (SRULE[load_opc_for_def] (Q.INST [`loc` |-> `LocMemory`] (SPEC_ALL compile_array_subscript_shape))),
             irule (SRULE[load_opc_for_def] (Q.INST [`loc` |-> `LocStorage`] (SPEC_ALL compile_array_subscript_shape))),
             irule (SRULE[load_opc_for_def] (Q.INST [`loc` |-> `LocTransient`] (SPEC_ALL compile_array_subscript_shape)))]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
  simp[stmt_shape_stable_plain] >> irule lower_value_shape >> simp[]
QED
Finalise compile_get_target_ptr_shape[local]

Theorem compile_store_at_loc_shape[local]:
  !internal dst val_op loc_opt.
    loc_opt <> SOME LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st val_op)
      (compile_store_at_loc dst val_op loc_opt) (\u st. T)
Proof
  rpt strip_tac >> Cases_on `loc_opt` >> simp[compile_store_at_loc_def]
  >- stmt_plain_void_drop >>
  rename1 `SOME store_loc <> SOME LocCode` >>
  Cases_on `store_loc` >> gvs[compile_store_at_loc_def] >> stmt_plain_void_drop
QED

Theorem compile_load_memory_shape[local]:
  !internal ptr_op is_prim.
    shape_step internal compiler_label (\st. plain_operand st ptr_op)
      (compile_load_memory ptr_op is_prim) (\op st. plain_operand st op)
Proof
  rpt gen_tac >> simp[compile_load_memory_def] >> IF_CASES_TAC
  >- stmt_plain_emit >> irule shape_step_return >> simp[]
QED

Theorem compile_tuple_load_all_shape[local]:
  !tys cenv src_op off internal.
    shape_step internal compiler_label (\st. plain_operand st src_op)
      (compile_tuple_load_all cenv src_op tys off)
      (\ops st. EVERY (plain_operand st) ops)
Proof
  Induct >- (simp[compile_tuple_load_all_def] >> rpt gen_tac >>
             irule shape_step_return >> simp[]) >>
  rpt gen_tac >> simp[compile_tuple_load_all_def] >> irule shape_step_bind >>
  qexists_tac `\p st. plain_operand st p /\ plain_operand st src_op` >>
  conj_tac
  >- (qx_gen_tac `src_elem` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\op st. plain_operand st op /\ plain_operand st src_op` >>
      conj_tac
      >- (qx_gen_tac `elem_op` >> BETA_TAC >> irule shape_step_bind >>
          qexists_tac `\ops st. EVERY (plain_operand st) ops /\ plain_operand st elem_op` >>
          conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          ho_match_mp_tac stmt_shape_frame >>
          qexists_tac `\st. plain_operand st src_op` >>
          simp[stmt_shape_stable_plain] >> first_x_assum irule) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st src_elem` >>
      simp[stmt_shape_stable_plain] >> irule compile_load_memory_shape) >>
  stmt_frame_emit `\st. plain_operand st src_op`
QED

Theorem stmt_stable_fst_operands[local]:
  !xs. shape_stable (\st. EVERY (\p. plain_operand st (FST p)) xs)
Proof
  gen_tac >> mp_tac (Q.SPEC `MAP FST xs` shape_stable_plain_operands) >>
  simp[EVERY_MAP, combinTheory.o_DEF]
QED

Theorem compile_log_eval_all_shape[local]:
  !es cenv internal.
    ~supported_exprs_exists expr_shape_root es ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_log_eval_all cenv es)
      (\ops st. EVERY (\p. plain_operand st (FST p)) ops)
Proof
  Induct >> simp[supported_expr_exists_def, compile_log_eval_all_def]
  >- (rpt gen_tac >> irule shape_step_return >> simp[]) >>
  rpt strip_tac >> irule shape_step_bind >>
  qexists_tac `\op st. plain_operand st op /\ cenv_shape_ok st cenv` >>
  conj_tac
  >- (qx_gen_tac `arg_op` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\ops st. EVERY (\p. plain_operand st (FST p)) ops /\
                           plain_operand st arg_op` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
      simp[stmt_shape_stable_plain] >> first_x_assum irule >> simp[]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
  simp[cenv_shape_ok_stable] >> irule lower_value_shape >> simp[]
QED

Theorem split_log_ops_plain[local]:
  !ops flags st.
    EVERY (\p. plain_operand st (FST p)) ops ==>
    EVERY (\p. plain_operand st (FST p)) (FST (split_log_ops ops flags)) /\
    EVERY (\p. plain_operand st (FST p)) (SND (split_log_ops ops flags))
Proof
  Induct >- (Cases >> simp[split_log_ops_def]) >>
  qx_gen_tac `arg_pair` >> rpt gen_tac >> PairCases_on `arg_pair` >>
  Cases_on `flags` >- simp[split_log_ops_def] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def] >> rpt strip_tac >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `flags` mp_tac) >> simp[]
QED

Theorem compile_log_topic_ops_shape[local]:
  !ops internal.
    shape_step internal compiler_label
      (\st. EVERY (\p. plain_operand st (FST p)) ops)
      (compile_log_topic_ops ops) (\xs st. EVERY (plain_operand st) xs)
Proof
  Induct >- (simp[compile_log_topic_ops_def] >> gen_tac >>
             irule shape_step_return >> simp[]) >>
  rpt gen_tac >> simp[compile_log_topic_ops_def] >> irule shape_step_bind >>
  qexists_tac `\op st. plain_operand st op /\
                      EVERY (\p. plain_operand st (FST p)) ops` >>
  conj_tac
  >- (qx_gen_tac `topic_op` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\xs st. EVERY (plain_operand st) xs /\ plain_operand st topic_op` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. EVERY (\p. plain_operand st (FST p)) ops` >>
      simp[stmt_shape_stable_plain] >> first_x_assum irule) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st (FST h)` >>
  simp[stmt_stable_fst_operands] >> irule compile_encode_log_topic_shape
QED

Theorem compile_log_store_data_shape[local]:
  !ops cenv buf_op offset internal.
    shape_step internal compiler_label
      (\st. EVERY (\p. plain_operand st (FST p)) ops /\ plain_operand st buf_op)
      (compile_log_store_data cenv ops buf_op offset) (\u st. T)
Proof
  Induct
  >- (rpt gen_tac >> simp[compile_log_store_data_def] >>
      irule shape_step_return >> simp[]) >>
  rpt gen_tac >> simp[compile_log_store_data_def] >> irule shape_step_bind >>
  qexists_tac `\dst st. plain_operand st dst /\
    (plain_operand st (FST h) /\
     (EVERY (\p. plain_operand st (FST p)) ops /\ plain_operand st buf_op))` >>
  conj_tac
  >- (qx_gen_tac `dst_op` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\u st. T /\
        (EVERY (\p. plain_operand st (FST p)) ops /\ plain_operand st buf_op)` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (\p. plain_operand st (FST p)) ops /\ plain_operand st buf_op`,
            `\u st. T`] >> simp[] >> first_x_assum irule) >>
      ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st dst_op /\ plain_operand st (FST h)` >>
      simp[stmt_stable_fst_operands, stmt_shape_stable_plain, shape_stable_conj] >>
      IF_CASES_TAC >- stmt_plain_void_drop >>
      IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. plain_operand st (FST h) /\ plain_operand st dst_op`, `\u st. T`] >>
          simp[compile_store_bytestring_shape]) >>
      stmt_plain_void_drop) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st buf_op` >>
  simp[stmt_stable_fst_operands, stmt_shape_stable_plain, shape_stable_conj] >>
  stmt_plain_emit
QED

Theorem compile_reason_message_shape[local]:
  !cenv reason_e internal.
    ~supported_expr_exists expr_shape_root reason_e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_reason_message cenv reason_e) (\vv st. value_shape_ok st vv)
Proof
  recInduct compile_reason_message_ind >> rpt strip_tac >>
  simp[Once compile_reason_message_def]
  >- (irule shape_step_bind >>
      qexists_tac `\buf st. plain_operand st buf.buf_operand` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >>
          simp[value_shape_ok_def, loc_shape_ok_def, base_ptr_def]) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. T`,
                   `\buf st. plain_operand st buf.buf_operand`] >>
      simp[compile_bytelike_literal_shape]) >>
  irule (cj 1 compile_expr_shape) >> simp[]
QED

val stmt_revert_void_drop = stmt_drop
  (ho_match_mp_tac stmt_shape_emit_void >>
   conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >> irule stmt_shape_stable_plain) >>
   simp[label_or_plain_def] >> stmt_shape_emit_simp >>
   simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]);

fun stmt_revert_emit input =
  ho_match_mp_tac stmt_shape_frame >> qexists_tac input >>
  conj_tac >- stmt_plain_emit >>
  conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >> irule stmt_shape_stable_plain) >>
  simp[];

fun stmt_bind post name first_step =
  irule shape_step_bind >> qexists_tac post >>
  reverse conj_tac >- first_step >> qx_gen_tac name >> BETA_TAC;

Theorem compile_revert_with_reason_shape:
  !internal cenv msg_vv msg_type msg_mem_size.
    shape_step internal compiler_label
      (\st. cenv_shape_ok st cenv /\ value_shape_ok st msg_vv)
      (compile_revert_with_reason cenv msg_vv msg_type msg_mem_size) (\u st. T)
Proof
  rpt gen_tac >> simp[compile_revert_with_reason_def] >>
  stmt_bind `\buf st. plain_operand st buf.buf_operand /\
    (cenv_shape_ok st cenv /\ value_shape_ok st msg_vv)` `buf`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[cenv_shape_ok_stable, value_shape_ok_stable, shape_stable_conj] >>
     irule compile_alloc_buffer_shape) >>
  stmt_sequence `\u st. plain_operand st buf.buf_operand /\
    (cenv_shape_ok st cenv /\ value_shape_ok st msg_vv)`
    (ho_match_mp_tac stmt_shape_emit_void >>
     simp[cenv_shape_ok_stable, value_shape_ok_stable, stmt_shape_stable_plain,
          shape_stable_conj, label_or_plain_def] >> stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_bind `\payload st. plain_operand st payload /\
    (plain_operand st buf.buf_operand /\
     (cenv_shape_ok st cenv /\ value_shape_ok st msg_vv))` `payload`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st buf.buf_operand` >>
     simp[cenv_shape_ok_stable, value_shape_ok_stable, shape_stable_conj,
          stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_bind `\tuple st. plain_operand st tuple.buf_operand /\
    (plain_operand st payload /\ (plain_operand st buf.buf_operand /\
      (cenv_shape_ok st cenv /\ value_shape_ok st msg_vv)))` `tuple`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[cenv_shape_ok_stable, value_shape_ok_stable, stmt_shape_stable_plain,
          shape_stable_conj] >> irule compile_alloc_buffer_shape) >>
  stmt_bind `\msg_op st. plain_operand st msg_op /\
    (plain_operand st tuple.buf_operand /\
     (plain_operand st payload /\ plain_operand st buf.buf_operand))` `msg_op`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. cenv_shape_ok st cenv /\ value_shape_ok st msg_vv` >>
     simp[stmt_shape_stable_plain, shape_stable_conj] >> irule unwrap_value_shape) >>
  suspend "copy_message"
QED

Resume compile_revert_with_reason_shape[copy_message]:
  stmt_bind `\n st. plain_operand st n /\ (plain_operand st msg_op /\
    plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `n`
    (stmt_frame_emit `\st. plain_operand st msg_op`) >>
  stmt_bind `\r st. plain_operand st r /\ (plain_operand st msg_op /\
    plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `r`
    (stmt_frame_emit `\st. plain_operand st n`) >>
  stmt_bind `\r1 st. plain_operand st r1 /\ (plain_operand st msg_op /\
    plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `r1`
    (stmt_frame_emit `\st. plain_operand st r`) >>
  stmt_bind `\sz st. plain_operand st sz /\ (plain_operand st msg_op /\
    plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `sz`
    (stmt_frame_emit `\st. plain_operand st r1`) >>
  stmt_sequence `\u st. plain_operand st tuple.buf_operand /\
    plain_operand st payload /\ plain_operand st buf.buf_operand` stmt_plain_void_drop >>
  stmt_bind `\size_buf st. plain_operand st size_buf.buf_operand /\
    (plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `size_buf`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[stmt_shape_stable_plain, shape_stable_conj] >> irule compile_alloc_buffer_shape) >>
  stmt_sequence `\u st. plain_operand st size_buf.buf_operand /\
    (plain_operand st tuple.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` stmt_plain_void >>
  suspend "encode_message"
QED

Resume compile_revert_with_reason_shape[encode_message]:
  stmt_bind `\src st. plain_operand st src /\ (plain_operand st size_buf.buf_operand /\
    plain_operand st payload /\ plain_operand st buf.buf_operand)` `src`
    (stmt_frame_emit `\st. plain_operand st tuple.buf_operand`) >>
  stmt_bind `\head_op st. plain_operand st head_op /\ (plain_operand st src /\
    plain_operand st size_buf.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `head_op`
    (stmt_frame_emit `\st. plain_operand st payload`) >>
  stmt_bind `\off st. plain_operand st off /\ (plain_operand st head_op /\ plain_operand st src /\
    plain_operand st size_buf.buf_operand /\ plain_operand st payload /\ plain_operand st buf.buf_operand)` `off`
    (stmt_frame_emit `\st. plain_operand st size_buf.buf_operand`) >>
  stmt_bind `\tail_op st. plain_operand st tail_op /\ (plain_operand st off /\ plain_operand st head_op /\
    plain_operand st src /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `tail_op`
    (stmt_frame_emit `\st. plain_operand st payload /\ plain_operand st off`) >>
  irule shape_step_bind >>
  qexists_tac `\msg_len st. plain_operand st msg_len /\ (plain_operand st tail_op /\ plain_operand st off /\
    plain_operand st head_op /\ plain_operand st src /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` >>
  reverse conj_tac
  >- (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st src` >>
      simp[stmt_shape_stable_plain, shape_stable_conj] >>
      conj_tac >- stmt_plain_emit >>
      rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >> irule stmt_shape_stable_plain) >>
  qx_gen_tac `msg_len` >> BETA_TAC >>
  stmt_bind `\round0 st. plain_operand st round0 /\ (plain_operand st msg_len /\ plain_operand st tail_op /\
    plain_operand st off /\ plain_operand st head_op /\ plain_operand st src /\
    plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `round0`
    (stmt_revert_emit `\st. plain_operand st msg_len`) >>
  stmt_bind `\rounded st. plain_operand st rounded /\ (plain_operand st msg_len /\ plain_operand st tail_op /\
    plain_operand st off /\ plain_operand st head_op /\ plain_operand st src /\
    plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `rounded`
    (stmt_revert_emit `\st. plain_operand st round0`) >>
  stmt_bind `\tail_end st. plain_operand st tail_end /\ (plain_operand st msg_len /\ plain_operand st tail_op /\
    plain_operand st off /\ plain_operand st head_op /\ plain_operand st src /\
    plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `tail_end`
    (stmt_revert_emit `\st. plain_operand st tail_op /\ plain_operand st rounded`) >>
  stmt_sequence `\u st. plain_operand st msg_len /\ plain_operand st tail_op /\ plain_operand st off /\
    plain_operand st head_op /\ plain_operand st src /\ plain_operand st size_buf.buf_operand /\
    plain_operand st buf.buf_operand` stmt_revert_void_drop >>
  suspend "finish_encoding"
QED

Resume compile_revert_with_reason_shape[finish_encoding]:
  stmt_bind `\copy_len st. plain_operand st copy_len /\ (plain_operand st msg_len /\
    plain_operand st tail_op /\ plain_operand st off /\ plain_operand st head_op /\
    plain_operand st src /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `copy_len`
    (stmt_revert_emit `\st. plain_operand st msg_len`) >>
  stmt_sequence `\u st. plain_operand st msg_len /\ plain_operand st off /\
    plain_operand st head_op /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand`
    stmt_revert_void_drop >>
  stmt_bind `\r2 st. plain_operand st r2 /\ (plain_operand st off /\
    plain_operand st head_op /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `r2`
    (stmt_revert_emit `\st. plain_operand st msg_len`) >>
  stmt_bind `\r3 st. plain_operand st r3 /\ (plain_operand st off /\
    plain_operand st head_op /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `r3`
    (stmt_revert_emit `\st. plain_operand st r2`) >>
  stmt_bind `\item_len st. plain_operand st item_len /\ (plain_operand st off /\
    plain_operand st head_op /\ plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `item_len`
    (stmt_revert_emit `\st. plain_operand st r3`) >>
  stmt_sequence `\u st. plain_operand st item_len /\ plain_operand st off /\
    plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand` stmt_revert_void_drop >>
  stmt_bind `\new_size st. plain_operand st new_size /\
    (plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand)` `new_size`
    (stmt_revert_emit `\st. plain_operand st off /\ plain_operand st item_len`) >>
  stmt_sequence `\u st. plain_operand st size_buf.buf_operand /\ plain_operand st buf.buf_operand`
    stmt_revert_void_drop >>
  stmt_bind `\encoded_len st. plain_operand st encoded_len /\ plain_operand st buf.buf_operand` `encoded_len`
    (stmt_revert_emit `\st. plain_operand st size_buf.buf_operand`) >>
  stmt_bind `\revert_offset st. plain_operand st revert_offset /\ plain_operand st encoded_len` `revert_offset`
    (stmt_revert_emit `\st. plain_operand st buf.buf_operand`) >>
  stmt_bind `\revert_len st. plain_operand st revert_len /\ plain_operand st revert_offset` `revert_len`
    (stmt_revert_emit `\st. plain_operand st encoded_len`) >>
  stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
    simp[stmt_shape_stable_plain, shape_stable_conj, label_or_plain_def] >>
    stmt_shape_emit_simp >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
    rpt strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def])
QED
Finalise compile_revert_with_reason_shape[local]

Theorem compile_raise_shape[local]:
  !reason cenv lctx ty internal.
    ~supported_stmt_expr_exists expr_shape_root (Raise reason) ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Raise reason)) (\u st. T)
Proof
  Cases >> rpt strip_tac >> simp[Once compile_stmt_def]
  >- (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
      simp[cenv_shape_ok_stable] >> stmt_shape_emit_simp >>
      simp[label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]))
  >- (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
      simp[cenv_shape_ok_stable] >> stmt_shape_emit_simp >>
      simp[label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def])) >>
  irule shape_step_bind >>
  qexists_tac `\msg st. value_shape_ok st msg /\ cenv_shape_ok st cenv` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ value_shape_ok st x`,
                   `\u st. T`] >> simp[compile_revert_with_reason_shape]) >>
  ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
  simp[cenv_shape_ok_stable] >> irule compile_reason_message_shape >>
  gvs[supported_stmt_expr_exists_def, supported_raise_exists_def]
QED

Theorem stmt_assert_blocks_shape[local]:
  !internal cenv cond_op (failure : unit compiler).
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv) failure (\u st. T) ==>
    shape_step internal compiler_label
      (\st. plain_operand st cond_op /\ cenv_shape_ok st cenv)
      (do ok_lbl <- fresh_label "assert_ok";
          fail_lbl <- fresh_label "assert_fail";
          emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [];
          new_block fail_lbl; failure; new_block ok_lbl; return () od) (\u st. T)
Proof
  rpt strip_tac >>
  stmt_bind `\l st. (plain_operand st cond_op /\ cenv_shape_ok st cenv) /\ compiler_label l` `ok_lbl`
    (ho_match_mp_tac shape_step_fresh_label >> simp[stmt_shape_stable_plain, cenv_shape_ok_stable, shape_stable_conj]) >>
  reverse (Cases_on `compiler_label ok_lbl`) >- simp[shape_step_def] >> simp[] >>
  stmt_bind `\l st. (plain_operand st cond_op /\ cenv_shape_ok st cenv) /\ compiler_label l` `fail_lbl`
    (ho_match_mp_tac shape_step_fresh_label >> simp[stmt_shape_stable_plain, cenv_shape_ok_stable, shape_stable_conj]) >>
  reverse (Cases_on `compiler_label fail_lbl`) >- simp[shape_step_def] >> simp[] >>
  stmt_sequence `\u st. cenv_shape_ok st cenv`
    (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
     simp[stmt_shape_stable_plain, cenv_shape_ok_stable, shape_stable_conj])) >>
  stmt_sequence `\u st. cenv_shape_ok st cenv`
    (ho_match_mp_tac stmt_shape_new_block >> simp[cenv_shape_ok_stable]) >>
  stmt_sequence `\u st. T` (first_x_assum ACCEPT_TAC) >>
  stmt_sequence `\u st. T`
    (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_const]) >>
  irule shape_step_return >> simp[]
QED

Theorem compile_assert_shape[local]:
  !reason cond_e cenv lctx ty internal.
    ~supported_stmt_expr_exists expr_shape_root (Assert cond_e reason) ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Assert cond_e reason)) (\u st. T)
Proof
  Cases >> rpt strip_tac >> simp[Once compile_stmt_def, stmt_return_bind] >>
  stmt_bind `\cond_op st. plain_operand st cond_op /\ cenv_shape_ok st cenv` `cond_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule lower_value_shape >>
     gvs[supported_stmt_expr_exists_def]) >>
  pure_rewrite_tac[comp_ignore_bind_def]
  >- (match_mp_tac (Q.INST [`failure` |-> `emit_inst REVERT [Lit (0w : bytes32); Lit (0w : bytes32)] []`]
        (SPEC_ALL (PURE_REWRITE_RULE [comp_ignore_bind_def] stmt_assert_blocks_shape))) >>
      stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
      simp[cenv_shape_ok_stable] >> stmt_shape_emit_simp >>
      simp[label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]))
  >- (match_mp_tac (Q.INST [`failure` |-> `emit_inst INVALID [] []`]
        (SPEC_ALL (PURE_REWRITE_RULE [comp_ignore_bind_def] stmt_assert_blocks_shape))) >>
      stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
      simp[cenv_shape_ok_stable] >> stmt_shape_emit_simp)) >>
  match_mp_tac (BETA_RULE (PURE_REWRITE_RULE [comp_bind_assoc]
    (Q.INST [`failure` |->
       `comp_bind (compile_reason_message cenv e)
          (\msg. compile_revert_with_reason cenv msg (expr_type e)
                   (type_memory_bytes cenv (expr_type e)))`]
      (SPEC_ALL (PURE_REWRITE_RULE [comp_ignore_bind_def] stmt_assert_blocks_shape))))) >>
  stmt_bind `\msg st. value_shape_ok st msg /\ cenv_shape_ok st cenv` `msg`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule compile_reason_message_shape >>
     gvs[supported_stmt_expr_exists_def, supported_assert_exists_def]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ value_shape_ok st msg`,
               `\u st. T`] >> simp[compile_revert_with_reason_shape]
QED

Theorem compile_log_shape:
  !event_id args cenv lctx ty internal.
    ~supported_exprs_exists expr_shape_root args ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Log event_id args)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  Cases_on `cenv.ce_event_info (nsid_to_string event_id)`
  >- (simp[] >> stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
       simp[cenv_shape_ok_stable] >> stmt_shape_emit_simp)) >>
  rename1 `SOME event_info` >> PairCases_on `event_info` >>
  simp[stmt_return_bind] >>
  stmt_bind `\ops st. EVERY (\p. plain_operand st (FST p)) ops` `ops`
    (irule compile_log_eval_all_shape >> simp[]) >>
  qmatch_goalsub_abbrev_tac `compile_log_topic_ops topics` >>
  qmatch_goalsub_abbrev_tac `NULL data_ops` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (\p. plain_operand st (FST p)) topics /\
          EVERY (\p. plain_operand st (FST p)) data_ops`, `\u st. T`] >>
  simp [] >>
  conj_tac >- (simp[Abbr `topics`, Abbr `data_ops`] >>
                metis_tac[split_log_ops_plain]) >>
  stmt_bind `\topic_ops st. EVERY (plain_operand st) topic_ops /\
      EVERY (\p. plain_operand st (FST p)) data_ops` `topic_ops`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. EVERY (\p. plain_operand st (FST p)) topics` >>
     simp[stmt_stable_fst_operands, compile_log_topic_ops_shape]) >>
  IF_CASES_TAC
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st)
          (Lit (n2w (SUC (LENGTH topic_ops))) ::
             (REVERSE topic_ops ++ [Lit (n2w event_info0)] ++ [Lit 0w; Lit 0w]))`,
         `\u st. T`] >>
      simp[stmt_log_emit_shape, EVERY_REVERSE, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  suspend "data"
QED

Resume compile_log_shape[data]:
  stmt_bind `\buf st. plain_operand st buf.buf_operand /\
    (EVERY (plain_operand st) topic_ops /\
     EVERY (\p. plain_operand st (FST p)) data_ops)` `buf`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[shape_stable_conj, shape_stable_plain_operands, stmt_stable_fst_operands,
          compile_alloc_buffer_shape]) >>
  stmt_sequence `\u st. T /\ (EVERY (plain_operand st) topic_ops /\
                                 plain_operand st buf.buf_operand)`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. EVERY (\p. plain_operand st (FST p)) data_ops /\
                       plain_operand st buf.buf_operand` >>
     simp[shape_stable_conj, shape_stable_plain_operands, stmt_shape_stable_plain,
          compile_log_store_data_shape]) >>
  stmt_bind `\abi st. plain_operand st abi.buf_operand /\
    (EVERY (plain_operand st) topic_ops /\ plain_operand st buf.buf_operand)` `abi`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[shape_stable_conj, shape_stable_plain_operands, stmt_shape_stable_plain,
          compile_alloc_buffer_shape]) >>
  stmt_bind `\len st. plain_operand st len /\
    (EVERY (plain_operand st) topic_ops /\ plain_operand st abi.buf_operand)` `len`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st abi.buf_operand /\ plain_operand st buf.buf_operand` >>
     simp[shape_stable_conj, shape_stable_plain_operands, stmt_shape_stable_plain,
          cj 2 compile_abi_encode_shape]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st)
      (Lit (n2w (SUC (LENGTH topic_ops))) ::
       (REVERSE topic_ops ++ [Lit (n2w event_info0)] ++ [len; abi.buf_operand]))`,
    `\u st. T`] >>
  simp[stmt_log_emit_shape, EVERY_REVERSE, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Finalise compile_log_shape[local]

Theorem compile_dynarray_to_storage_shape:
  !internal src dst ew ems transient.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_dynarray_to_storage src dst ew ems transient) (\u st. T)
Proof
  rpt gen_tac >> simp[Once compile_dynarray_to_storage_def] >>
  stmt_bind `\len st. plain_operand st len /\
    (plain_operand st src /\ plain_operand st dst)` `len`
    (stmt_frame_emit `\st. plain_operand st src /\ plain_operand st dst`) >>
  stmt_bind `\l st. (plain_operand st len /\
    (plain_operand st src /\ plain_operand st dst)) /\ compiler_label l` `cond_lbl`
    (ho_match_mp_tac shape_step_fresh_label >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  reverse (Cases_on `compiler_label cond_lbl`) >- simp[shape_step_def] >> simp[] >>
  stmt_bind `\l st. (plain_operand st len /\
    (plain_operand st src /\ plain_operand st dst)) /\ compiler_label l` `body_lbl`
    (ho_match_mp_tac shape_step_fresh_label >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  reverse (Cases_on `compiler_label body_lbl`) >- simp[shape_step_def] >> simp[] >>
  stmt_bind `\l st. (plain_operand st len /\
    (plain_operand st src /\ plain_operand st dst)) /\ compiler_label l` `exit_lbl`
    (ho_match_mp_tac shape_step_fresh_label >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  reverse (Cases_on `compiler_label exit_lbl`) >- simp[shape_step_def] >> simp[] >>
  stmt_bind `\ctr st. (plain_operand st len /\
    (plain_operand st src /\ plain_operand st dst)) /\ plain_operand st (Var ctr)` `ctr`
    (ho_match_mp_tac shape_step_fresh_var >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  suspend "loop"
QED

Resume compile_dynarray_to_storage_shape[loop]:
  qabbrev_tac `live = \st. (plain_operand st len /\ plain_operand st src /\
                           plain_operand st dst) /\ plain_operand st (Var ctr)` >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_jmp >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_new_block >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_bind `\lt st. plain_operand st lt /\ live st` `lt`
    (simp[Abbr `live`] >> stmt_frame_emit
      `\st. (plain_operand st len /\ plain_operand st src /\ plain_operand st dst) /\
             plain_operand st (Var ctr)`) >>
  stmt_bind `\done_op st. plain_operand st done_op /\ live st` `done_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st lt` >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. live st`
    (stmt_drop (ho_match_mp_tac stmt_shape_jnz >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain])) >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_new_block >>
     simp[Abbr `live`, shape_stable_conj, stmt_shape_stable_plain]) >>
  simp[Abbr `live`] >> IF_CASES_TAC
  >- suspend "single"
  >> suspend "multi"
QED

Resume compile_dynarray_to_storage_shape[single]:
  stmt_bind `\mul st. plain_operand st mul /\ ((plain_operand st len /\
    plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr))` `product_op`
    (stmt_frame_emit `\st. (plain_operand st len /\ plain_operand st src /\
      plain_operand st dst) /\ plain_operand st (Var ctr)`) >>
  stmt_bind `\off st. plain_operand st off /\ ((plain_operand st len /\
    plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr))` `off`
    (stmt_frame_emit `\st. plain_operand st product_op`) >>
  stmt_bind `\source_ptr st. plain_operand st source_ptr /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))` `source_ptr`
    (stmt_frame_emit `\st. plain_operand st src /\ plain_operand st off`) >>
  stmt_bind `\val_op st. plain_operand st val_op /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))` `val_op`
    (stmt_frame_emit `\st. plain_operand st source_ptr`) >>
  stmt_bind `\off st. plain_operand st off /\
    (plain_operand st val_op /\ plain_operand st len /\ plain_operand st dst /\
     plain_operand st (Var ctr))` `slot_off`
    (stmt_frame_emit `\st. plain_operand st val_op /\ plain_operand st len /\
      plain_operand st dst /\ plain_operand st (Var ctr)`) >>
  stmt_bind `\ptr st. plain_operand st ptr /\
    (plain_operand st val_op /\ plain_operand st len /\ plain_operand st dst /\
     plain_operand st (Var ctr))` `dst_elem`
    (stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st slot_off`) >>
  stmt_sequence `\u st. T /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st dst_elem /\ plain_operand st val_op` >>
     simp[shape_stable_conj, stmt_shape_stable_plain] >>
     IF_CASES_TAC >> stmt_plain_void_drop) >>
  simp[] >> suspend "tail_single"
QED

Resume compile_dynarray_to_storage_shape[multi]:
  stmt_bind `\mul st. plain_operand st mul /\ ((plain_operand st len /\
    plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr))` `product_op`
    (stmt_frame_emit `\st. (plain_operand st len /\ plain_operand st src /\
      plain_operand st dst) /\ plain_operand st (Var ctr)`) >>
  stmt_bind `\off st. plain_operand st off /\ ((plain_operand st len /\
    plain_operand st src /\ plain_operand st dst) /\ plain_operand st (Var ctr))` `off`
    (stmt_frame_emit `\st. plain_operand st product_op`) >>
  stmt_bind `\source_ptr st. plain_operand st source_ptr /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))` `source_ptr`
    (stmt_frame_emit `\st. plain_operand st src /\ plain_operand st off`) >>
  stmt_bind `\mul st. plain_operand st mul /\
    (plain_operand st source_ptr /\ plain_operand st len /\ plain_operand st dst /\
     plain_operand st (Var ctr))` `slot_mul`
    (stmt_frame_emit `\st. plain_operand st (Var ctr)`) >>
  stmt_bind `\off st. plain_operand st off /\
    (plain_operand st source_ptr /\ plain_operand st len /\ plain_operand st dst /\
     plain_operand st (Var ctr))` `slot_off`
    (stmt_frame_emit `\st. plain_operand st slot_mul`) >>
  stmt_bind `\d st. plain_operand st d /\
    (plain_operand st source_ptr /\ plain_operand st len /\ plain_operand st dst /\
     plain_operand st (Var ctr))` `dst_elem`
    (stmt_frame_emit `\st. plain_operand st dst /\ plain_operand st slot_off`) >>
  stmt_sequence `\u st. T /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st source_ptr /\ plain_operand st dst_elem` >>
     simp[shape_stable_conj, stmt_shape_stable_plain, compile_word_copy_loop_noncode_shape]) >>
  simp[] >> suspend "tail"
QED

val stmt_dyn_storage_tail =
  stmt_bind `\next st. plain_operand st next /\
    (plain_operand st len /\ plain_operand st dst /\ plain_operand st (Var ctr))` `next`
    (stmt_frame_emit `\st. plain_operand st len /\ plain_operand st dst /\
      plain_operand st (Var ctr)`) >>
  stmt_sequence `\u st. plain_operand st len /\ plain_operand st dst`
    (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[shape_stable_conj, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def])) >>
  stmt_sequence `\u st. plain_operand st len /\ plain_operand st dst`
    (ho_match_mp_tac stmt_shape_jmp >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st len /\ plain_operand st dst`
    (ho_match_mp_tac stmt_shape_new_block >>
     simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  IF_CASES_TAC >> stmt_plain_void_drop;

Resume compile_dynarray_to_storage_shape[tail_single]:
  stmt_dyn_storage_tail
QED

Resume compile_dynarray_to_storage_shape[tail]:
  stmt_dyn_storage_tail
QED

Finalise compile_dynarray_to_storage_shape[local]

Theorem compile_assign_value_shape:
  !internal cenv dst dst_loc src prim src_loc dst_ty src_ty da_info mem_size.
    dst_loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st dst /\ plain_operand st src)
      (compile_assign_value cenv dst dst_loc src prim src_loc dst_ty src_ty da_info mem_size)
      (\u st. T)
Proof
  rpt strip_tac >> Cases_on `dst_loc` >> gvs[] >> simp[Once compile_assign_value_def]
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >> (stmt_sequence `\u st. plain_operand st dst /\ plain_operand st src`
        (ho_match_mp_tac stmt_shape_emit_inst >>
         simp[shape_stable_conj, stmt_shape_stable_plain] >> stmt_shape_emit_simp) >>
      irule shape_step_return >> simp[])
QED

Resume compile_assign_value_shape[memory]:
  IF_CASES_TAC >- stmt_plain_void_drop >>
  IF_CASES_TAC
  >- (simp[stmt_return_bind] >>
      stmt_bind `\buf st. plain_operand st buf.buf_operand /\
        (plain_operand st dst /\ plain_operand st src)` `buf`
        (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
         simp[shape_stable_conj, stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
      stmt_sequence `\u st. T /\
        (plain_operand st buf.buf_operand /\ plain_operand st dst)`
        (ho_match_mp_tac stmt_shape_frame >>
         qexists_tac `\st. plain_operand st buf.buf_operand /\ plain_operand st src` >>
         simp[shape_stable_conj, stmt_shape_stable_plain, compile_copy_memory_shape]) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st dst /\ plain_operand st buf.buf_operand`, `\u st. T`] >>
      simp[compile_store_memory_shape]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. plain_operand st dst /\ plain_operand st src`,
               `\u st. T`] >> simp[compile_store_memory_shape]
QED

val stmt_assign_storage =
  stmt_bind `\value_op st. plain_operand st value_op /\ plain_operand st dst` `value_op`
    (IF_CASES_TAC
     >- (stmt_bind `\buf st. plain_operand st buf.buf_operand /\
            (plain_operand st dst /\ plain_operand st src)` `buf`
           (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
            simp[shape_stable_conj, stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
         stmt_sequence `\u st. T /\
            (plain_operand st buf.buf_operand /\ plain_operand st dst)`
           (ho_match_mp_tac stmt_shape_frame >>
            qexists_tac `\st. plain_operand st buf.buf_operand /\ plain_operand st src` >>
            simp[shape_stable_conj, stmt_shape_stable_plain, cj 1 compile_typed_copy_shape]) >>
         irule shape_step_return >> simp[]) >>
     irule shape_step_return >> simp[]) >>
  IF_CASES_TAC >- stmt_plain_void_drop >>
  Cases_on `da_info`
  >- (simp[] >> IF_CASES_TAC
      >- (stmt_bind `\loaded st. plain_operand st loaded /\ plain_operand st dst` `loaded`
            (stmt_frame_emit `\st. plain_operand st value_op`) >>
          stmt_plain_void_drop) >>
      stmt_sequence `\u st. T`
        (irule shape_step_conseq >>
         qexistsl_tac [`compiler_label`,
           `\st. plain_operand st value_op /\ plain_operand st dst`, `\u st. T`] >>
         simp[compile_memory_to_storage_shape, compile_memory_to_transient_shape]) >>
      irule shape_step_return >> simp[]) >>
  rename1 `SOME pair_info` >> PairCases_on `pair_info` >> simp[] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st value_op /\ plain_operand st dst`, `\u st. T`] >>
  simp[compile_dynarray_to_storage_shape];

Resume compile_assign_value_shape[storage]:
  stmt_assign_storage
QED

Resume compile_assign_value_shape[transient]:
  stmt_assign_storage
QED

Finalise compile_assign_value_shape[local]

Theorem compile_tuple_store_all_shape:
  !tys targets vals cenv internal.
    EVERY (\t. case t of BaseTarget bt => ~supported_target_exists expr_shape_root bt
                       | _ => T) targets ==>
    shape_step internal compiler_label
      (\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) vals)
      (compile_tuple_store_all cenv tys targets vals) (\u st. T)
Proof
  Induct >- (rpt gen_tac >> strip_tac >> Cases_on `targets` >> Cases_on `vals` >>
             simp[compile_tuple_store_all_def] >> irule shape_step_return >> simp[]) >>
  rpt gen_tac >> Cases_on `targets`
  >- (simp[compile_tuple_store_all_def] >> irule shape_step_return >> simp[]) >>
  Cases_on `vals`
  >- (simp[compile_tuple_store_all_def] >> strip_tac >> irule shape_step_return >> simp[]) >>
  rename1 `compile_tuple_store_all cenv (src_ty::tys) (target::targets) (value_op::vals)` >>
  Cases_on `target` >> simp[compile_tuple_store_all_def, stmt_return_bind] >> strip_tac
  >- suspend "base"
  >> (stmt_sequence `\u st. cenv_shape_ok st cenv /\ plain_operand st value_op /\
                               EVERY (plain_operand st) vals`
        (ho_match_mp_tac stmt_shape_emit_void >>
         simp[cenv_shape_ok_stable, shape_stable_plain_operands, shape_stable_conj,
              stmt_shape_stable_plain] >> stmt_shape_emit_simp) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) vals`, `\u st. T`] >>
      simp[] >> first_x_assum irule >> simp[])
QED

Resume compile_tuple_store_all_shape[base]:
  stmt_bind `\r st. (plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode) /\
    (cenv_shape_ok st cenv /\ plain_operand st value_op /\ EVERY (plain_operand st) vals)` `r`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_plain_operands,
          shape_stable_conj] >> irule compile_get_target_ptr_shape >> simp[]) >>
  reverse (Cases_on `FST (SND r) <> SOME LocCode`) >- simp[shape_step_def] >> simp[] >>
  stmt_sequence `\u st. T /\ (cenv_shape_ok st cenv /\ EVERY (plain_operand st) vals)`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (FST r) /\ plain_operand st value_op` >>
     simp[cenv_shape_ok_stable, shape_stable_plain_operands, shape_stable_conj] >>
     IF_CASES_TAC
     >- (IF_CASES_TAC >- (irule compile_store_at_loc_shape >> simp[]) >>
         stmt_plain_void_drop) >>
     irule compile_assign_value_shape >> Cases_on `FST (SND r)` >> gvs[]) >>
  simp[] >> first_x_assum irule >> simp[]
QED

Finalise compile_tuple_store_all_shape[local]

Theorem compile_tuple_unpack_shape[local]:
  !cenv ty may_stage targets src internal.
    EVERY (\t. case t of BaseTarget bt => ~supported_target_exists expr_shape_root bt
                       | _ => T) targets ==>
    shape_step internal compiler_label
      (\st. cenv_shape_ok st cenv /\ plain_operand st src)
      (compile_tuple_unpack cenv ty may_stage targets src) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_tuple_unpack_def] >>
  qmatch_goalsub_abbrev_tac `compile_tuple_load_all cenv _ elem_types 0` >>
  IF_CASES_TAC
  >- (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
       simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
       stmt_shape_emit_simp)) >>
  stmt_bind `\staged st. plain_operand st staged /\ cenv_shape_ok st cenv` `staged`
    (IF_CASES_TAC
     >- (simp[stmt_return_bind] >>
         stmt_bind `\buf st. plain_operand st buf.buf_operand /\
           (cenv_shape_ok st cenv /\ plain_operand st src)` `buf`
           (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
            simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj,
                 compile_alloc_buffer_shape]) >>
         stmt_sequence `\u st. plain_operand st buf.buf_operand /\
           (cenv_shape_ok st cenv /\ plain_operand st src)`
           (ho_match_mp_tac stmt_shape_emit_void >>
            simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj,
                 label_or_plain_def] >> stmt_shape_emit_simp >>
            simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
         irule shape_step_return >> simp[]) >>
     irule shape_step_return >> simp[]) >>
  stmt_bind `\vals st. EVERY (plain_operand st) vals /\ cenv_shape_ok st cenv` `vals`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st staged` >>
     simp[cenv_shape_ok_stable, compile_tuple_load_all_shape]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) vals`, `\u st. T`] >>
  simp[] >> irule compile_tuple_store_all_shape >> simp[]
QED

Theorem compile_assign_base_shape[local]:
  !bt e cenv lctx ty internal.
    ~supported_target_exists expr_shape_root bt /\
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Assign (BaseTarget bt) e)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def, stmt_return_bind] >> IF_CASES_TAC
  >- (stmt_bind `\r st. plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode` `r`
        (irule compile_get_target_ptr_shape >> simp[]) >>
      reverse (Cases_on `FST (SND r) <> SOME LocCode`) >- simp[shape_step_def] >> simp[] >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. plain_operand st (FST r) /\ plain_operand st (Lit 0w)`, `\u st. T`] >>
      simp[compile_store_at_loc_shape, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_bind `\r st. (plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode) /\
    cenv_shape_ok st cenv` `r`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule compile_get_target_ptr_shape >> simp[]) >>
  simp[stmt_return_bind] >>
  reverse (Cases_on `FST (SND r) <> SOME LocCode`) >- simp[shape_step_def] >> simp[] >>
  stmt_bind `\v st. plain_operand st (FST v) /\ plain_operand st (FST r)` `v`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[stmt_shape_stable_plain] >> irule lower_value_with_loc_shape >> simp[]) >>
  simp[stmt_return_bind] >> Cases_on `FST (SND r)`
  >- (simp[] >> stmt_plain_void_drop) >>
  simp[] >> irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st (FST r) /\ plain_operand st (FST v)`, `\u st. T`] >>
  simp[] >> irule compile_assign_value_shape >> gvs[]
QED

Theorem compile_assign_tuple_shape[local]:
  !targets e cenv lctx ty internal.
    EVERY (\t. case t of BaseTarget bt => ~supported_target_exists expr_shape_root bt
                       | _ => T) targets /\
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Assign (TupleTarget targets) e)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\v st. value_shape_ok st v /\ cenv_shape_ok st cenv` `v`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule (cj 1 compile_expr_shape) >> simp[]) >>
  stmt_bind `\op st. plain_operand st op /\ cenv_shape_ok st cenv` `source_op`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. cenv_shape_ok st cenv /\ value_shape_ok st v` >>
     simp[cenv_shape_ok_stable, unwrap_value_shape]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ plain_operand st source_op`, `\u st. T`] >>
  simp[compile_tuple_unpack_shape]
QED

Theorem compile_annassign_shape:
  !e cenv lctx ty id vtyp internal.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (AnnAssign id vtyp e)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_sequence `\u st. cenv_shape_ok st cenv`
    (irule emit_local_alloca_shape) >>
  stmt_bind `\v st. value_shape_ok st v /\ cenv_shape_ok st cenv` `v`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule (cj 1 compile_expr_shape) >> simp[]) >>
  stmt_bind `\op st. plain_operand st op /\ cenv_shape_ok st cenv` `source_op`
    (IF_CASES_TAC
     >- (irule shape_step_return >>
         simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
     ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. cenv_shape_ok st cenv /\ value_shape_ok st v` >>
     simp[cenv_shape_ok_stable, unwrap_value_shape]) >>
  simp[stmt_return_bind] >>
  Cases_on `FLOOKUP cenv.ce_vars id`
  >- (simp[] >> stmt_drop (ho_match_mp_tac stmt_shape_emit_void >>
       simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
       stmt_shape_emit_simp)) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  TRY (stmt_drop (ho_match_mp_tac stmt_shape_emit_void >>
       simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
       stmt_shape_emit_simp) >> NO_TAC) >>
  suspend "stores"
QED

Resume compile_annassign_shape[stores]:
  markerLib.RESUME_TAC >> (rpt strip_tac >> IF_CASES_TAC
  >- (stmt_drop (ho_match_mp_tac stmt_shape_emit_void >>
       simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj,
            label_or_plain_def] >> stmt_shape_emit_simp >>
       simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
       rpt strip_tac >> drule_all cenv_shape_ok_lookup >>
       simp[loc_shape_ok_def, plain_operand_def])) >>
  qmatch_goalsub_abbrev_tac `compile_assign_value cenv dst LocMemory` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st dst /\ plain_operand st source_op`, `\u st. T`] >>
  simp[compile_assign_value_shape] >> rpt strip_tac >>
  gvs[Abbr `dst`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  drule_all cenv_shape_ok_lookup >> simp[loc_shape_ok_def, plain_operand_def])
QED
Finalise compile_annassign_shape[local]

Theorem compile_augassign_shape[local]:
  !bt e cenv lctx ty target_ty bop internal.
    ~supported_target_exists expr_shape_root bt /\
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (AugAssign target_ty bt bop e)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\r st. (plain_operand st (FST r) /\ FST (SND r) <> SOME LocCode) /\
    cenv_shape_ok st cenv` `r`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule compile_get_target_ptr_shape >> simp[]) >>
  simp[stmt_return_bind] >> Cases_on `FST (SND r)`
  >- (simp[] >> stmt_drop (ho_match_mp_tac stmt_shape_emit_void >>
       simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
       stmt_shape_emit_simp)) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[stmt_return_bind] >>
  (stmt_bind `\cur st. plain_operand st cur /\
       (plain_operand st (FST r) /\ cenv_shape_ok st cenv)` `cur`
     (ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st (FST r)` >>
      simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
      stmt_plain_emit) >>
   stmt_bind `\rhs st. plain_operand st rhs /\
       (plain_operand st cur /\ plain_operand st (FST r))` `rhs`
     (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
      simp[stmt_shape_stable_plain, shape_stable_conj] >>
      irule lower_value_shape >> simp[]) >>
   stmt_bind `\res st. plain_operand st res /\ plain_operand st (FST r)` `res`
     (ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st cur /\ plain_operand st rhs` >>
      simp[stmt_shape_stable_plain] >> irule compile_binop_shape) >>
   stmt_plain_void_drop)
QED

Theorem compile_append_shape:
  !bt e cenv lctx ty internal.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
      (compile_stmt cenv lctx ty (Append bt e)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\raw st. plain_operand st raw /\ cenv_shape_ok st cenv` `raw`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule lower_value_shape >> simp[]) >>
  stmt_bind `\staged st. plain_operand st staged /\ cenv_shape_ok st cenv` `staged`
    (suspend "stage") >>
  simp[stmt_return_bind] >>
  qmatch_goalsub_abbrev_tac `load_opc_for loc` >>
  reverse (Cases_on `loc <> LocCode`)
  >- (simp[shape_step_def] >> rpt strip_tac >>
      drule infer_array_location_not_code >> simp[Abbr `loc`] >>
      disch_then (qspec_then `target_to_expr bt` mp_tac) >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st (compile_target_base cenv bt) /\ plain_operand st staged`,
    `\u st. T`] >>
  simp[compile_dynarray_append_shape] >> metis_tac[compile_target_base_shape]
QED

Resume compile_append_shape[stage]:
  IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  stmt_bind `\buf st. plain_operand st buf.buf_operand /\
       (plain_operand st raw /\ cenv_shape_ok st cenv)` `buf`
       (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
        simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj,
             compile_alloc_buffer_shape]) >>
     stmt_sequence `\u st. plain_operand st buf.buf_operand /\ cenv_shape_ok st cenv`
       (suspend "store") >>
  irule shape_step_return >> simp[]
QED
Resume compile_append_shape[store]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. (plain_operand st buf.buf_operand /\ cenv_shape_ok st cenv) /\
           (plain_operand st buf.buf_operand /\ plain_operand st raw)`,
    `\u st. (plain_operand st buf.buf_operand /\ cenv_shape_ok st cenv) /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >>
  simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj,
       compile_store_memory_shape]
QED
Finalise compile_append_shape[local]

Theorem compile_load_tuple_elements_shape[local]:
  !tys cenv base offset internal.
    shape_step internal compiler_label (\st. plain_operand st base)
      (compile_load_tuple_elements cenv base tys offset)
      (\ops st. EVERY (plain_operand st) ops)
Proof
  Induct >> rpt gen_tac >> simp[compile_load_tuple_elements_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `emit_op ADD [base_op; _]` >>
  stmt_bind `\p st. plain_operand st p /\ plain_operand st base_op` `elem_ptr`
    (stmt_frame_emit `\st. plain_operand st base_op`) >>
  stmt_bind `\v st. plain_operand st v /\ plain_operand st base_op` `value_op`
    (stmt_frame_emit `\st. plain_operand st elem_ptr`) >>
  stmt_bind `\ops st. EVERY (plain_operand st) ops /\ plain_operand st value_op` `ops`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st base_op` >>
     simp[stmt_shape_stable_plain]) >>
  irule shape_step_return >> simp[]
QED

Theorem stmt_shape_stable_retpc[local]:
  !pc. shape_stable (\st. retpc_operand st pc \/ plain_operand st pc)
Proof
  rw[shape_stable_def] >> metis_tac[retpc_operand_mono, plain_operand_mono]
QED

Theorem stmt_ret_shape[local]:
  !front pc.
    shape_step T compiler_label
      (\st. EVERY (plain_operand st) front /\
            (retpc_operand st pc \/ plain_operand st pc))
      (emit_inst RET (front ++ [pc]) []) (\u st. T)
Proof
  rpt gen_tac >> rewrite_tac[shape_step_def] >> rpt strip_tac >>
  Cases_on `x` >>
  `!id. lowered_inst_ok T (mk_inst id RET (front ++ [pc]) [])` by
    (stmt_shape_emit_simp >>
     gvs[EVERY_MEM, plain_operand_def, retpc_operand_def,
         stackPlanTypesTheory.is_label_operand_def] >>
     metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  mp_tac (Q.SPECL [`compiler_label`, `\st. T`, `front`, `pc`]
    shape_step_emit_inst_ret) >>
  simp[stmt_shape_stable_const] >>
  simp[shape_step_def] >> disch_then drule >> gvs[]
QED

Theorem compile_internal_return_shape:
  !cenv ret_val pc count ret_ty src_ty elem_types buf.
    shape_step T compiler_label
      (\st. (retpc_operand st pc \/ plain_operand st pc) /\
            (case ret_val of NONE => T | SOME v => plain_operand st v) /\
            (case buf of NONE => T | SOME b => plain_operand st b))
      (compile_internal_return cenv ret_val pc count ret_ty src_ty elem_types buf)
      (\u st. T)
Proof
  rpt gen_tac >> simp[compile_internal_return_def] >> IF_CASES_TAC
  >- (Cases_on `ret_val` >> simp[]
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (plain_operand st) [] /\ (retpc_operand st pc \/ plain_operand st pc)`,
            `\u st. T`] >> simp[stmt_ret_shape, SRULE [] (Q.SPEC `[]` stmt_ret_shape),
      SRULE [] (Q.SPEC `[x]` stmt_ret_shape)]) >>
      IF_CASES_TAC
      >- (irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (plain_operand st) [x] /\ (retpc_operand st pc \/ plain_operand st pc)`,
            `\u st. T`] >> simp[stmt_ret_shape, SRULE [] (Q.SPEC `[]` stmt_ret_shape),
      SRULE [] (Q.SPEC `[x]` stmt_ret_shape)]) >>
      stmt_bind `\ops st. EVERY (plain_operand st) ops /\
        (retpc_operand st pc \/ plain_operand st pc)` `ops`
        (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. plain_operand st x` >>
         simp[stmt_shape_stable_retpc, compile_load_tuple_elements_shape]) >>
      irule stmt_ret_shape) >>
  Cases_on `buf` >> simp[]
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [] /\ (retpc_operand st pc \/ plain_operand st pc)`,
        `\u st. T`] >> simp[stmt_ret_shape, SRULE [] (Q.SPEC `[]` stmt_ret_shape),
      SRULE [] (Q.SPEC `[x]` stmt_ret_shape)]) >>
  Cases_on `ret_val` >> simp[]
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [] /\ (retpc_operand st pc \/ plain_operand st pc)`,
        `\u st. T`] >> simp[stmt_ret_shape, SRULE [] (Q.SPEC `[]` stmt_ret_shape),
      SRULE [] (Q.SPEC `[x]` stmt_ret_shape)]) >>
  stmt_sequence `\u st. retpc_operand st pc \/ plain_operand st pc`
    (suspend "copy") >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [] /\ (retpc_operand st pc \/ plain_operand st pc)`,
    `\u st. T`] >> simp[stmt_ret_shape, SRULE [] (Q.SPEC `[]` stmt_ret_shape),
      SRULE [] (Q.SPEC `[x]` stmt_ret_shape)]
QED

Resume compile_internal_return_shape[copy]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. (retpc_operand st pc \/ plain_operand st pc) /\
           (plain_operand st x /\ plain_operand st x')`,
    `\u st. (retpc_operand st pc \/ plain_operand st pc) /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >>
  simp[stmt_shape_stable_retpc, compile_store_memory_shape]
QED
Finalise compile_internal_return_shape[local]

val stmt_plain_inst_drop = stmt_drop
  (ho_match_mp_tac stmt_shape_emit_inst >>
   simp[stmt_shape_stable_plain, shape_stable_conj, stmt_shape_stable_const,
        label_or_plain_def] >> stmt_shape_emit_simp >>
   simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
   metis_tac[stackPlanTypesTheory.is_label_operand_def]);

Theorem compile_external_return_shape:
  !ret_val prim raw info max_size nr nkey trans view.
    shape_step F compiler_label
      (\st. case ret_val of NONE => T | SOME v => plain_operand st v)
      (compile_external_return ret_val prim raw info max_size nr nkey trans view)
      (\u st. T)
Proof
  rpt gen_tac >> simp[compile_external_return_def] >>
  stmt_sequence `\u st. case ret_val of NONE => T | SOME v => plain_operand st v`
    (suspend "unlock") >>
  Cases_on `ret_val` >> simp[] >- stmt_plain_inst_drop >>
  suspend "return"
QED

Resume compile_external_return_shape[unlock]:
  IF_CASES_TAC >- (irule shape_step_conseq >>
    qexistsl_tac [`compiler_label`,
      `\st. (case ret_val of NONE => T | SOME v => plain_operand st v) /\ T`,
      `\u st. (case ret_val of NONE => T | SOME v => plain_operand st v) /\ T`] >>
    rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
    ho_match_mp_tac shape_step_frame >>
    simp[compile_nonreentrant_unlock_shape] >> Cases_on `ret_val` >>
    simp[stmt_shape_stable_plain, stmt_shape_stable_const]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_external_return_shape[return]:
  IF_CASES_TAC
  >- (stmt_bind `\len st. plain_operand st len /\ plain_operand st x` `len`
        (stmt_frame_emit `\st. plain_operand st x`) >>
      stmt_bind `\off st. plain_operand st off /\ plain_operand st len` `off`
        (stmt_frame_emit `\st. plain_operand st x`) >>
      stmt_plain_inst_drop) >>
  IF_CASES_TAC
  >- (stmt_bind `\buf st. plain_operand st buf.buf_operand /\ plain_operand st x` `buf`
        (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
         simp[stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
      simp[stmt_return_bind] >>
      stmt_sequence `\u st. plain_operand st buf.buf_operand /\ plain_operand st x`
        stmt_plain_void >> stmt_plain_inst_drop) >>
  stmt_bind `\buf st. plain_operand st buf.buf_operand /\ plain_operand st x` `buf`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
     simp[stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
  simp[stmt_return_bind] >>
  stmt_bind `\len st. plain_operand st len /\ plain_operand st buf.buf_operand` `len`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st buf.buf_operand /\ plain_operand st x` >>
     simp[stmt_shape_stable_plain, cj 2 compile_abi_encode_shape]) >>
  stmt_plain_inst_drop
QED
Finalise compile_external_return_shape[local]

Theorem compile_internal_return_from_env_shape:
  !cenv ty src_ty value_op pc.
    shape_step T compiler_label
      (\st. cenv_shape_ok st cenv /\ plain_operand st value_op /\
            (retpc_operand st pc \/ plain_operand st pc))
      (compile_internal_return_from_env cenv ty src_ty value_op pc) (\u st. T)
Proof
  rpt gen_tac >> simp[compile_internal_return_from_env_def] >>
  stmt_bind `\buf st. (case buf of NONE => T | SOME b => plain_operand st b) /\
      (plain_operand st value_op /\ (retpc_operand st pc \/ plain_operand st pc))` `buf`
    (suspend "buffer") >>
  simp[stmt_return_bind] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. (retpc_operand st pc \/ plain_operand st pc) /\ plain_operand st value_op /\
           (case buf of NONE => T | SOME b => plain_operand st b)`, `\u st. T`] >>
  simp[SRULE [] (Q.INST [`ret_val` |-> `SOME value_op`]
    (SPEC_ALL compile_internal_return_shape))]
QED

Resume compile_internal_return_from_env_shape[buffer]:
  Cases_on `cenv.ce_return_buf` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `SOME loc` >>
  namedCases_on `loc` ["off sz", "slot", "slot", "imm", "ret_op sz"] >>
  simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  suspend "buffer_cases"
QED
Resume compile_internal_return_from_env_shape[buffer_cases]:
  markerLib.RESUME_TAC
  >- (stmt_bind `\b st. plain_operand st b /\
        (plain_operand st value_op /\ (retpc_operand st pc \/ plain_operand st pc))` `b`
        (ho_match_mp_tac stmt_shape_frame >>
         qexists_tac `\st. plain_operand st (Lit (n2w off))` >>
         simp[stmt_shape_stable_plain, stmt_shape_stable_retpc, shape_stable_conj] >>
         conj_tac >- stmt_plain_emit >>
         simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >> irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[] >> rpt strip_tac >>
  gvs[cenv_shape_ok_def, loc_shape_ok_def]
QED
Finalise compile_internal_return_from_env_shape[local]

Theorem compile_return_none_shape:
  !cenv lctx ty.
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmt cenv lctx ty (Return NONE)) (\u st. T)
Proof
  rpt gen_tac >> Cases_on `cenv.ce_return_pc` >>
  simp[Once compile_stmt_def]
  >- (pairarg_tac >> simp[] >>
      stmt_sequence `\u st. T`
        (IF_CASES_TAC
         >- (irule shape_step_conseq >>
             qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
             simp[compile_nonreentrant_unlock_shape]) >>
         irule shape_step_return >> simp[]) >> stmt_plain_inst_drop) >>
  rename1 `SOME loc` >>
  namedCases_on `loc` ["off sz", "slot", "slot", "imm", "ret_op sz"] >>
  simp[] >>
  TRY (simp[shape_step_def, cenv_shape_ok_def] >> NO_TAC) >>
  suspend "internal"
QED
Resume compile_return_none_shape[internal]:
  markerLib.RESUME_TAC
  >- (stmt_bind `\rpc st. plain_operand st rpc` `rpc`
        (irule shape_step_conseq >>
         qexistsl_tac [`compiler_label`, `\st. plain_operand st (Lit (n2w off))`,
           `\rpc st. plain_operand st rpc`] >>
         rpt conj_tac >> TRY (simp[plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def] >> NO_TAC) >> stmt_plain_emit) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [] /\ (retpc_operand st rpc \/ plain_operand st rpc)`,
        `\u st. T`] >> simp[SRULE [] (Q.SPEC `[]` stmt_ret_shape)]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [] /\
       (retpc_operand st ret_op \/ plain_operand st ret_op)`,
    `\u st. T`] >> simp[SRULE [] (Q.SPEC `[]` stmt_ret_shape)] >>
  rpt strip_tac >> gvs[cenv_shape_ok_def]
QED
Finalise compile_return_none_shape[local]

Theorem compile_return_some_shape:
  !cenv lctx ty e.
    ~supported_expr_exists expr_shape_root e ==>
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmt cenv lctx ty (Return (SOME e))) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\v st. plain_operand st v /\ cenv_shape_ok st cenv` `value_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule lower_value_shape >> simp[]) >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- suspend "external" >>
  rename1 `SOME loc` >>
  namedCases_on `loc` ["off sz", "slot", "slot", "imm", "ret_op sz"] >>
  simp[] >>
  TRY (simp[shape_step_def, cenv_shape_ok_def] >> NO_TAC) >>
  suspend "internal"
QED
Resume compile_return_some_shape[internal]:
  markerLib.RESUME_TAC
  >- (stmt_bind `\rpc st. plain_operand st rpc /\
         (plain_operand st value_op /\ cenv_shape_ok st cenv)` `rpc`
        (ho_match_mp_tac stmt_shape_frame >>
         qexists_tac `\st. plain_operand st (Lit (n2w off))` >>
         simp[shape_stable_conj, stmt_shape_stable_plain, cenv_shape_ok_stable] >>
         conj_tac >- stmt_plain_emit >>
         simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. cenv_shape_ok st cenv /\ plain_operand st value_op /\
          (retpc_operand st rpc \/ plain_operand st rpc)`, `\u st. T`] >>
      simp[compile_internal_return_from_env_shape]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ plain_operand st value_op /\
      (retpc_operand st ret_op \/ plain_operand st ret_op)`, `\u st. T`] >>
  simp[compile_internal_return_from_env_shape] >> rpt strip_tac >>
  gvs[cenv_shape_ok_def]
QED
Resume compile_return_some_shape[external]:
  stmt_bind `\v st. plain_operand st v` `ret_op`
    (IF_CASES_TAC
     >- (stmt_bind `\buf st. plain_operand st buf.buf_operand /\ plain_operand st value_op` `buf`
           (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
            simp[stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
         simp[stmt_return_bind] >>
         stmt_sequence `\u st. plain_operand st buf.buf_operand`
           (irule shape_step_conseq >>
            qexistsl_tac [`compiler_label`,
              `\st. plain_operand st buf.buf_operand /\
                 (plain_operand st buf.buf_operand /\ plain_operand st value_op)`,
              `\u st. plain_operand st buf.buf_operand /\ T`] >>
            rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
            ho_match_mp_tac shape_step_frame >>
            simp[stmt_shape_stable_plain, cj 1 compile_typed_copy_shape]) >>
         irule shape_step_return >> simp[]) >>
     irule shape_step_return >> simp[]) >>
  (* Raw returns now copy into another fresh typed buffer. *)
  stmt_bind `\v st. plain_operand st v` `raw_ret_op`
    (IF_CASES_TAC
     >- (stmt_bind `\buf st. plain_operand st buf.buf_operand /\ plain_operand st ret_op` `buf`
           (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. T` >>
            simp[stmt_shape_stable_plain, compile_alloc_buffer_shape]) >>
         stmt_sequence `\u st. plain_operand st buf.buf_operand`
           (irule shape_step_conseq >>
            qexistsl_tac [`compiler_label`,
              `\st. plain_operand st buf.buf_operand /\
                 (plain_operand st buf.buf_operand /\ plain_operand st ret_op)`,
              `\u st. plain_operand st buf.buf_operand /\ T`] >>
            rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
            ho_match_mp_tac shape_step_frame >>
            simp[stmt_shape_stable_plain, cj 1 compile_typed_copy_shape]) >>
         irule shape_step_return >> simp[]) >>
     irule shape_step_return >> simp[]) >>
  irule (SRULE [] (Q.INST [`ret_val` |-> `SOME raw_ret_op`]
    (SPEC_ALL compile_external_return_shape)))
QED
Finalise compile_return_some_shape[local]

Theorem compile_range_bound_checks_shape[local]:
  !internal start_op end_op rounds_op bound signed.
    shape_step internal compiler_label
      (\st. plain_operand st start_op /\ plain_operand st end_op /\
            plain_operand st rounds_op)
      (compile_range_bound_checks start_op end_op rounds_op bound signed)
      (\u st. T)
Proof
  rpt gen_tac >> simp[compile_range_bound_checks_def] >>
  stmt_bind `\v st. plain_operand st v /\ plain_operand st rounds_op` `bad_order`
    (IF_CASES_TAC >> stmt_frame_emit
      `\st. plain_operand st start_op /\ plain_operand st end_op`) >>
  stmt_bind `\v st. plain_operand st v /\ plain_operand st rounds_op` `good_order`
    (stmt_frame_emit `\st. plain_operand st bad_order`) >>
  stmt_sequence `\u st. plain_operand st good_order /\ plain_operand st rounds_op`
    stmt_plain_void >>
  stmt_bind `\v st. plain_operand st v` `bad_rounds` stmt_plain_emit >>
  stmt_bind `\v st. plain_operand st v` `good_rounds` stmt_plain_emit >>
  stmt_plain_void_drop
QED

Theorem compile_iter_elem_copy_shape[local]:
  !internal cenv src dst size loc slots target_ty elem_ty.
    loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_iter_elem_copy cenv src dst size loc slots target_ty elem_ty)
      (\u st. T)
Proof
  rpt strip_tac >> simp[compile_iter_elem_copy_def] >>
  Cases_on `slots` >> simp[]
  >- (IF_CASES_TAC
      >- (Cases_on `loc` >> gvs[] >>
          stmt_bind `\v st. plain_operand st v /\ plain_operand st dst` `value_op`
            (stmt_frame_emit `\st. plain_operand st src`) >> stmt_plain_void_drop) >>
      stmt_sequence `\u st. T` (irule compile_slot_to_memory_shape >> simp[]) >>
      irule shape_step_return >> simp[]) >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (Cases_on `loc` >> gvs[] >>
          stmt_bind `\v st. plain_operand st v /\ plain_operand st dst` `value_op`
            (stmt_frame_emit `\st. plain_operand st src`) >> stmt_plain_void_drop) >>
      Cases_on `loc` >> gvs[] >>
      FIRST [stmt_plain_void_drop >> NO_TAC,
        (irule shape_step_conseq >>
         qexistsl_tac [`compiler_label`,
           `\st. plain_operand st dst /\ plain_operand st src`, `\u st. T`] >>
         simp[compile_copy_memory_shape])]) >>
  IF_CASES_TAC
  >- (stmt_bind `\v st. plain_operand st v /\ plain_operand st dst` `value_op`
        (stmt_frame_emit `\st. plain_operand st src`) >> stmt_plain_void_drop) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st dst /\ plain_operand st src`, `\u st. T`] >>
  simp[compile_store_memory_shape]
QED

Theorem compile_if_shape:
  !cenv lctx ty cond_e then_body else_body.
    ~supported_expr_exists expr_shape_root cond_e /\
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmts cenv lctx ty then_body) (\u st. T) /\
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmts cenv lctx ty else_body) (\u st. T) ==>
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmt cenv lctx ty (If cond_e then_body else_body)) (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  qabbrev_tac `env_live = \st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx` >>
  `shape_stable env_live` by
    simp[Abbr `env_live`, cenv_shape_ok_stable, stmt_shape_stable_const, shape_stable_conj] >>
  stmt_bind `\v st. plain_operand st v /\ env_live st` `cond_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[Abbr `env_live`, cenv_shape_ok_stable, stmt_shape_stable_const, shape_stable_conj] >>
     irule lower_value_shape >> simp[]) >>
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st cond_op /\ env_live st) /\ compiler_label l` >>
  conj_tac
  >- (qx_gen_tac `then_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label then_lbl`)
      >- simp[shape_step_def] >> simp[] >>
      irule shape_step_bind >>
      qexists_tac `\l st. (plain_operand st cond_op /\ env_live st) /\ compiler_label l` >>
      conj_tac
      >- (qx_gen_tac `else_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label else_lbl`)
          >- simp[shape_step_def] >> simp[] >>
          irule shape_step_bind >>
          qexists_tac `\l st. (plain_operand st cond_op /\ env_live st) /\ compiler_label l` >>
          conj_tac
          >- (qx_gen_tac `exit_lbl` >> BETA_TAC >> reverse (Cases_on `compiler_label exit_lbl`)
              >- simp[shape_step_def] >> simp[] >> suspend "branches") >>
          ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
      ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_conj, stmt_shape_stable_plain]
QED
Resume compile_if_shape[branches]:
  stmt_sequence `\u st. plain_operand st cond_op /\ env_live st`
    (ho_match_mp_tac stmt_shape_jnz >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st cond_op /\ env_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. env_live st` (suspend "then_body") >>
  stmt_bind `\cs st. env_live st` `cs_then`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `env_live`, `\cs st. cs = st /\ env_live st`] >>
     simp[shape_step_comp_get]) >>
  simp[stmt_return_bind] >>
  stmt_sequence `\u st. env_live st` (suspend "jump") >>
  stmt_sequence `\u st. env_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[SF ETA_ss]) >>
  stmt_sequence `\u st. T` (suspend "else_body") >>
  stmt_bind `\cs st. T` `cs_else`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. T`, `\cs st. cs = st /\ T`] >>
     simp[shape_step_comp_get]) >>
  simp[stmt_return_bind] >>
  stmt_sequence `\u st. T`
    (irule emit_jmp_if_not_terminated_shape >> simp[jump_label_ok_def]) >>
  IF_CASES_TAC
  >- (stmt_sequence `\u st. T`
        (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_const]) >>
      irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_if_shape[then_body]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. env_live st /\ env_live st`,
    `\u st. env_live st /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[]
QED
Resume compile_if_shape[jump]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. env_live st /\ T`,
    `\u st. env_live st /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[] >>
  irule emit_jmp_if_not_terminated_shape >> simp[jump_label_ok_def]
QED
Resume compile_if_shape[else_body]:
  simp[SF ETA_ss]
QED
Finalise compile_if_shape[local]

fun stmt_label post name =
  stmt_bind post name
    (ho_match_mp_tac shape_step_fresh_label >> simp[SF ETA_ss]) >>
  (reverse (Cases_on (`compiler_label ` @ name)) >- simp[shape_step_def]) >> simp[];

Theorem compile_for_range_shape:
  !cenv lctx ty id fty start_e end_e bound body.
    ~supported_expr_exists expr_shape_root start_e /\
    ~supported_expr_exists expr_shape_root end_e /\
    (!env exit_lbl incr_lbl. shape_step (IS_SOME env.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st env /\ loop_ctx_shape_ok (InLoop exit_lbl incr_lbl))
      (compile_stmts env (InLoop exit_lbl incr_lbl) ty body) (\u st. T)) ==>
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body))
      (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\v st. plain_operand st v /\ cenv_shape_ok st cenv` `start_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule lower_value_shape >> simp[]) >>
  stmt_bind `\v st. plain_operand st v /\ (plain_operand st start_op /\ cenv_shape_ok st cenv)` `end_op`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
     irule lower_value_shape >> simp[]) >>
  stmt_bind `\env st. (cenv_shape_ok st env /\ env.ce_return_pc = cenv.ce_return_pc) /\
      (plain_operand st end_op /\ plain_operand st start_op)` `body_cenv`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj, declare_local_shape]) >>
  Cases_on `body_cenv.ce_return_pc = cenv.ce_return_pc`
  >- suspend "labels" >> simp[shape_step_def]
QED
Resume compile_for_range_shape[labels]:
  simp[] >>
  qabbrev_tac `live = \st. cenv_shape_ok st body_cenv /\
    plain_operand st end_op /\ plain_operand st start_op` >>
  `shape_stable live` by
    simp[Abbr `live`, cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
  stmt_sequence `\u st. live st`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`,
       `\st. (plain_operand st end_op /\ plain_operand st start_op) /\ cenv_shape_ok st body_cenv`,
       `\u st. (plain_operand st end_op /\ plain_operand st start_op) /\ cenv_shape_ok st body_cenv`] >>
     simp[Abbr `live`] >> ho_match_mp_tac shape_step_frame >>
     simp[stmt_shape_stable_plain, shape_stable_conj, emit_local_alloca_shape]) >>
  map_every (stmt_label `\l st. live st /\ compiler_label l`)
    [`entry_lbl`, `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`] >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[SF ETA_ss]) >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[SF ETA_ss]) >>
  stmt_bind `\n st. live st /\ plain_operand st (Var n)` `counter_var`
    (ho_match_mp_tac shape_step_fresh_var >> simp[SF ETA_ss]) >>
  suspend "counter"
QED
Resume compile_for_range_shape[counter]:
  qabbrev_tac `ctr_live = \st. live st /\ plain_operand st (Var counter_var)` >>
  `shape_stable ctr_live` by
    simp[Abbr `ctr_live`, shape_stable_conj, stmt_shape_stable_plain] >>
  stmt_sequence `\u st. ctr_live st`
    (ho_match_mp_tac stmt_shape_emit_inst >>
     simp[Abbr `ctr_live`, Abbr `live`, shape_stable_conj,
       cenv_shape_ok_stable, stmt_shape_stable_plain, label_or_plain_def] >>
     stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_bind `\r st. plain_operand st r /\ ctr_live st` `rounds` (suspend "rounds") >>
  stmt_sequence `\u st. plain_operand st rounds /\ ctr_live st` (suspend "checks") >>
  stmt_bind `\v st. plain_operand st v /\ ctr_live st` `end_val`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st start_op /\ plain_operand st rounds` >>
     simp[Abbr `ctr_live`, Abbr `live`, shape_stable_conj,
          cenv_shape_ok_stable, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. plain_operand st end_val /\ ctr_live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st end_val /\ ctr_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_bind `\v st. plain_operand st v /\ ctr_live st` `done_op`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (Var counter_var) /\ plain_operand st end_val` >>
     simp[Abbr `ctr_live`, shape_stable_conj, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. plain_operand st done_op /\ ctr_live st`
    (ho_match_mp_tac stmt_shape_jnz >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st done_op /\ ctr_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  suspend "body"
QED
Resume compile_for_range_shape[rounds]:
  Cases_on `start_op` >> Cases_on `end_op` >> simp[] >>
  TRY (irule shape_step_return >>
    simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `emit_op SUB ops` >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. EVERY (plain_operand st) ops` >>
  simp[Abbr `ops`, Abbr `ctr_live`, Abbr `live`, shape_stable_conj,
       cenv_shape_ok_stable, stmt_shape_stable_plain] >> stmt_plain_emit
QED
Resume compile_for_range_shape[checks]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. (plain_operand st rounds /\ ctr_live st) /\ (plain_operand st rounds /\ ctr_live st)`,
    `\u st. (plain_operand st rounds /\ ctr_live st) /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >>
  simp[shape_stable_conj, stmt_shape_stable_plain] >>
  Cases_on `start_op` >> Cases_on `end_op` >> simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `compile_range_bound_checks a b rounds` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st a /\ plain_operand st b /\ plain_operand st rounds`,
    `\u st. T`] >>
  simp[compile_range_bound_checks_shape, Abbr `ctr_live`, Abbr `live`]
QED
Resume compile_for_range_shape[body]:
  stmt_sequence `\u st. ctr_live st` (suspend "store") >>
  stmt_sequence `\u st. plain_operand st (Var counter_var)` (suspend "recursive") >>
  stmt_sequence `\u st. plain_operand st (Var counter_var)`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. plain_operand st (Var counter_var) /\ T`,
       `\u st. plain_operand st (Var counter_var) /\ T`] >>
     rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
     ho_match_mp_tac shape_step_frame >> simp[stmt_shape_stable_plain] >>
     irule emit_jmp_if_not_terminated_shape >> simp[jump_label_ok_def]) >>
  stmt_sequence `\u st. plain_operand st (Var counter_var)`
    (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_plain]) >>
  stmt_bind `\v st. plain_operand st v /\ plain_operand st (Var counter_var)` `new_counter`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (Var counter_var)` >>
     simp[stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. plain_operand st new_counter /\ plain_operand st (Var counter_var)`
    (ho_match_mp_tac stmt_shape_emit_inst >> simp[shape_stable_conj,
       stmt_shape_stable_plain, label_or_plain_def] >> stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. plain_operand st new_counter /\ plain_operand st (Var counter_var)`
    (ho_match_mp_tac stmt_shape_jmp >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st new_counter /\ plain_operand st (Var counter_var)`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_for_range_shape[store]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `ctr_live`, `\u st. ctr_live st`] >>
  simp[] >>
  Cases_on `FLOOKUP body_cenv.ce_vars id` >> simp[] >>
  TRY (ho_match_mp_tac stmt_shape_emit_void >> simp[SF ETA_ss] >>
       stmt_shape_emit_simp >> NO_TAC) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  ho_match_mp_tac stmt_shape_emit_void >> simp[SF ETA_ss] >>
  simp[Abbr `ctr_live`, Abbr `live`, label_or_plain_def] >>
  stmt_shape_emit_simp >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  rpt strip_tac >> drule_all cenv_shape_ok_lookup >>
  simp[loc_shape_ok_def, plain_operand_def]
QED
Resume compile_for_range_shape[recursive]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st (Var counter_var) /\
      (cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok (InLoop exit_lbl incr_lbl))`,
    `\u st. plain_operand st (Var counter_var) /\ T`] >>
  rpt conj_tac >> TRY (simp[Abbr `ctr_live`, Abbr `live`, loop_ctx_shape_ok_def, jump_label_ok_def] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[stmt_shape_stable_plain] >>
  first_x_assum (qspecl_then [`body_cenv`, `exit_lbl`, `incr_lbl`] mp_tac) >> simp[]
QED
Finalise compile_for_range_shape[local]

Theorem compile_for_array_shape:
  !cenv lctx ty id fty arr_e bound body.
    ~supported_expr_exists expr_shape_root arr_e /\
    (!env exit_lbl incr_lbl. shape_step (IS_SOME env.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st env /\ loop_ctx_shape_ok (InLoop exit_lbl incr_lbl))
      (compile_stmts env (InLoop exit_lbl incr_lbl) ty body) (\u st. T)) ==>
    shape_step (IS_SOME cenv.ce_return_pc) compiler_label
      (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
      (compile_stmt cenv lctx ty (For id fty (Array arr_e) bound body))
      (\u st. T)
Proof
  rpt strip_tac >> simp[Once compile_stmt_def] >>
  stmt_bind `\v st. value_shape_ok st v /\ cenv_shape_ok st cenv` `arr_vv`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable] >> irule (cj 1 compile_expr_shape) >> simp[]) >>
  simp[stmt_return_bind] >>
  qmatch_goalsub_abbrev_tac `load_opc_for loc` >>
  reverse (Cases_on `loc <> LocCode`)
  >- (simp[shape_step_def] >> rpt strip_tac >>
      drule infer_array_location_not_code >> simp[Abbr `loc`] >>
      disch_then (qspec_then `arr_e` mp_tac) >> simp[]) >>
  stmt_bind `\v st. plain_operand st v /\
       (plain_operand st (vv_operand arr_vv) /\ cenv_shape_ok st cenv)` `len_op`
    (suspend "length") >>
  stmt_bind `\env st. (cenv_shape_ok st env /\ env.ce_return_pc = cenv.ce_return_pc) /\
      (plain_operand st len_op /\ plain_operand st (vv_operand arr_vv) /\ cenv_shape_ok st cenv)` `body_cenv`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj, declare_local_shape]) >>
  Cases_on `body_cenv.ce_return_pc = cenv.ce_return_pc`
  >- suspend "labels" >> simp[shape_step_def]
QED
Resume compile_for_array_shape[length]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st (vv_operand arr_vv) /\ cenv_shape_ok st cenv`,
    `\v st. plain_operand st v /\ plain_operand st (vv_operand arr_vv) /\ cenv_shape_ok st cenv`] >>
  rpt conj_tac >> TRY (simp[value_shape_ok_operand] >> NO_TAC) >>
  IF_CASES_TAC
  >- (ho_match_mp_tac stmt_shape_frame >>
      qexists_tac `\st. plain_operand st (vv_operand arr_vv)` >>
      simp[cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
      Cases_on `loc` >> gvs[load_opc_for_def] >> stmt_plain_emit) >>
  irule shape_step_return >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_for_array_shape[labels]:
  simp[] >>
  qabbrev_tac `live = \st. cenv_shape_ok st body_cenv /\
    plain_operand st len_op /\ plain_operand st (vv_operand arr_vv) /\ cenv_shape_ok st cenv` >>
  `shape_stable live` by
    simp[Abbr `live`, cenv_shape_ok_stable, stmt_shape_stable_plain, shape_stable_conj] >>
  stmt_sequence `\u st. live st`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`,
       `\st. live st /\ cenv_shape_ok st body_cenv`,
       `\u st. live st /\ cenv_shape_ok st body_cenv`] >>
     rpt conj_tac >> TRY (simp[Abbr `live`] >> NO_TAC) >>
     ho_match_mp_tac shape_step_frame >> simp[emit_local_alloca_shape]) >>
  stmt_sequence `\u st. live st` (suspend "check") >>
  map_every (stmt_label `\l st. live st /\ compiler_label l`)
    [`entry_lbl`, `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`] >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[SF ETA_ss]) >>
  stmt_sequence `\u st. live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[SF ETA_ss]) >>
  stmt_bind `\n st. live st /\ plain_operand st (Var n)` `idx_var`
    (ho_match_mp_tac shape_step_fresh_var >> simp[SF ETA_ss]) >>
  suspend "index"
QED
Resume compile_for_array_shape[check]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. live st /\ plain_operand st len_op`,
    `\u st. live st /\ T`] >>
  rpt conj_tac >> TRY (simp[Abbr `live`] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[] >>
  IF_CASES_TAC
  >- (stmt_bind `\v st. plain_operand st v` `invalid` stmt_plain_emit >>
      stmt_bind `\v st. plain_operand st v` `valid` stmt_plain_emit >>
      stmt_plain_void_drop) >>
  irule shape_step_return >> simp[]
QED
Resume compile_for_array_shape[index]:
  qabbrev_tac `idx_live = \st. live st /\ plain_operand st (Var idx_var)` >>
  `shape_stable idx_live` by
    simp[Abbr `idx_live`, shape_stable_conj, stmt_shape_stable_plain] >>
  stmt_sequence `\u st. idx_live st`
    (ho_match_mp_tac stmt_shape_emit_inst >> simp[SF ETA_ss] >>
     stmt_shape_emit_simp >> simp[label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. idx_live st`
    (ho_match_mp_tac stmt_shape_jmp >> simp[SF ETA_ss]) >>
  stmt_sequence `\u st. idx_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[SF ETA_ss]) >>
  stmt_bind `\v st. plain_operand st v /\ idx_live st` `done_op`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (Var idx_var) /\ plain_operand st len_op` >>
     simp[Abbr `idx_live`, Abbr `live`, shape_stable_conj,
          cenv_shape_ok_stable, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. plain_operand st done_op /\ idx_live st`
    (ho_match_mp_tac stmt_shape_jnz >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st done_op /\ idx_live st`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_bind `\v st. plain_operand st v /\ idx_live st` `idx_offset`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (Var idx_var)` >>
     simp[Abbr `idx_live`, shape_stable_conj, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_bind `\v st. plain_operand st v /\ idx_live st` `total_offset`
    (IF_CASES_TAC
     >- (ho_match_mp_tac stmt_shape_frame >>
         qexists_tac `\st. plain_operand st idx_offset` >>
         simp[stmt_shape_stable_plain] >> stmt_plain_emit) >>
     irule shape_step_return >> simp[]) >>
  stmt_bind `\v st. plain_operand st v /\ idx_live st` `elem_ptr`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (vv_operand arr_vv) /\ plain_operand st total_offset` >>
     simp[Abbr `idx_live`, Abbr `live`, shape_stable_conj,
          cenv_shape_ok_stable, stmt_shape_stable_plain] >> stmt_plain_emit) >>
  suspend "body"
QED
Resume compile_for_array_shape[body]:
  stmt_sequence `\u st. idx_live st` (suspend "copy") >>
  stmt_sequence `\u st. plain_operand st (Var idx_var)` (suspend "recursive") >>
  stmt_sequence `\u st. plain_operand st (Var idx_var)`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. plain_operand st (Var idx_var) /\ T`,
       `\u st. plain_operand st (Var idx_var) /\ T`] >>
     rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
     ho_match_mp_tac shape_step_frame >> simp[stmt_shape_stable_plain] >>
     irule emit_jmp_if_not_terminated_shape >> simp[jump_label_ok_def]) >>
  stmt_sequence `\u st. plain_operand st (Var idx_var)`
    (ho_match_mp_tac stmt_shape_new_block >> simp[stmt_shape_stable_plain]) >>
  stmt_bind `\v st. plain_operand st v /\ plain_operand st (Var idx_var)` `new_idx`
    (ho_match_mp_tac stmt_shape_frame >>
     qexists_tac `\st. plain_operand st (Var idx_var)` >>
     simp[stmt_shape_stable_plain] >> stmt_plain_emit) >>
  stmt_sequence `\u st. plain_operand st new_idx /\ plain_operand st (Var idx_var)`
    (ho_match_mp_tac stmt_shape_emit_inst >> simp[shape_stable_conj,
       stmt_shape_stable_plain, label_or_plain_def] >> stmt_shape_emit_simp >>
     simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  stmt_sequence `\u st. plain_operand st new_idx /\ plain_operand st (Var idx_var)`
    (ho_match_mp_tac stmt_shape_jmp >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  stmt_sequence `\u st. plain_operand st new_idx /\ plain_operand st (Var idx_var)`
    (ho_match_mp_tac stmt_shape_new_block >> simp[shape_stable_conj, stmt_shape_stable_plain]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_for_array_shape[copy]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. idx_live st /\ (plain_operand st elem_ptr /\ idx_live st)`,
    `\u st. idx_live st /\ T`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[] >>
  Cases_on `FLOOKUP body_cenv.ce_vars id` >> simp[]
  >- stmt_plain_void_drop >>
  rename1 `SOME vloc` >> Cases_on `vloc` >> simp[] >>
  TRY (stmt_plain_void_drop >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `compile_iter_elem_copy cenv elem_ptr dst` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st elem_ptr /\ plain_operand st dst`, `\u st. T`] >>
  simp[compile_iter_elem_copy_shape] >> rpt strip_tac >>
  gvs[Abbr `dst`, Abbr `idx_live`, Abbr `live`, plain_operand_def,
      stackPlanTypesTheory.is_label_operand_def] >>
  drule_all cenv_shape_ok_lookup >> simp[loc_shape_ok_def, plain_operand_def]
QED
Resume compile_for_array_shape[recursive]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. plain_operand st (Var idx_var) /\
      (cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok (InLoop exit_lbl incr_lbl))`,
    `\u st. plain_operand st (Var idx_var) /\ T`] >>
  rpt conj_tac >> TRY (simp[Abbr `idx_live`, Abbr `live`, loop_ctx_shape_ok_def, jump_label_ok_def] >> NO_TAC) >>
  ho_match_mp_tac shape_step_frame >> simp[stmt_shape_stable_plain] >>
  first_x_assum (qspecl_then [`body_cenv`, `exit_lbl`, `incr_lbl`] mp_tac) >> simp[]
QED
Finalise compile_for_array_shape[local]

(* By compile_stmt_ind.  internal is IS_SOME ce_return_pc: Return
   emits RET exactly when ce_return_pc is SOME, STOP/RETURN otherwise. *)
Theorem compile_stmt_shape:
  (!cenv lctx ty s.
     ~supported_stmt_expr_exists expr_shape_root s ==>
     shape_step (IS_SOME cenv.ce_return_pc) compiler_label
       (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
       (compile_stmt cenv lctx ty s) (\x st. T)) /\
  (!cenv lctx ty ss.
     ~supported_stmts_expr_exists expr_shape_root ss ==>
     shape_step (IS_SOME cenv.ce_return_pc) compiler_label
       (\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)
       (compile_stmts cenv lctx ty ss) (\x st. T))
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def,
       supported_iterator_exists_def, supported_assert_exists_def,
       supported_raise_exists_def, supported_expr_exists_def] >>
  rpt strip_tac >>
  FIRST [
    (irule compile_return_none_shape >> NO_TAC),
    (irule compile_return_some_shape >> simp[] >> NO_TAC),
    (irule compile_if_shape >> simp[] >> NO_TAC),
    (rename1 `compile_stmt _ _ _ (For _ _ (Range _ _) _ _)` >> suspend "range"),
    (rename1 `compile_stmt _ _ _ (For _ _ (Array _) _ _)` >> suspend "array"),
    (rename1 `compile_stmts _ _ _ (_::_)` >> suspend "cons"),
    (rename1 `compile_stmts _ _ _ []` >> simp[Once compile_stmt_def] >>
      irule shape_step_return >> simp[] >> NO_TAC),
    (rename1 `compile_stmt _ _ _ Pass` >> simp[Once compile_stmt_def] >>
      irule shape_step_return >> simp[] >> NO_TAC),
    (rename1 `compile_stmt _ _ _ Break` >> suspend "break"),
    (rename1 `compile_stmt _ _ _ Continue` >> suspend "continue"),
    (rename1 `compile_stmt _ _ _ (Expr _)` >> suspend "expr"),
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv`, `\u st. T`] >>
     simp[] >>
     FIRST [irule compile_raise_shape, irule compile_assert_shape,
            irule compile_assign_base_shape, irule compile_assign_tuple_shape,
            irule compile_augassign_shape, irule compile_append_shape,
            irule compile_log_shape, irule compile_annassign_shape] >>
     simp[supported_stmt_expr_exists_def, supported_raise_exists_def,
          supported_assert_exists_def] >>
     qpat_x_assum `~supported_expr_exists _ _` kall_tac >>
     pop_assum mp_tac >> Induct_on `targets` >>
     simp[supported_assignment_exists_def] >>
     Cases_on `h` >> simp[supported_assignment_exists_def])]
QED
Resume compile_stmt_shape[range]:
  irule compile_for_range_shape >> simp[]
QED
Resume compile_stmt_shape[array]:
  irule compile_for_array_shape >> simp[]
QED
Resume compile_stmt_shape[cons]:
  simp[Once compile_stmt_def] >>
  stmt_bind `\cs st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx` `cs`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx`,
       `\cs st. cs = st /\ (cenv_shape_ok st cenv /\ loop_ctx_shape_ok lctx)`] >>
     simp[shape_step_comp_get]) >>
  IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  qpat_x_assum `!cs env. _ ==> _ ==> shape_step _ _ _ (compile_stmt _ _ _ _) _`
    (qspec_then `cs` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!cs env. _ ==> _ ==> shape_step _ _ _ (compile_stmts _ _ _ _) _`
    (qspec_then `cs` mp_tac) >> simp[] >> strip_tac >>
  stmt_bind `\env st. (cenv_shape_ok st env /\ env.ce_return_pc = cenv.ce_return_pc) /\
    loop_ctx_shape_ok lctx` `body_cenv`
    (ho_match_mp_tac stmt_shape_frame >> qexists_tac `\st. cenv_shape_ok st cenv` >>
     simp[stmt_shape_stable_const, declare_stmt_local_shape]) >>
  Cases_on `body_cenv.ce_return_pc = cenv.ce_return_pc`
  >- suspend "cons_body" >> simp[shape_step_def]
QED
Resume compile_stmt_shape[cons_body]:
  qpat_x_assum `!env. shape_step _ _ _ (compile_stmt _ _ _ _) _`
    (qspec_then `body_cenv` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env. shape_step _ _ _ (compile_stmts _ _ _ _) _`
    (qspec_then `body_cenv` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  stmt_sequence `\u st. cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok lctx`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`,
       `\st. (cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok lctx) /\
             (cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok lctx)`,
       `\u st. (cenv_shape_ok st body_cenv /\ loop_ctx_shape_ok lctx) /\ T`] >>
     rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
     ho_match_mp_tac shape_step_frame >>
     simp[cenv_shape_ok_stable, shape_stable_conj, stmt_shape_stable_const]) >>
  simp[]
QED
Resume compile_stmt_shape[break]:
  markerLib.RESUME_TAC >> simp[Once compile_stmt_def]
  >- (stmt_sequence `\u st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok NoLoop`
        (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
          simp[shape_stable_conj, cenv_shape_ok_stable, stmt_shape_stable_const] >>
          stmt_shape_emit_simp)) >> irule shape_step_return >> simp[]) >>
  stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
    simp[shape_stable_conj, cenv_shape_ok_stable, stmt_shape_stable_const,
         label_or_plain_def] >> stmt_shape_emit_simp >>
    simp[loop_ctx_shape_ok_def, stackPlanTypesTheory.is_label_operand_def])
QED
Resume compile_stmt_shape[continue]:
  markerLib.RESUME_TAC >> simp[Once compile_stmt_def]
  >- (stmt_sequence `\u st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok NoLoop`
        (stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
          simp[shape_stable_conj, cenv_shape_ok_stable, stmt_shape_stable_const] >>
          stmt_shape_emit_simp)) >> irule shape_step_return >> simp[]) >>
  stmt_drop (ho_match_mp_tac stmt_shape_emit_inst >>
    simp[shape_stable_conj, cenv_shape_ok_stable, stmt_shape_stable_const,
         label_or_plain_def] >> stmt_shape_emit_simp >>
    simp[loop_ctx_shape_ok_def, stackPlanTypesTheory.is_label_operand_def])
QED
Resume compile_stmt_shape[expr]:
  simp[Once compile_stmt_def] >>
  stmt_sequence `\v st. value_shape_ok st v`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv`,
       `\v st. value_shape_ok st v`] >> simp[compile_expr_shape]) >>
  irule shape_step_return >> simp[]
QED
Finalise compile_stmt_shape

(* ===== Module lowering ===== *)

Theorem shape_step_emit_op_under:
  !internal LP P opc ops.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) /\
    (!st. P st ==> EVERY (label_or_plain st) ops) ==>
    shape_step internal LP P (emit_op opc ops)
      (\x st. P st /\ plain_operand st x)
Proof
  rpt strip_tac >> irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. P st /\ EVERY (label_or_plain st) ops`,
               `\x st. P st /\ plain_operand st x`] >>
  simp[] >> irule shape_step_emit_op >> simp[]
QED

Theorem shape_step_emit_inst_under:
  !internal LP P opc ops outs.
    shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) /\
    (!st. P st ==> EVERY (label_or_plain st) ops) ==>
    shape_step internal LP P (emit_inst opc ops outs) (\x st. P st)
Proof
  rpt strip_tac >> irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. P st /\ EVERY (label_or_plain st) ops`,
               `\x st. P st`] >>
  simp[] >> irule shape_step_emit_inst >> simp[]
QED

Theorem shape_step_pre_fact:
  !internal LP P m Q b.
    (!st. P st ==> b) /\
    (b ==> shape_step internal LP P m Q) ==>
    shape_step internal LP P m Q
Proof
  rw[shape_step_def] >> metis_tac[]
QED

Theorem compile_selector_checks_shape:
  !selectors method_id.
    EVERY (\(sel,lbl). jump_label_ok lbl) selectors ==>
    shape_step F jump_label_ok (\st. plain_operand st method_id)
      (compile_selector_checks method_id selectors) (\x st. T)
Proof
  Induct_on `selectors`
  >- (simp[compile_selector_checks_def] >> rpt gen_tac >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> PairCases_on `h` >> simp[Once compile_selector_checks_def] >>
  rpt strip_tac >> irule shape_step_pre_fact >>
  qexists_tac `~is_label_operand method_id` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\x st. plain_operand st method_id /\ plain_operand st x` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      conj_tac
      >- (qspec_then `[method_id]` mp_tac shape_stable_plain_operands >> simp[]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def,
           inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
           mk_inst_def, is_terminator_def, is_param_opcode_def,
           inst_jump_labels_ok_def, label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\l st. (plain_operand st method_id /\ plain_operand st x) /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ml` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\l st. ((plain_operand st method_id /\ plain_operand st x) /\ compiler_label ml) /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `nl` >> BETA_TAC >> suspend "branches"
QED

Resume compile_selector_checks_shape[branches]:
  irule shape_step_pre_fact >>
  qexists_tac `~is_label_operand x /\ compiler_label ml /\ compiler_label nl` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. ((plain_operand st method_id /\ plain_operand st x) /\ compiler_label ml) /\ compiler_label nl` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_inst_under >>
      conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           jump_label_ok_def, label_or_plain_def,
           stackPlanTypesTheory.is_label_operand_def] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`jump_label_ok`, `\st. plain_operand st method_id`, `\u st. T`] >>
  simp[] >> suspend "blocks"
QED

Resume compile_selector_checks_shape[blocks]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st method_id` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_new_block >>
      simp[jump_label_ok_def] >>
      qspec_then `[method_id]` mp_tac shape_stable_plain_operands >> simp[]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st method_id` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_inst_under >>
      conj_tac
      >- (qspec_then `[method_id]` mp_tac shape_stable_plain_operands >> simp[]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           label_or_plain_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st method_id` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_new_block >>
      simp[jump_label_ok_def] >>
      qspec_then `[method_id]` mp_tac shape_stable_plain_operands >> simp[]) >>
  simp[]
QED

Finalise compile_selector_checks_shape

(* Straight-line code, fresh labels and JMPs to the selector labels. *)
Theorem compile_selector_dispatch_linear_shape:
  !selectors fallback_lbl.
    EVERY (\(sel, lbl). jump_label_ok lbl) selectors /\
    jump_label_ok fallback_lbl ==>
    shape_step F jump_label_ok (\st. T)
      (compile_selector_dispatch_linear selectors fallback_lbl) (\x st. T)
Proof
  rpt strip_tac >> simp[compile_selector_dispatch_linear_def] >>
  irule shape_step_bind >>
  qexists_tac `\x st. T /\ plain_operand st x` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
           inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
           mk_inst_def, is_terminator_def, is_param_opcode_def,
           inst_jump_labels_ok_def]) >>
  qx_gen_tac `cds` >> BETA_TAC >>
  irule shape_step_pre_fact >> qexists_tac `~is_label_operand cds` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\x st. (T /\ plain_operand st cds) /\ plain_operand st x` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      conj_tac
      >- (qspec_then `[cds]` mp_tac shape_stable_plain_operands >> simp[]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `has_sel` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`jump_label_ok`, `\st. plain_operand st has_sel`, `\u st. T`] >>
  simp[] >> suspend "iszero"
QED

Resume compile_selector_dispatch_linear_shape[iszero]:
  irule shape_step_pre_fact >> qexists_tac `~is_label_operand has_sel` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\x st. plain_operand st has_sel /\ plain_operand st x` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      conj_tac
      >- (qspec_then `[has_sel]` mp_tac shape_stable_plain_operands >> simp[]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           label_or_plain_def]) >>
  qx_gen_tac `cond` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`jump_label_ok`, `\st. plain_operand st cond`, `\u st. T`] >>
  simp[] >>
  irule shape_step_bind >>
  qexists_tac `\l st. plain_operand st cond /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      qspec_then `[cond]` mp_tac shape_stable_plain_operands >> simp[]) >>
  qx_gen_tac `dispatch` >> BETA_TAC >> suspend "jump"
QED

Resume compile_selector_dispatch_linear_shape[jump]:
  irule shape_step_pre_fact >>
  qexists_tac `~is_label_operand cond /\ compiler_label dispatch` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st cond /\ compiler_label dispatch` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_inst_under >>
      conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           label_or_plain_def, stackPlanTypesTheory.is_label_operand_def] >>
      rpt strip_tac >> gvs[jump_label_ok_def] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st cond /\ compiler_label dispatch` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_new_block >>
      simp[jump_label_ok_def] >> rw[shape_stable_def] >>
      metis_tac[plain_operand_mono]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`jump_label_ok`, `\st. T`, `\u st. T`] >>
  simp[] >> suspend "load"
QED

Resume compile_selector_dispatch_linear_shape[load]:
  irule shape_step_bind >>
  qexists_tac `\x st. T /\ plain_operand st x` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
           inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
           mk_inst_def, is_terminator_def, is_param_opcode_def,
           inst_jump_labels_ok_def, label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `raw` >> BETA_TAC >>
  irule shape_step_pre_fact >> qexists_tac `~is_label_operand raw` >>
  conj_tac >- simp[plain_operand_def] >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\x st. (T /\ plain_operand st raw) /\ plain_operand st x` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_under >>
      conj_tac
      >- (qspec_then `[raw]` mp_tac shape_stable_plain_operands >> simp[]) >>
      simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
           label_positions_ok_def, is_read0_opcode_def, mk_inst_def,
           is_terminator_def, is_param_opcode_def, inst_jump_labels_ok_def,
           label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `method_id` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`jump_label_ok`, `\st. plain_operand st method_id`, `\u st. T`] >>
  simp[] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >>
  reverse conj_tac >- simp[compile_selector_checks_shape] >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac shape_step_emit_inst_under >>
  simp[shape_stable_def, lowered_inst_ok_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
       mk_inst_def, is_terminator_def, is_param_opcode_def,
       inst_jump_labels_ok_def, label_or_plain_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Finalise compile_selector_dispatch_linear_shape


Theorem extbodies_emit_plain:
  !internal LP live opc ops.
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st id outs. EVERY (plain_operand st) live ==>
       lowered_inst_ok internal (mk_inst id opc ops outs)) /\
    (!st. EVERY (plain_operand st) live ==> EVERY (plain_operand st) ops) ==>
    shape_step internal LP (\st. EVERY (plain_operand st) live)
      (emit_op opc ops) (\x st. EVERY (plain_operand st) (x::live))
Proof
  rpt strip_tac >>
  Cases_on `?st. EVERY (plain_operand st) live`
  >- (pop_assum (qx_choose_then `s` assume_tac) >>
      qpat_assum `!st id outs. _` (drule_then assume_tac) >>
      irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. EVERY (plain_operand st) live /\
                         EVERY (label_or_plain st) ops`,
               `\x st. EVERY (plain_operand st) live /\ plain_operand st x`] >>
  simp[] >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op >> simp[shape_stable_plain_operands]) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[EVERY_MEM, label_or_plain_def] >> metis_tac[]) >>
  rw[shape_step_def] >> metis_tac[]
QED

Theorem extbodies_emit_void_plain:
  !internal LP live opc ops.
    ~MEM opc [GAS; RETPC_PARAM] /\
    (!st id. EVERY (plain_operand st) live ==>
       lowered_inst_ok internal (mk_inst id opc ops [])) /\
    (!st. EVERY (plain_operand st) live ==> EVERY (label_or_plain st) ops) ==>
    shape_step internal LP (\st. EVERY (plain_operand st) live)
      (emit_void opc ops) (\x st. EVERY (plain_operand st) live)
Proof
  rpt strip_tac >>
  Cases_on `?st. EVERY (plain_operand st) live`
  >- (pop_assum (qx_choose_then `s` assume_tac) >>
      qpat_assum `!st id. _` (drule_then assume_tac) >>
      irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. EVERY (plain_operand st) live /\
                         EVERY (label_or_plain st) ops`,
               `\x st. EVERY (plain_operand st) live`] >>
  simp[] >>
  ho_match_mp_tac shape_step_emit_void >> simp[shape_stable_plain_operands]) >>
  rw[shape_step_def] >> metis_tac[]
QED

val extbodies_opcode_tac =
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, jump_label_ok_def, is_terminator_def,
       is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
       plain_operand_def, label_or_plain_def, stackPlanTypesTheory.is_label_operand_def];

(* The three clamp forms have the same emit/emit/assert proof skeleton. *)
val extbodies_clamp_tac =
  irule shape_step_bind >>
  qexists_tac `\x st. EVERY (plain_operand st) [x; v]` >> conj_tac
  >- (qx_gen_tac `x` >> BETA_TAC >> irule shape_step_bind >>
      qexists_tac `\y st. EVERY (plain_operand st) [y; x; v]` >> conj_tac
      >- (qx_gen_tac `y` >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (plain_operand st) [y; x; v]`,
            `\u st. EVERY (plain_operand st) [y; x; v]`] >>
          simp_tac bool_ss [] >> ho_match_mp_tac extbodies_emit_void_plain >>
          extbodies_opcode_tac) >>
      ho_match_mp_tac extbodies_emit_plain >> extbodies_opcode_tac) >>
  ho_match_mp_tac extbodies_emit_plain >> extbodies_opcode_tac;

Theorem compile_abi_bytes_clamp_shape:
  !v m. shape_step F compiler_label (\st. EVERY (plain_operand st) [v])
    (compile_abi_bytes_clamp v m) (\x st. T)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_abi_bytes_clamp_def, LET_THM] >>
  BETA_TAC >> extbodies_clamp_tac
QED

Theorem compile_abi_int_clamp_shape:
  !v bits signed. shape_step F compiler_label (\st. EVERY (plain_operand st) [v])
    (compile_abi_int_clamp v bits signed) (\x st. T)
Proof
  rpt gen_tac >> Cases_on `signed` >>
  pure_rewrite_tac[compile_abi_int_clamp_def, LET_THM, COND_CLAUSES] >>
  BETA_TAC >> extbodies_clamp_tac
QED

Theorem compile_abi_clamp_basetype_shape:
  !v clamp. shape_step F compiler_label (\st. EVERY (plain_operand st) [v])
    (compile_abi_clamp_basetype v clamp) (\x st. T)
Proof
  gen_tac >> Cases >>
  pure_rewrite_tac[compile_abi_clamp_basetype_def]
  >- (irule shape_step_return >> simp[])
  >- (irule compile_abi_int_clamp_shape)
  >- (irule compile_abi_bytes_clamp_shape) >>
  extbodies_clamp_tac
QED

(* Deterministic composition of an ordinary emit with its continuation. *)
fun extbodies_emit_bind post name cont =
  irule shape_step_bind >> qexists_tac post >> conj_tac
  >- (qx_gen_tac name >> BETA_TAC >> cont) >>
  ho_match_mp_tac extbodies_emit_plain >> extbodies_opcode_tac;

fun extbodies_void_bind post cont =
  irule shape_step_ignore_bind >> qexists_tac post >> conj_tac
  >- (gen_tac >> BETA_TAC >> cont) >>
  ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac;

Theorem compile_getelemptr_abi_shape:
  !src dynamic off.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [src])
      (compile_getelemptr_abi src dynamic off CALLDATALOAD)
      (\ptr st. plain_operand st ptr)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_getelemptr_abi_def] >>
  extbodies_emit_bind `\head st. EVERY (plain_operand st) [head; src]` `head`
    (Cases_on `dynamic` >> pure_rewrite_tac[COND_CLAUSES, NOT_CLAUSES]
     >- extbodies_emit_bind `\offv st. EVERY (plain_operand st) [offv; head; src]` `offv`
       (extbodies_emit_bind `\ptrv st. EVERY (plain_operand st) [ptrv; offv; head; src]` `ptrv`
         (extbodies_emit_bind `\bad st. EVERY (plain_operand st) [bad; ptrv; offv; head; src]` `bad`
           (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; ptrv; offv; head; src]` `ok`
             (extbodies_void_bind `\u st. EVERY (plain_operand st) [ok; bad; ptrv; offv; head; src]`
               (irule shape_step_return >> simp[]))))) >>
     irule shape_step_return >> simp[])
QED

Theorem compile_abi_decode_dyn_elem_ptr_shape:
  !elem src hi sz.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [elem; src; hi])
      (compile_abi_decode_dyn_elem_ptr CALLDATALOAD elem src hi sz)
      (\ptr st. plain_operand st ptr)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  extbodies_emit_bind `\offv st. EVERY (plain_operand st) [offv; elem; src; hi]` `offv`
   (extbodies_emit_bind `\ptrv st. EVERY (plain_operand st) [ptrv; offv; elem; src; hi]` `ptrv`
    (extbodies_emit_bind `\bad st. EVERY (plain_operand st) [bad; ptrv; offv; elem; src; hi]` `bad`
     (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; ptrv; offv; elem; src; hi]` `ok`
      (extbodies_void_bind `\u st. EVERY (plain_operand st) [ok; bad; ptrv; offv; elem; src; hi]`
       (extbodies_emit_bind `\eend st. EVERY (plain_operand st) [eend; ok; bad; ptrv; offv; elem; src; hi]` `eend`
        (extbodies_emit_bind `\oob st. EVERY (plain_operand st) [oob; eend; ok; bad; ptrv; offv; elem; src; hi]` `oob`
         (extbodies_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; eend; ok; bad; ptrv; offv; elem; src; hi]` `ok2`
          (extbodies_void_bind `\u st. EVERY (plain_operand st) [ok2; oob; eend; ok; bad; ptrv; offv; elem; src; hi]`
           (irule shape_step_return >> simp[])))))))))
QED

Theorem compile_abi_decode_static_shape:
  !src dst clamp.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [src; dst])
      (compile_abi_decode_static src dst CALLDATALOAD
        (\v. compile_abi_clamp_basetype v clamp)) (\x st. T)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_abi_decode_static_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. EVERY (plain_operand st) [v; src; dst]` >> conj_tac
  >- (qx_gen_tac `v` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\u st. EVERY (plain_operand st) [v; src; dst] /\ T` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (plain_operand st) [v; src; dst]`,
            `\u st. EVERY (plain_operand st) [v; src; dst]`] >>
          simp_tac bool_ss [] >> ho_match_mp_tac extbodies_emit_void_plain >>
          extbodies_opcode_tac) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [v; src; dst] /\
               EVERY (plain_operand st) [v]`,
        `\u st. EVERY (plain_operand st) [v; src; dst] /\ T`] >>
      simp_tac bool_ss [] >> conj_tac >- simp[] >>
      mp_tac (Q.SPECL [`v`, `clamp`] compile_abi_clamp_basetype_shape) >>
      strip_tac >> drule shape_step_frame >>
      disch_then (qspec_then `\st. EVERY (plain_operand st) [v; src; dst]` mp_tac) >>
      simp[shape_stable_plain_operands]) >>
  ho_match_mp_tac extbodies_emit_plain >> extbodies_opcode_tac
QED


Theorem cenv_decode_operand_plain:
  !st cenv name loc dst.
    cenv_shape_ok st cenv /\ FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst ==> plain_operand st dst
Proof
  rpt strip_tac >>
  `loc_shape_ok st loc` by metis_tac[cenv_shape_ok_def] >>
  Cases_on `loc` >>
  gvs[var_location_decode_operand_def, loc_shape_ok_def, plain_operand_def,
      stackPlanTypesTheory.is_label_operand_def]
QED

Theorem cenv_shape_ok_ptr_update:
  !st cenv name op size.
    cenv_shape_ok st cenv /\ plain_operand st op ==>
    cenv_shape_ok st (cenv with ce_vars := cenv.ce_vars |+ (name, PtrVar op size))
Proof
  rpt strip_tac >>
  gvs[cenv_shape_ok_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `name = n` >> gvs[loc_shape_ok_def] >>
  metis_tac[]
QED

Theorem extbodies_frame:
  !R internal LP P m Q.
    shape_step internal LP P m Q /\ shape_stable R /\
    (!st. R st ==> P st) ==>
    shape_step internal LP R m (\x st. R st /\ Q x st)
Proof
  rpt strip_tac >> irule shape_step_conseq >>
  qexistsl_tac [`LP`, `\st. R st /\ P st`,
    `\x st. R st /\ Q x st`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac shape_step_frame >> simp[]
QED

Theorem extbodies_assume:
  !b internal LP P m Q.
    (b ==> shape_step internal LP P m Q) ==>
    shape_step internal LP (\st. P st /\ b) m Q
Proof
  Cases >> simp[shape_step_def] >> metis_tac[]
QED

Theorem extbodies_emit_inst_void:
  !opc ops. emit_inst opc ops [] = emit_void opc ops
Proof
  simp[emit_inst_def, emit_void_def]
QED

fun extbodies_block_bind post cont =
  irule shape_step_ignore_bind >> qexists_tac post >> conj_tac
  >- (gen_tac >> BETA_TAC >> cont) >>
  ho_match_mp_tac shape_step_new_block >> simp[shape_stable_plain_operands];

fun extbodies_label_bind pre name cont =
  irule shape_step_bind >> qexists_tac pre >> conj_tac
  >- (qx_gen_tac name >> BETA_TAC >> ho_match_mp_tac extbodies_assume >> strip_tac >> cont) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_plain_operands];

Theorem compile_abi_decode_shape:
  (!dst src opc hi info. opc = CALLDATALOAD ==>
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_to_buf dst src opc hi info) (\x st. T)) /\
  (!dst src opc hi elems ao vo. opc = CALLDATALOAD ==>
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_complex_elems dst src opc hi elems ao vo) (\x st. T)) /\
  (!dst src opc hi ei asz msz ip cnt. opc = CALLDATALOAD ==>
    shape_step F compiler_label
      (\st. EVERY (plain_operand st) [dst; src; hi; ip; cnt])
      (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt) (\x st. T))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume compile_abi_decode_shape[prim]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [src; dst]`, `\x st. T`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  irule compile_abi_decode_static_shape
QED

Resume compile_abi_decode_shape[nil]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule shape_step_return >> simp[]
QED

Resume compile_abi_decode_shape[bytes]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM, opcode_case_def] >> BETA_TAC >>
  extbodies_emit_bind `\len st. EVERY (plain_operand st) [len; dst; src; hi]` `len`
   (extbodies_emit_bind `\bad st. EVERY (plain_operand st) [bad; len; dst; src; hi]` `bad`
    (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]` `ok`
     (extbodies_void_bind `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`
      (suspend "bytes_tail"))))
QED
Resume compile_abi_decode_shape[bytes_tail]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`,
        `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`] >>
      simp_tac bool_ss [] >>
      ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac) >>
  suspend "bytes_guard"
QED
Resume compile_abi_decode_shape[bytes_guard]:
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (irule shape_step_return >> simp[]) >>
  extbodies_emit_bind `\start st. EVERY (plain_operand st) [start; ok; bad; len; dst; src; hi]` `start`
   (extbodies_emit_bind `\last st. EVERY (plain_operand st) [last; start; ok; bad; len; dst; src; hi]` `last`
    (extbodies_emit_bind `\oob st. EVERY (plain_operand st) [oob; last; start; ok; bad; len; dst; src; hi]` `oob`
     (extbodies_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]` `ok2`
      (suspend "bytes_assert"))))
QED
Resume compile_abi_decode_shape[bytes_assert]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac
QED
Resume compile_abi_decode_shape[complex]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `!static_sz. _` (qspec_then
    `FOLDR (\(_, a:num, _:num) acc. a + acc) 0 elems` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `!static_sz. _` (qspec_then
    `FOLDR (\(_, a:num, _:num) acc. a + acc) 0 elems` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (first_assum irule >> simp[]) >>
  extbodies_emit_bind `\last st. EVERY (plain_operand st) [last; dst; src; hi]` `last`
   (extbodies_emit_bind `\bad st. EVERY (plain_operand st) [bad; last; dst; src; hi]` `bad`
    (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; last; dst; src; hi]` `ok`
     (extbodies_void_bind `\u st. EVERY (plain_operand st) [ok; bad; last; dst; src; hi]`
      (irule shape_step_conseq >>
       qexistsl_tac [`compiler_label`,
         `\st. EVERY (plain_operand st) [dst; src; hi]`, `\x st. T`] >>
       simp_tac bool_ss [] >> conj_tac >- simp[] >>
       first_assum irule >> simp[]))))
QED
Resume compile_abi_decode_shape[cons]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `compile_getelemptr_abi src dyn ao CALLDATALOAD` >>
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dyn` mp_tac) >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dyn` mp_tac) >>
  simp_tac bool_ss [Abbr `dyn`] >> ntac 2 disch_tac >>
  irule shape_step_bind >>
  qexists_tac `\elem st. EVERY (plain_operand st) [elem; dst; src; hi]` >>
  conj_tac
  >- (qx_gen_tac `elem` >> BETA_TAC >>
      extbodies_emit_bind `\edst st. EVERY (plain_operand st) [edst; elem; dst; src; hi]` `edst`
       (irule shape_step_ignore_bind >>
        qexists_tac `\u st. EVERY (plain_operand st) [edst; elem; dst; src; hi] /\ T` >>
        conj_tac
        >- (gen_tac >> BETA_TAC >>
            irule shape_step_conseq >>
            qexistsl_tac [`compiler_label`,
              `\st. EVERY (plain_operand st) [dst; src; hi]`, `\x st. T`] >>
            simp_tac bool_ss [] >> conj_tac >- simp[] >>
            first_assum irule) >>
        ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
        qexists_tac `\st. EVERY (plain_operand st) [edst; elem; hi]` >>
        conj_tac >- (first_assum irule) >> simp[])) >>
  suspend "cons_ptr"
QED
Resume compile_abi_decode_shape[cons_ptr]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [dst; src; hi]`,
    `\elem st. EVERY (plain_operand st) [dst; src; hi] /\ plain_operand st elem`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  qexists_tac `\st. EVERY (plain_operand st) [src]` >>
  conj_tac >- (irule compile_getelemptr_abi_shape) >> simp[]
QED
Resume compile_abi_decode_shape[array]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM, opcode_case_def] >> BETA_TAC >>
  extbodies_emit_bind `\cnt0 st. EVERY (plain_operand st) [cnt0; dst; src; hi]` `cnt0`
   (suspend "array_clamp")
QED
Resume compile_abi_decode_shape[array_clamp]:
  extbodies_emit_bind `\bad st. EVERY (plain_operand st) [bad; cnt0; dst; src; hi]` `bad`
    (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]` `ok`
     (suspend "array_check"))
QED
Resume compile_abi_decode_shape[array_check]:
  extbodies_void_bind `\u st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]`
      (irule shape_step_ignore_bind >>
       qexists_tac `\u st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]` >>
       conj_tac >- suspend "array_reload" >> suspend "array_guard")
QED
Resume compile_abi_decode_shape[array_guard]:
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (irule shape_step_return >> simp[]) >>
  extbodies_emit_bind `\sz st. EVERY (plain_operand st) [sz; ok; bad; cnt0; dst; src; hi]` `sz`
   (extbodies_emit_bind `\sz1 st. EVERY (plain_operand st) [sz1; sz; ok; bad; cnt0; dst; src; hi]` `sz1`
    (extbodies_emit_bind `\last st. EVERY (plain_operand st) [last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `last`
     (extbodies_emit_bind `\oob st. EVERY (plain_operand st) [oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `oob`
      (extbodies_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `ok2`
       (suspend "array_assert")))))
QED
Resume compile_abi_decode_shape[array_assert]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac
QED
Resume compile_abi_decode_shape[array_reload]:
  gen_tac >> BETA_TAC >>
  extbodies_emit_bind `\cnt st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi]` `cnt`
   (extbodies_void_bind `\u st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi]`
     (suspend "array_choose"))
QED
Resume compile_abi_decode_shape[array_choose]:
  qmatch_goalsub_abbrev_tac `if bulk then _ else _` >>
  Cases_on `bulk` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (extbodies_emit_bind `\sz st. EVERY (plain_operand st) [sz; cnt; ok; bad; cnt0; dst; src; hi]` `sz`
       (extbodies_emit_bind `\sdata st. EVERY (plain_operand st) [sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]` `sdata`
        (extbodies_emit_bind `\ddata st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]` `ddata`
         (suspend "array_copy")))) >>
  irule shape_step_bind >>
  qexists_tac `\buf st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi] /\
                        plain_operand st buf.buf_operand` >>
  conj_tac >- suspend "array_loop" >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >> qexists_tac `\st. T` >>
  simp_tac bool_ss [] >> irule compile_alloc_buffer_shape
QED
Resume compile_abi_decode_shape[array_copy]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]`] >>
  simp_tac bool_ss [] >> ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac
QED
Resume compile_abi_decode_shape[array_loop]:
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [buf.buf_operand; dst; src; hi; cnt]`, `\x st. T`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  extbodies_void_bind `\u st. EVERY (plain_operand st) [buf.buf_operand; dst; src; hi; cnt]`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`,
       `\st. EVERY (plain_operand st) [dst; src; hi; buf.buf_operand; cnt]`, `\x st. T`] >>
     simp_tac bool_ss [] >> conj_tac >- simp[] >>
     first_x_assum (qspecl_then [`F`, `buf.buf_operand`, `buf`, `cnt`] mp_tac) >>
     simp_tac bool_ss [])
QED
Resume compile_abi_decode_shape[loop]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM,
    extbodies_emit_inst_void] >> BETA_TAC >>
  extbodies_label_bind
    `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `hdr`
   (extbodies_label_bind
     `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `bodylbl`
    (extbodies_label_bind
      `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `exit`
     (suspend "loop_jump")))
QED
Resume compile_abi_decode_shape[loop_jump]:
  extbodies_void_bind `\u st. EVERY (plain_operand st) [dst; src; hi; ip; cnt]`
   (extbodies_block_bind `\u st. EVERY (plain_operand st) [dst; src; hi; ip; cnt]`
     (suspend "loop_header"))
QED
Resume compile_abi_decode_shape[loop_header]:
  extbodies_emit_bind `\idx st. EVERY (plain_operand st) [idx; dst; src; hi; ip; cnt]` `idx`
   (extbodies_emit_bind `\n st. EVERY (plain_operand st) [n; idx; dst; src; hi; ip; cnt]` `n`
    (extbodies_emit_bind `\cmp st. EVERY (plain_operand st) [cmp; n; idx; dst; src; hi; ip; cnt]` `cmp`
     (extbodies_emit_bind `\done st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]` `done`
      (suspend "loop_jnz"))))
QED
Resume compile_abi_decode_shape[loop_jnz]:
  extbodies_void_bind `\u st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]`
    (extbodies_block_bind `\u st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]`
      (suspend "loop_body")) >>
  rpt strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_abi_decode_shape[loop_body]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) [dst; src; hi; ip]`,
    `\x st. T`] >> simp_tac bool_ss [] >> conj_tac >- simp[] >>
  extbodies_emit_bind `\idx2 st. EVERY (plain_operand st) [idx2; dst; src; hi; ip]` `idx2`
   (extbodies_emit_bind `\sdata st. EVERY (plain_operand st) [sdata; idx2; dst; src; hi; ip]` `sdata`
    (suspend "loop_source"))
QED
Resume compile_abi_decode_shape[loop_source]:
  extbodies_emit_bind `\soff st. EVERY (plain_operand st) [soff; sdata; idx2; dst; src; hi; ip]` `soff`
   (extbodies_emit_bind `\esrc st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip]` `esrc`
    (irule shape_step_bind >>
     qexists_tac `\actual st. EVERY (plain_operand st) [actual; idx2; dst; hi; ip]` >>
     conj_tac >- suspend "loop_dest" >> suspend "loop_actual"))
QED
Resume compile_abi_decode_shape[loop_actual]:
  qmatch_goalsub_abbrev_tac `if dyn then _ else _` >>
  Cases_on `dyn` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip]`,
        `\actual st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip] /\ plain_operand st actual`] >>
      simp_tac bool_ss [] >> conj_tac >- simp[] >>
      ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
      qexists_tac `\st. EVERY (plain_operand st) [esrc; sdata; hi]` >>
      conj_tac >- (irule compile_abi_decode_dyn_elem_ptr_shape) >> simp[]) >>
  irule shape_step_return >> simp[]
QED
Resume compile_abi_decode_shape[loop_dest]:
  qx_gen_tac `actual` >> BETA_TAC >>
  extbodies_emit_bind `\ddata st. EVERY (plain_operand st) [ddata; actual; idx2; dst; hi; ip]` `ddata`
   (extbodies_emit_bind `\doff st. EVERY (plain_operand st) [doff; ddata; actual; idx2; dst; hi; ip]` `doff`
    (extbodies_emit_bind `\edst st. EVERY (plain_operand st) [edst; doff; ddata; actual; idx2; dst; hi; ip]` `edst`
     (irule shape_step_ignore_bind >>
      qexists_tac `\u st. EVERY (plain_operand st) [edst; doff; ddata; actual; idx2; dst; hi; ip] /\ T` >>
      conj_tac >- suspend "loop_end" >> suspend "loop_recurse")))
QED
Resume compile_abi_decode_shape[loop_recurse]:
  qpat_x_assum `!dyn dst src. _` (qspec_then
    `case ei of DecPrimWord _ => F | DecBytestring _ => T |
     DecDynArray _ _ _ _ _ => T | DecComplex T _ => T | DecComplex F _ => F` mp_tac) >>
  disch_then assume_tac >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  qexists_tac `\st. EVERY (plain_operand st) [edst; actual; hi]` >>
  conj_tac >- (first_assum irule >> simp_tac bool_ss []) >> simp[]
QED
Resume compile_abi_decode_shape[loop_end]:
  gen_tac >> BETA_TAC >> simp_tac bool_ss [] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) [idx2; ip]`,
    `\x st. T`] >> simp_tac bool_ss [] >> conj_tac >- simp[] >>
  extbodies_emit_bind `\next st. EVERY (plain_operand st) [next; idx2; ip]` `next`
   (extbodies_void_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
    (extbodies_void_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
     (extbodies_block_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
      (irule shape_step_return >> simp[]))))
QED
Finalise compile_abi_decode_shape

(* Each body opens its "fn_" entry block, then compile_guarded_body via
   compile_stmt_shape with ce_return_pc = NONE. *)
Theorem extbodies_cenv_frame:
  !internal LP cenv P m Q.
    shape_step internal LP P m Q ==>
    shape_step internal LP (\st. cenv_shape_ok st cenv /\ P st) m
      (\x st. cenv_shape_ok st cenv /\ Q x st)
Proof
  rpt strip_tac >> ho_match_mp_tac shape_step_frame >>
  simp[cenv_shape_ok_stable]
QED

fun extbodies_cenv_emit_bind live name cont =
  irule shape_step_bind >>
  qexists_tac (`\x st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) (x::` @ live @ `)`) >>
  conj_tac >- (qx_gen_tac name >> BETA_TAC >> cont) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) ` @ live,
    `\x st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) (x::` @ live @ `)`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_emit_plain >> extbodies_opcode_tac;

val extbodies_args_decode_tail_tac =
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> simp_tac bool_ss [] >> first_x_assum irule) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; src; Lit 0w]`,
    `\u st. cenv_shape_ok st cenv /\ T`] >>
  conj_tac >- simp[] >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule_all cenv_decode_operand_plain >>
      simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
      gvs[plain_operand_def]) >>
  conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >> simp[compile_abi_decode_shape];

Theorem compile_decode_args_shape:
  !args cenv offset base_adj.
    shape_step F compiler_label (\st. cenv_shape_ok st cenv)
      (compile_decode_args cenv args offset CALLDATALOAD (Lit 0w) base_adj)
      (\x st. T)
Proof
  Induct >> rpt gen_tac
  >- (pure_rewrite_tac[compile_decode_args_def] >>
      irule shape_step_return >> simp[]) >>
  PairCases_on `h` >>
  pure_rewrite_tac[compile_decode_args_def, LET_THM] >> BETA_TAC >>
  Cases_on `h1` >> pure_rewrite_tac[COND_CLAUSES]
  >- suspend "primitive" >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `var_location_decode_operand loc = SOME dst` >>
  Cases_on `h2` >> pure_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- suspend "dynamic" >>
  extbodies_cenv_emit_bind `[]` `src` (suspend "static_decode")
QED
Resume compile_decode_args_shape[dynamic]:
  extbodies_cenv_emit_bind `[]` `head`
    (extbodies_cenv_emit_bind `[head]` `offv`
      (extbodies_cenv_emit_bind `[offv; head]` `src` extbodies_args_decode_tail_tac))
QED
Resume compile_decode_args_shape[static_decode]:
  extbodies_args_decode_tail_tac
QED
Resume compile_decode_args_shape[primitive]:
  extbodies_cenv_emit_bind `[]` `src`
    (extbodies_cenv_emit_bind `[src]` `v` (suspend "clamp"))
QED
Resume compile_decode_args_shape[clamp]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ (EVERY (plain_operand st) [v] /\ T)` >>
  conj_tac >- suspend "store" >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [v]`,
    `\u st. cenv_shape_ok st cenv /\ (EVERY (plain_operand st) [v] /\ T)`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_frame >> qexists_tac `\st. EVERY (plain_operand st) [v]` >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  irule compile_abi_clamp_basetype_shape
QED
Resume compile_decode_args_shape[store]:
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. cenv_shape_ok st cenv` >>
  conj_tac >- (gen_tac >> BETA_TAC >> first_x_assum irule) >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `var_location_decode_operand loc = SOME dst` >>
  suspend "mstore"
QED
Resume compile_decode_args_shape[mstore]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; v]`,
    `\u st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; v]`] >>
  conj_tac >- simp[] >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule_all cenv_decode_operand_plain >> simp[] >> gvs[]) >>
  conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac
QED
Finalise compile_decode_args_shape

Theorem compile_register_positional_args_shape:
  !args cenv offset.
    shape_step F compiler_label (\st. cenv_shape_ok st cenv)
      (compile_register_positional_args cenv args offset)
      (\cenv' st. cenv_shape_ok st cenv' /\ cenv'.ce_return_pc = cenv.ce_return_pc)
Proof
  Induct >> rpt gen_tac
  >- (pure_rewrite_tac[compile_register_positional_args_def] >>
      irule shape_step_return >> simp[]) >>
  PairCases_on `h` >> pure_rewrite_tac[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `var_location_memory_size loc = SOME sz` >>
  irule shape_step_bind >>
  qexists_tac `\buf st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand` >>
  conj_tac >- suspend "allocated" >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ T`,
    `\buf st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >> irule compile_alloc_buffer_shape
QED
Resume compile_register_positional_args_shape[allocated]:
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\ce st. ce = (cenv with ce_vars updated_by
    (\m. m |+ (h0, PtrVar buf.buf_operand sz))) /\ cenv_shape_ok st ce` >>
  conj_tac >- suspend "registered" >>
  irule shape_step_return >> simp[] >> rpt strip_tac >>
  `cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar buf.buf_operand sz)) =
   cenv with ce_vars := cenv.ce_vars |+ (h0, PtrVar buf.buf_operand sz)`
    by simp[compile_env_component_equality] >>
  asm_rewrite_tac[] >> irule cenv_shape_ok_ptr_update >> simp[]
QED
Resume compile_register_positional_args_shape[registered]:
  qx_gen_tac `ce` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st ce /\
      ce = (cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar buf.buf_operand sz)))`,
    `\cenv' st. cenv_shape_ok st cenv' /\ cenv'.ce_return_pc = cenv.ce_return_pc`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_assume >> strip_tac >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. cenv_shape_ok st ce /\ T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st ce`,
        `\cenv' st. cenv_shape_ok st cenv' /\ cenv'.ce_return_pc = ce.ce_return_pc`] >>
      conj_tac >- (gvs[]) >> conj_tac >- simp[] >> conj_tac >- simp[] >>
      first_x_assum irule) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st ce /\ cenv_shape_ok st ce`,
    `\u st. cenv_shape_ok st ce /\ T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >> irule compile_decode_args_shape
QED
Finalise compile_register_positional_args_shape

fun extbodies_void_end live =
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) ` @ live,
    `\u st. EVERY (plain_operand st) ` @ live] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_emit_void_plain >> extbodies_opcode_tac;

val extbodies_from_true_tac =
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) []`, `\u st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[];

Theorem compile_entry_checks_shape:
  !min_cds payable. shape_step F compiler_label (\st. T)
    (compile_entry_checks min_cds payable) (\x st. T)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_entry_checks_def] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> Cases_on `min_cds > 4` >>
      pure_asm_rewrite_tac[COND_CLAUSES]
      >- (extbodies_from_true_tac >>
          extbodies_emit_bind `\cds st. EVERY (plain_operand st) [cds]` `cds`
            (extbodies_emit_bind `\enough st. EVERY (plain_operand st) [enough; cds]` `enough`
              (extbodies_emit_bind `\ok st. EVERY (plain_operand st) [ok; enough; cds]` `ok`
                (extbodies_void_end `[ok; enough; cds]`)))) >>
      irule shape_step_return >> simp[]) >>
  Cases_on `payable` >> pure_rewrite_tac[NOT_CLAUSES, COND_CLAUSES]
  >- (irule shape_step_return >> simp[]) >>
  extbodies_from_true_tac >>
  extbodies_emit_bind `\cv st. EVERY (plain_operand st) [cv]` `cv`
    (extbodies_emit_bind `\nv st. EVERY (plain_operand st) [nv; cv]` `nv`
      (extbodies_void_end `[nv; cv]`))
QED



Theorem compile_guarded_body_env_shape:
  !cenv nr nkey transient view body ret_type.
    cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label (\st. cenv_shape_ok st cenv)
      (compile_guarded_body cenv nr nkey transient view body ret_type) (\x st. T)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_guarded_body_def] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. cenv_shape_ok st cenv /\ T` >>
  conj_tac >- suspend "statements" >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ T`,
    `\u st. cenv_shape_ok st cenv /\ T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >> Cases_on `nr` >> pure_rewrite_tac[COND_CLAUSES]
  >- (irule compile_nonreentrant_lock_shape) >> irule shape_step_return >> simp[]
QED
Resume compile_guarded_body_env_shape[statements]:
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >>
  conj_tac >- suspend "termination" >>
  rename1 `~supported_stmts_expr_exists expr_shape_root body_stmts` >>
  mp_tac (Q.SPECL [`cenv`, `NoLoop`,
    `case ret_type of SOME t => t | NONE => BaseT BoolT`, `body_stmts`] (cj 2 compile_stmt_shape)) >>
  simp[loop_ctx_shape_ok_def] >>
  disch_then (fn th => irule shape_step_conseq >>
    qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv`, `\u st. T`] >>
    simp_tac bool_ss [] >> ACCEPT_TAC th)
QED
Resume compile_guarded_body_env_shape[termination]:
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\cs st. cs = st /\ T` >> conj_tac
  >- (qx_gen_tac `cs` >> BETA_TAC >> Cases_on `block_is_terminated cs` >>
      pure_asm_rewrite_tac[COND_CLAUSES]
      >- (irule shape_step_return >> simp[]) >>
      suspend "epilogue") >>
  qspec_then `\st. T` mp_tac (Q.SPECL [`F`, `compiler_label`] shape_step_comp_get) >>
  simp[]
QED
Resume compile_guarded_body_env_shape[epilogue]:
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (let
        fun terminal opc =
          pure_rewrite_tac[optionTheory.option_case_def, extbodies_emit_inst_void] >>
          mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`, opc, `[]`]
            shape_step_emit_void) >> simp[] >> disch_then irule >>
          extbodies_opcode_tac >> simp[shape_stable_def]
      in
        gen_tac >> BETA_TAC >> Cases_on `ret_type`
        >- terminal `STOP` >> terminal `INVALID`
      end) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  Cases_on `nr` >> pure_rewrite_tac[COND_CLAUSES]
  >- (irule compile_nonreentrant_unlock_shape) >> irule shape_step_return >> simp[]
QED
Finalise compile_guarded_body_env_shape

Theorem compile_external_function_body_shape:
  !cenv args nr nkey transient view body ret_type.
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label (\st. T)
      (compile_external_function_body cenv args nr nkey transient view body ret_type)
      (\x st. T)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_external_function_body_def] >>
  irule shape_step_bind >>
  qexists_tac `\ce st. cenv_shape_ok st ce /\ ce.ce_return_pc = cenv.ce_return_pc` >>
  conj_tac
  >- (qx_gen_tac `ce` >> BETA_TAC >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. cenv_shape_ok st ce /\ ce.ce_return_pc = NONE`, `\u st. T`] >>
      conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
      ho_match_mp_tac extbodies_assume >> strip_tac >>
      irule compile_guarded_body_env_shape >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv`,
    `\ce st. cenv_shape_ok st ce /\ ce.ce_return_pc = cenv.ce_return_pc`] >>
  conj_tac >- simp[] >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> irule cenv_static_ok_shape_ok >> simp[]) >>
  conj_tac >- simp[] >> irule compile_register_positional_args_shape
QED

Theorem compile_external_fn_bodies_shape:
  !fns.
    EVERY external_fn_shape_ok fns ==>
    shape_step F jump_label_ok (\st. T) (compile_external_fn_bodies fns)
      (\x st. T)
Proof
  Induct >> simp_tac std_ss [listTheory.EVERY_DEF]
  >- (pure_rewrite_tac[compile_external_fn_bodies_def] >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  pure_rewrite_tac[external_fn_shape_ok_def] >> strip_tac >>
  pure_rewrite_tac[compile_external_fn_bodies_def] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
          >- (gen_tac >> BETA_TAC >> first_x_assum irule >> simp[]) >>
          suspend "body") >>
      suspend "checks") >>
  ho_match_mp_tac shape_step_new_block >>
  simp[shape_stable_def, jump_label_ok_def]
QED
Resume compile_external_fn_bodies_shape[body]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[jump_label_ok_def] >>
  irule compile_external_function_body_shape >> simp[]
QED
Resume compile_external_fn_bodies_shape[checks]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[jump_label_ok_def] >>
  irule compile_entry_checks_shape
QED
Finalise compile_external_fn_bodies_shape

Theorem compile_guarded_body_shape:
  !cenv is_nr nkey use_trans is_view body ret_type.
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label (\st. T)
      (compile_guarded_body cenv is_nr nkey use_trans is_view body ret_type)
      (\x st. T)
Proof
  rpt strip_tac >> rename1 `~supported_stmts_expr_exists _ ss` >>
  simp[compile_guarded_body_def] >>
  irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
  reverse conj_tac
  >- (Cases_on `is_nr` >>
      simp[compile_nonreentrant_lock_shape, shape_step_return]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
  reverse conj_tac
  >- (qmatch_goalsub_abbrev_tac `compile_stmts cenv NoLoop ty ss` >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. cenv_shape_ok st cenv /\ loop_ctx_shape_ok NoLoop`,
        `\x st. T`] >>
      conj_tac >- simp[] >>
      conj_tac >- simp[loop_ctx_shape_ok_def, cenv_static_ok_shape_ok] >>
      conj_tac >- simp[] >>
      mp_tac (Q.SPECL [`cenv`, `NoLoop`, `ty`, `ss`]
        (cj 2 compile_stmt_shape)) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\x st. x = st /\ T` >> reverse conj_tac
  >- (irule (BETA_RULE (Q.SPECL [`F`, `compiler_label`, `\st. T`]
        shape_step_comp_get))) >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
  reverse conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. T`, `\x st. T`] >>
      simp[] >> Cases_on `is_nr` >>
      simp[compile_nonreentrant_unlock_shape, shape_step_return]) >>
  gen_tac >> BETA_TAC >> Cases_on `ret_type` >> simp[] >>
  (pure_rewrite_tac[emit_inst_def, GSYM emit_void_def] >>
   irule shape_step_emit_void_pre >>
   simp[lowered_inst_ok_def, raw_opcode_ok_def,
        inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
        inst_jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
        mk_inst_def])
QED

Theorem compile_fallback_body_shape:
  !cenv is_payable is_nr nkey use_trans is_view body ret_type.
    fallback_shape_ok
      (SOME (cenv, is_payable, is_nr, nkey, use_trans, is_view, body,
             ret_type)) ==>
    shape_step F compiler_label (\st. T)
      (compile_fallback_body cenv is_payable is_nr nkey use_trans is_view
         body ret_type) (\x st. T)
Proof
  let
    val inst_simp = simp[label_or_plain_def, plain_operand_def,
      lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
      label_positions_ok_def, is_read0_opcode_def, inst_jump_labels_ok_def,
      is_terminator_def, is_param_opcode_def, mk_inst_def,
      stackPlanTypesTheory.is_label_operand_def]
  in
    rpt gen_tac >> simp[fallback_shape_ok_def] >> strip_tac >>
    simp[compile_fallback_body_def] >>
    irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
    reverse conj_tac
    >- (Cases_on `is_payable` >> simp[shape_step_return] >>
        ntac 2
          (irule shape_step_bind >>
           qexists_tac `\x st. plain_operand st x` >>
           reverse conj_tac
           >- (irule shape_step_emit_op_pre >> inst_simp) >>
           gen_tac >> BETA_TAC) >>
        irule shape_step_emit_void_pre >> inst_simp) >>
    gen_tac >> BETA_TAC >> irule compile_guarded_body_shape >> simp[]
  end
QED

Theorem captured_params_shape_stable[local]:
  !captured. shape_stable
    (\st. EVERY (\(name,is_stack,op). plain_operand st op) captured)
Proof
  rw[shape_stable_def, EVERY_MEM] >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >>
  strip_tac >> drule_all plain_operand_mono >> simp[]
QED

Theorem compile_internal_param_decls_shape[local]:
  !params idx.
    shape_step T compiler_label (\st. T)
      (compile_internal_param_decls params idx)
      (\r st. EVERY (\(name,is_stack,op). plain_operand st op) (FST r))
Proof
  Induct_on `params`
  >- (gen_tac >> simp[compile_internal_param_decls_def] >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  irule shape_step_bind >>
  qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `PARAM`,
          `[Lit (n2w idx)]`] shape_step_emit_op) >>
      simp[shape_stable_def, label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
           is_read0_opcode_def, label_positions_ok_def, is_terminator_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\r st. plain_operand st x /\
    EVERY (\(name,is_stack,op). plain_operand st op) (FST r)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  first_x_assum (qspec_then `idx + 1` assume_tac) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. plain_operand st x` mp_tac) >>
  simp[] >> disch_then irule >>
  rw[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Theorem cenv_shape_ok_var_update[local]:
  !st cenv op name sz.
    cenv_shape_ok st cenv /\ plain_operand st op ==>
    cenv_shape_ok st
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar op sz)))
Proof
  rw[cenv_shape_ok_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[loc_shape_ok_def] >>
  Cases_on `name = n` >> gvs[loc_shape_ok_def] >> metis_tac[]
QED

Theorem materialize_internal_params_shape:
  !captured cenv.
    shape_step T compiler_label
      (\st. cenv_shape_ok st cenv /\
        EVERY (\(name,is_stack,op). plain_operand st op) captured)
      (materialize_internal_params cenv captured)
      (\cenv' st. cenv_shape_ok st cenv' /\
                  cenv'.ce_return_pc = cenv.ce_return_pc)
Proof
  Induct_on `captured`
  >- (gen_tac >> simp[materialize_internal_params_def] >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- suspend "stack"
  >> first_x_assum (qspec_then
       `cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar h2
         (case FLOOKUP cenv.ce_vars h0 of SOME (MemLoc _ sz) => sz | _ => 0)))`
       mp_tac) >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[cenv_shape_ok_var_update] >>
  disch_then irule >> irule cenv_shape_ok_var_update >> simp[]
QED

Resume materialize_internal_params_shape[stack]:
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (first_x_assum (qspec_then `cenv` mp_tac) >>
      simp[shape_step_def] >> metis_tac[]) >>
  Cases_on `x` >> simp[]
  >~ [`emit_op ALLOCA _`] >- suspend "allocate" >>
  first_x_assum (qspec_then `cenv` mp_tac) >>
  simp[shape_step_def] >> metis_tac[]
QED
Resume materialize_internal_params_shape[allocate]:
  rename1 `emit_op ALLOCA [Lit (n2w sz)]` >>
  irule shape_step_bind >>
  qexists_tac `\ptr st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    plain_operand st ptr` >> reverse conj_tac
  >- suspend "alloc_rule" >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    plain_operand st x` >> reverse conj_tac
  >- suspend "store_rule" >>
  gen_tac >> BETA_TAC >>
  first_x_assum (qspec_then
    `cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar x sz))` mp_tac) >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[cenv_shape_ok_var_update] >>
  disch_then irule >> irule cenv_shape_ok_var_update >> simp[]
QED
Resume materialize_internal_params_shape[alloc_rule]:
  `shape_stable (\st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
       EVERY (\(name,is_stack,op). plain_operand st op) captured)` by
    (ho_match_mp_tac shape_stable_conj >> conj_tac
     >- simp[cenv_shape_ok_stable] >>
     ho_match_mp_tac shape_stable_conj >> conj_tac
     >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
     simp[captured_params_shape_stable]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`,
    `\st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
       EVERY (\(name,is_stack,op). plain_operand st op)
         (captured:(string # bool # operand) list)`,
    `ALLOCA`, `[Lit (n2w sz)]`] shape_step_emit_op) >>
  simp[GSYM CONJ_ASSOC, label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def]
QED
Resume materialize_internal_params_shape[store_rule]:
  `shape_stable (\st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
       EVERY (\(name,is_stack,op). plain_operand st op) captured /\
       plain_operand st x)` by
    (ho_match_mp_tac shape_stable_conj >> conj_tac
     >- simp[cenv_shape_ok_stable] >>
     ho_match_mp_tac shape_stable_conj >> conj_tac
     >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
     ho_match_mp_tac shape_stable_conj >> conj_tac
     >- simp[captured_params_shape_stable] >>
     rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`,
    `\st. cenv_shape_ok st cenv /\ plain_operand st h2 /\
       EVERY (\(name,is_stack,op). plain_operand st op)
         (captured:(string # bool # operand) list) /\ plain_operand st x`,
    `MSTORE`, `[x:operand; h2]`] shape_step_emit_void) >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
    inst_shape_ok_def, inst_jump_labels_ok_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def] >>
  simp[shape_step_def, label_or_plain_def] >> rpt strip_tac >>
  `~is_label_operand x /\ ~is_label_operand h2` by
    (conj_tac
     >- (qpat_x_assum `plain_operand st x` mp_tac >>
         simp[plain_operand_def]) >>
     qpat_x_assum `plain_operand st h2` mp_tac >> simp[plain_operand_def]) >>
  first_x_assum drule_all >> simp[]
QED
Finalise materialize_internal_params_shape[local]

Theorem compile_alloc_buffer_shape_triv[local]:
  !size. shape_step T compiler_label (\st. T)
    (compile_alloc_buffer size) (\x st. T)
Proof
  qx_gen_tac `sz` >> simp[compile_alloc_buffer_def] >> irule shape_step_bind >>
  qexists_tac `\op st. plain_operand st op` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `ALLOCA`,
    `[Lit (n2w sz)]`] shape_step_emit_op) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def]
QED


Theorem compile_alloc_buffer_with_id_shape[local]:
  !sz. shape_step T compiler_label (\st. T)
    (compile_alloc_buffer_with_id sz) (\x st. T)
Proof
  gen_tac >> simp[compile_alloc_buffer_with_id_def] >>
  irule shape_step_bind >> qexists_tac `\id st. T` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_id >> simp[shape_stable_def]) >>
  qx_gen_tac `id` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\out st. plain_operand st (Var out)` >> reverse conj_tac
  >- (mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`]
        shape_step_fresh_var) >> simp[shape_stable_def]) >>
  qx_gen_tac `out` >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`,
    `mk_inst id ALLOCA [Lit (n2w sz)] [out]`] shape_step_emit) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def] >>
  simp[shape_step_def] >> metis_tac[]
QED

(* Side conditions of the single emissions in internal-function code. *)
val intfn_emit_simps =
  [shape_stable_def, label_or_plain_def, plain_operand_def,
   stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
   mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
   is_read0_opcode_def, label_positions_ok_def, is_terminator_def];


Theorem internal_cenv_install_shape[local]:
  !cenv rb pc st.
    cenv_static_ok cenv /\
    (case rb of NONE => T | SOME op => plain_operand st op) /\
    retpc_operand st pc ==>
    cenv_shape_ok st
      (cenv with <|ce_return_buf :=
        (case (rb,cenv.ce_return_buf) of
          (SOME op,SOME (MemLoc off sz)) => SOME (PtrVar op sz)
        | _ => cenv.ce_return_buf);
        ce_return_pc := SOME (PtrVar pc 0)|>)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv_shape_ok st cenv` by metis_tac[cenv_static_ok_shape_ok] >>
  Cases_on `rb` >> gvs[cenv_shape_ok_def] >>
  Cases_on `cenv.ce_return_buf` >> gvs[]
  >- (first_assum MATCH_ACCEPT_TAC) >>
  rename1 `cenv.ce_return_buf = SOME loc` >>
  `?off sz. loc = MemLoc off sz` by metis_tac[cenv_static_ok_def] >>
  gvs[cenv_shape_ok_def, loc_shape_ok_def] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem internal_fallthrough_shape[local]:
  !pc ret_type is_nr nkey use_trans is_view.
    shape_step T compiler_label (\st. retpc_operand st pc)
      (do (if is_nr then compile_nonreentrant_unlock nkey use_trans is_view
           else return ());
          (case ret_type of NONE => emit_inst RET [pc] []
           | SOME _ => emit_inst INVALID [] []) od) (\x st. T)
Proof
  rpt gen_tac >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. retpc_operand st pc` >> reverse conj_tac
  >- (reverse (Cases_on `is_nr`) >> simp[]
      >- (irule shape_step_return >> simp[]) >>
      qspecl_then [`T`, `compiler_label`, `nkey`, `use_trans`, `is_view`]
        assume_tac compile_nonreentrant_unlock_shape >>
      drule shape_step_frame >>
      disch_then (qspec_then `\st. retpc_operand st pc` mp_tac) >>
      simp[shape_stable_def] >> metis_tac[retpc_operand_mono]) >>
  gen_tac >> BETA_TAC >> Cases_on `ret_type` >> simp[]
  >- (mp_tac (Q.SPECL [`compiler_label`, `\st. T`, `[]`, `pc`]
        shape_step_emit_inst_ret) >>
      Cases_on `pc` >> simp intfn_emit_simps >>
      rewrite_tac[shape_step_def, retpc_operand_def] >>
      simp[] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `INVALID`, `[]`, `[]`]
    shape_step_emit_inst) >>
  simp intfn_emit_simps >> rewrite_tac[shape_step_def] >> metis_tac[]
QED

Theorem internal_body_finish_shape[local]:
  !cenv pc body ret_type is_nr nkey use_trans is_view.
    IS_SOME cenv.ce_return_pc /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step T compiler_label
      (\st. retpc_operand st pc /\ cenv_shape_ok st cenv)
      (do compile_stmts cenv NoLoop
            (case ret_type of SOME t => t | NONE => BaseT BoolT) body;
          cs <- comp_get;
          if block_is_terminated cs then return ()
          else do (if is_nr then
                     compile_nonreentrant_unlock nkey use_trans is_view
                   else return ());
                  (case ret_type of NONE => emit_inst RET [pc] []
                   | SOME _ => emit_inst INVALID [] []) od
       od) (\x st. T)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. retpc_operand st pc` >> reverse conj_tac
  >- (qspecl_then [`cenv`, `NoLoop`,
        `case ret_type of SOME t => t | NONE => BaseT BoolT`, `ss`]
        mp_tac (cj 2 compile_stmt_shape) >>
      simp[loop_ctx_shape_ok_def] >> strip_tac >>
      drule shape_step_frame >>
      disch_then (qspec_then `\st. retpc_operand st pc` mp_tac) >>
      simp[shape_stable_def] >> metis_tac[retpc_operand_mono]) >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\cs st. retpc_operand st pc` >> conj_tac
  >- (qx_gen_tac `cs` >> BETA_TAC >> Cases_on `block_is_terminated cs` >> simp[]
      >- (irule shape_step_return >> simp[]) >>
      irule internal_fallthrough_shape) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. retpc_operand st pc`]
    shape_step_comp_get) >>
  rewrite_tac[shape_step_def] >> metis_tac[]
QED

Theorem internal_comp_bind_return[local]:
  comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem internal_alloc_body_suffix_shape:
  !cenv cenv2 pc ret_type is_ctor imm_len is_nr nkey use_trans is_view ss.
    IS_SOME cenv2.ce_return_pc /\
    ~supported_stmts_expr_exists expr_shape_root ss ==>
    shape_step T compiler_label
      (\st. retpc_operand st pc /\ cenv_shape_ok st cenv2)
      (do forced_alloc_id <-
            (do (case ret_type of
                   SOME ret_ty =>
                     if cenv.ce_returns_count > 0 then
                       do compile_alloc_buffer (type_memory_bytes cenv ret_ty);
                          return () od
                     else return ()
                 | NONE => return ());
                forced <-
                  (if is_ctor /\ imm_len > 0 then
                     do alloc_result <- compile_alloc_buffer_with_id imm_len;
                        emit_op MLOAD
                          [Lit (n2w (if imm_len > 32 then imm_len - 32 else 0))];
                        return (SOME (FST alloc_result)) od
                   else return NONE);
                (if is_nr then compile_nonreentrant_lock nkey use_trans is_view
                 else return ());
                return forced od);
          (do compile_stmts cenv2 NoLoop
                (case ret_type of SOME t => t | NONE => BaseT BoolT) ss;
              cs <- comp_get;
              if block_is_terminated cs then return ()
              else do (if is_nr then
                         compile_nonreentrant_unlock nkey use_trans is_view
                       else return ());
                      (case ret_type of NONE => emit_inst RET [pc] []
                       | SOME _ => emit_inst INVALID [] []) od od);
          return forced_alloc_id od) (\x st. T)
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `comp_bind prefix _` >>
  `shape_step T compiler_label (\st. T) prefix (\x st. T)` by
    (unabbrev_all_tac >> suspend "prefix") >>
  drule shape_step_frame >>
  disch_then (qspec_then
    `\st. retpc_operand st pc /\ cenv_shape_ok st cenv2` mp_tac) >>
  impl_tac
  >- (ho_match_mp_tac shape_stable_conj >>
      simp[cenv_shape_ok_stable, shape_stable_def] >>
      metis_tac[retpc_operand_mono]) >>
  simp[] >> strip_tac >> irule shape_step_bind >>
  qexists_tac `\x st. retpc_operand st pc /\ cenv_shape_ok st cenv2` >>
  reverse conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule internal_body_finish_shape >> simp[]
QED
Resume internal_alloc_body_suffix_shape[prefix]:
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> reverse conj_tac
  >- (Cases_on `ret_type` >> simp[]
      >- (irule shape_step_return >> simp[]) >>
      Cases_on `cenv.ce_returns_count > 0` >> simp[]
      >- (irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          irule compile_alloc_buffer_shape_triv) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\id st. T` >> reverse conj_tac
  >- (Cases_on `is_ctor /\ imm_len > 0` >> simp[]
      >- (irule shape_step_bind >> qexists_tac `\r st. T` >> reverse conj_tac
          >- (irule compile_alloc_buffer_with_id_shape) >>
          gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
          qexists_tac `\u st. T` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `MLOAD`,
            `[Lit (n2w (if imm_len > 32 then imm_len - 32 else 0))]`]
            shape_step_emit_op) >>
          simp intfn_emit_simps >> rewrite_tac[shape_step_def] >> metis_tac[]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  Cases_on `is_nr` >> simp[]
  >- (irule compile_nonreentrant_lock_shape) >>
  irule shape_step_return >> simp[]
QED
Finalise internal_alloc_body_suffix_shape[local]

(* The PARAM/RETPC_PARAM prologue, then the body via compile_stmt_shape with
   ce_return_pc = SOME (PtrVar return_pc 0), so internal = T. *)
Theorem compile_internal_function_shape:
  !cenv params has_ret_buf is_nr nkey use_trans is_view is_ctor imm_len body
   ret_type.
    cenv_static_ok cenv /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step T compiler_label (\st. T)
      (compile_internal_function cenv params has_ret_buf is_nr nkey
         use_trans is_view is_ctor imm_len body ret_type) (\x st. T)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  simp[Once compile_internal_function_def, internal_comp_bind_return] >>
  irule shape_step_bind >>
  qexists_tac `\rb st. case rb of NONE => T | SOME op => plain_operand st op` >>
  reverse conj_tac
  >- (reverse (Cases_on `has_ret_buf`) >> simp[]
      >- (irule shape_step_return >> simp[]) >>
      irule shape_step_bind >>
      qexists_tac `\op st. plain_operand st op` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `PARAM`, `[Lit 0w]`]
        shape_step_emit_op) >> simp intfn_emit_simps) >>
  qx_gen_tac `rb` >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac
    `\r st. (case rb of NONE => T | SOME op => plain_operand st op) /\
       EVERY (\(name,is_stack,op). plain_operand st op) (FST r)` >>
  reverse conj_tac
  >- (qspecl_then [`params`, `if has_ret_buf then 1 else 0`] assume_tac
        compile_internal_param_decls_shape >>
      drule shape_step_frame >> disch_then (qspec_then
        `\st. case rb of NONE => T | SOME op => plain_operand st op` mp_tac) >>
      simp[] >> impl_tac
      >- (Cases_on `rb` >> simp[shape_stable_def] >>
          metis_tac[plain_operand_mono]) >> simp[]) >>
  qx_gen_tac `r` >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac
    `\pc st. ((case rb of NONE => T | SOME op => plain_operand st op) /\
       EVERY (\(name,is_stack,op). plain_operand st op) (FST r)) /\
       retpc_operand st pc` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_emit_op_retpc >>
      ho_match_mp_tac shape_stable_conj >> conj_tac
      >- (Cases_on `rb` >> simp[shape_stable_def] >>
          metis_tac[plain_operand_mono]) >>
      simp[shape_stable_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `pc` >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `materialize_internal_params cenv1 _` >>
  irule shape_step_bind >> qexists_tac
    `\cenv2 st. retpc_operand st pc /\ cenv_shape_ok st cenv2 /\
       cenv2.ce_return_pc = SOME (PtrVar pc 0)` >> reverse conj_tac
  >- suspend "materialize"
  >> qx_gen_tac `cenv2` >> BETA_TAC >> suspend "suffix"
QED
Resume compile_internal_function_shape[materialize]:
  qspecl_then [`FST r`, `cenv1`] assume_tac materialize_internal_params_shape >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. retpc_operand st pc` mp_tac) >>
  impl_tac
  >- (simp[shape_stable_def] >> metis_tac[retpc_operand_mono]) >>
  strip_tac >> irule shape_step_conseq >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- simp[Abbr `cenv1`] >>
  rpt strip_tac >> simp[] >>
  mp_tac (Q.SPECL [`cenv`, `rb`, `pc`, `st`] internal_cenv_install_shape) >>
  simp[Abbr `cenv1`]
QED
Theorem cenv_shape_ok_alloca_locals[local]:
  cenv_shape_ok st (cenv with ce_alloca_locals := enabled) =
  cenv_shape_ok st cenv
Proof
  simp[cenv_shape_ok_def]
QED

Resume compile_internal_function_shape[suffix]:
  Cases_on `cenv2.ce_return_pc = SOME (PtrVar pc 0)`
  >- (simp[comp_ignore_bind_def] >> irule shape_step_conseq >>
      irule_at Any (SRULE [comp_ignore_bind_def, comp_bind_assoc,
        internal_comp_bind_return, cenv_shape_ok_alloca_locals]
        (Q.SPECL [`cenv`, `cenv2 with ce_alloca_locals := T`]
          internal_alloc_body_suffix_shape)) >> simp[]) >>
  simp[shape_step_def]
QED
Finalise compile_internal_function_shape

Theorem shape_state_new_block:
  !name st old s.
    new_block name st = (old,s) /\ shape_state st ==> shape_state s
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[] >>
  gvs[shape_state_def, state_insts_def, all_blocks_def, not_fresh_at_def] >>
  metis_tac[]
QED

Theorem internal_segment_new_block:
  !st old s name t has_ret_buf rc.
    new_block name st = (old,s) /\
    shape_extends T compiler_label s t ==>
    ?seg. all_blocks t = all_blocks st ++ seg /\
          internal_segment_ok (name,has_ret_buf,rc) seg
Proof
  rpt gen_tac >> strip_tac >>
  `all_blocks s = all_blocks st ++
     [<| bb_label := name; bb_instructions := [] |>]`
    by gvs[new_block_def, all_blocks_def] >>
  `state_insts s = state_insts st` by gvs[state_insts_def] >>
  fs[shape_extends_def, compileEnvTheory.cs_extends_def] >>
  qexists_tac `REVERSE new ++
    [<| bb_label := t.cs_current_bb;
        bb_instructions := t.cs_current_insts |>]` >>
  `all_blocks t = all_blocks st ++ (REVERSE new ++
    [<| bb_label := t.cs_current_bb;
        bb_instructions := t.cs_current_insts |>])`
    by gvs[new_block_def, all_blocks_def] >>
  simp[] >>
  gvs[internal_segment_ok_def, added_insts_def, added_labels_def,
      state_insts_def, DROP_APPEND, EVERY_FLAT, EVERY_MAP] >>
  Cases_on `new = []` >>
  gvs[new_block_def, arithmeticTheory.ADD_COMM] >>
  `0 < LENGTH new` by (Cases_on `new` >> gvs[]) >>
  `1 - LENGTH new = 0` by simp[] >>
  Cases_on `REVERSE new` >> gvs[] >>
  qmatch_asmsub_abbrev_tac `DROP k t.cs_current_insts` >>
  `k = 0` by (simp[Abbr `k`] >> decide_tac) >>
  gvs[DROP_1] >>
  metis_tac[HD_REVERSE, HD]
QED

(* From compile_internal_function_shape: new_block fn_lbl starts each
   segment, and the next one ends it. *)
Theorem compile_internal_fn_bodies_shape:
  !fns st r st'.
    compile_internal_fn_bodies fns st = (r, st') /\ shape_state st /\
    EVERY internal_fn_shape_ok fns ==>
    shape_state st' /\
    ?segs. all_blocks st' = all_blocks st ++ FLAT segs /\
           LIST_REL internal_segment_ok (internal_fn_descriptors fns) segs
Proof
  Induct_on `fns`
  >- (simp[compile_internal_fn_bodies_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >>
      simp[internal_fn_descriptors_def]) >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[Once compile_internal_fn_bodies_def, internal_fn_shape_ok_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `comp_ignore_bind (new_block name) m st` >>
  Cases_on `new_block name st` >>
  fs[comp_ignore_bind_def, comp_bind_def] >>
  rename1 `new_block name st = (old,s)` >>
  drule_all shape_state_new_block >> strip_tac >>
  fs[Abbr `m`, comp_bind_def] >>
  pairarg_tac >> fs[] >>
  drule_all compile_internal_function_shape >>
  rewrite_tac[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[comp_return_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  rename1 `cenv_static_ok cenv` >>
  rename1 `compile_internal_function cenv params has_ret_buf` >>
  drule_all internal_segment_new_block >>
  disch_then (qspecl_then [`has_ret_buf`, `cenv.ce_returns_count`]
    strip_assume_tac) >>
  qexists_tac `seg :: segs` >>
  simp[internal_fn_descriptors_def, APPEND_ASSOC]

QED

Theorem shape_state_initial_compile_state[local]:
  !lbl. shape_state (initial_compile_state lbl)
Proof
  simp[initial_compile_state_def, shape_state_def, opaque_insts_ok_def,
       state_insts_def, all_blocks_def]
QED

Theorem runtime_entry_blocks_shape[local]:
  !st. shape_extends F jump_label_ok (initial_compile_state "__entry") st ==>
    all_blocks st <> [] /\
    (HD (all_blocks st)).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks st))) /\
    EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions) (all_blocks st)
Proof
  gen_tac >> strip_tac >>
  `state_insts (initial_compile_state "__entry") = [] /\
   MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
     ["__entry"]`
    by simp[initial_compile_state_def, state_insts_def, all_blocks_def] >>
  qpat_x_assum `shape_extends _ _ _ _` mp_tac >>
  rewrite_tac[shape_extends_def] >> strip_tac >>
  drule state_insts_cs_extends >>
  drule block_labels_cs_extends >>
  asm_rewrite_tac [] >> rpt strip_tac >>
  qpat_x_assum `MAP _ (all_blocks (initial_compile_state _)) = _` kall_tac >>
  qpat_x_assum `state_insts (initial_compile_state _) = _` kall_tac >>
  fs[state_insts_def, EVERY_FLAT, EVERY_MAP] >>
  Cases_on `all_blocks st` >> gvs[] >>
  qpat_x_assum `EVERY (lowered_inst_ok F) _` mp_tac >>
  qpat_x_assum `_ ++ _ = added_insts _ _` (fn th => rewrite_tac[GSYM th]) >>
  simp[EVERY_FLAT, EVERY_MAP]
QED

Theorem runtime_fallback_shape[local]:
  !fallback_fn. fallback_shape_ok fallback_fn ==>
    shape_step F jump_label_ok (\st. T)
      (case fallback_fn of
         NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body, fb_ty) =>
           compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ty)
      (\x st. T)
Proof
  Cases >> simp[]
  >- (strip_tac >> irule shape_step_conseq >>
      qexistsl_tac [`jump_label_ok`,
        `\st. T /\ EVERY (label_or_plain st) [Lit 0w; Lit 0w]`,
        `\x st. T`] >>
      conj_tac >- simp[] >>
      conj_tac
      >- simp[label_or_plain_def, plain_operand_def,
              stackPlanTypesTheory.is_label_operand_def] >>
      conj_tac >- simp[] >>
      ho_match_mp_tac shape_step_emit_inst >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
           is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
           is_terminator_def, stackPlanTypesTheory.is_label_operand_def]) >>
  PairCases_on `x` >> strip_tac >>
  drule compile_fallback_body_shape >> strip_tac >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. T`, `\x st. T`] >>
  simp[jump_label_ok_def]
QED

Theorem runtime_entry_prefix_shape[local]:
  !selectors external_fns fallback_fn.
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn ==>
    shape_step F jump_label_ok (\st. T)
      (do fallback_lbl <- fresh_label "fallback";
          compile_selector_dispatch_linear
            (MAP (\(sel, lbl, z). (sel, lbl)) selectors) fallback_lbl;
          compile_external_fn_bodies external_fns;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body, fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ty)
       od) (\x st. T)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\l st. T /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_def]) >>
  gen_tac >> BETA_TAC >>
  Cases_on `compiler_label x`
  >- (irule shape_step_conseq >>
      qexistsl_tac [`jump_label_ok`, `\st. T`, `\x st. T`] >>
      simp[] >>
      irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
      reverse conj_tac
      >- (irule compile_selector_dispatch_linear_shape >>
          simp[jump_label_ok_def, EVERY_MAP] >>
          fs[EVERY_MEM, pairTheory.FORALL_PROD, jump_label_ok_def] >>
          metis_tac[]) >>
      gen_tac >> BETA_TAC >>
      irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
      reverse conj_tac >- (irule compile_external_fn_bodies_shape >> simp[]) >>
      gen_tac >> BETA_TAC >>
      irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
      reverse conj_tac
      >- (ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def, jump_label_ok_def]) >>
      gen_tac >> BETA_TAC >> irule runtime_fallback_shape >> simp[]) >>
  simp[shape_step_def]
QED

(* The runtime block stream: entry code (dispatch, external bodies,
   fallback) followed by one segment per internal function. *)
Theorem compile_generate_runtime_shape:
  !selectors external_fns internal_fns fallback_fn bucket_count
   fn_metadata_bytes dense_buckets entry_info st1.
    compile_generate_runtime selectors external_fns internal_fns fallback_fn
      Linear bucket_count fn_metadata_bytes dense_buckets entry_info
      (initial_compile_state "__entry") = ((), st1) /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns ==>
    shape_state st1 /\
    ?entry_blocks segs.
      all_blocks st1 = entry_blocks ++ FLAT segs /\
      entry_blocks <> [] /\ (HD entry_blocks).bb_label = "__entry" /\
      EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry_blocks)) /\
      EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions)
        entry_blocks /\
      LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_entry_prefix_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `shape_step F jump_label_ok (\st. T) prefix _` >>
  `compile_generate_runtime selectors external_fns internal_fns fallback_fn
     Linear bucket_count fn_metadata_bytes dense_buckets entry_info =
   comp_ignore_bind prefix
     (comp_bind (compile_internal_fn_bodies internal_fns) (\x. comp_return ()))`
    by simp[compile_generate_runtime_def, Abbr `prefix`,
            comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (prefix_result, entry_st)` >>
  Cases_on `prefix_result` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >>
  simp[shape_step_def] >>
  disch_then drule >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  drule runtime_entry_blocks_shape >> strip_tac >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  gvs[] >>
  rename1 `LIST_REL internal_segment_ok _ runtime_segs` >>
  qexistsl_tac [`all_blocks entry_st`, `runtime_segs`] >> simp[]
QED

(* ===== Source side conditions from supported_program ===== *)

(* supported_pure_expr rejects all Calls; supported_effect_expr accepts
   only IntCall, ExtCall, Send and Pop, so SelfDestructTarget is unsupported.
   supported_expr also rejects Env MsgGas and every raw_call form, and
   accepts builtins only at the arity their dispatcher reads. *)
Theorem supported_builtin_form_shape_root[local]:
  supported_builtin_form tops ty bi es ==>
  ~expr_shape_root (Builtin ty bi es)
Proof
  Cases_on `bi` >>
  simp[supportedExprFormsTheory.supported_builtin_form_def,
       expr_shape_root_def, builtin_arity_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[wordsTheory.NUMERAL_LESS_THM, listTheory.LENGTH_EQ_NUM_compute] >>
  Cases_on `es` >> gvs[]
QED

Theorem supported_type_builtin_form_shape_root[local]:
  supported_type_builtin_form tops ty tb target es ==>
  ~expr_shape_root (TypeBuiltin ty tb target es)
Proof
  Cases_on `tb` >>
  simp[supportedExprFormsTheory.supported_type_builtin_form_def,
       expr_shape_root_def, type_builtin_arity_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[wordsTheory.NUMERAL_LESS_THM, listTheory.LENGTH_EQ_NUM_compute] >>
  Cases_on `es` >> gvs[]
QED

Theorem supported_pure_shape[local]:
  (!tops e. supported_pure_expr tops e ==>
    ~supported_expr_exists expr_shape_root e) /\
  (!tops es. supported_pure_exprs tops es ==>
    ~supported_exprs_exists expr_shape_root es) /\
  (!tops fields. supported_pure_fields tops fields ==>
    ~supported_fields_exists expr_shape_root fields)
Proof
  ho_match_mp_tac supportedExprsTheory.supported_pure_expr_ind >>
  rw[supportedExprsTheory.supported_pure_expr_def,
     supported_expr_exists_def] >>
  simp[expr_shape_root_def]
  >- (qmatch_goalsub_rename_tac `supported_expr_exists expr_shape_root storage_base` >>
      Cases_on `storage_base` >> gvs[supported_expr_exists_def, expr_shape_root_def])
  >- (qmatch_goalsub_rename_tac `supported_expr_exists expr_shape_root storage_base` >>
      Cases_on `storage_base` >> gvs[supported_expr_exists_def, expr_shape_root_def])
  >- (drule supported_builtin_form_shape_root >> simp[expr_shape_root_def])
  >> drule supported_type_builtin_form_shape_root >> simp[expr_shape_root_def]
QED

Theorem supported_expr_shape[local]:
  !tops e. supported_expr tops e ==>
    ~supported_expr_exists expr_shape_root e
Proof
  rw[supportedExprsTheory.supported_expr_def]
  >- metis_tac[supported_pure_shape] >>
  qpat_x_assum `supported_effect_expr _ _` mp_tac >>
  Cases_on `e` >>
  simp[supportedExprsTheory.supported_effect_expr_def,
       supported_expr_exists_def, expr_shape_root_def]
  >- (rename1 `supported_target_exists _ pop_target` >>
      Cases_on `pop_target` >> simp[supported_expr_exists_def]) >>
  qmatch_goalsub_rename_tac `supported_opt_exists _ call_default` >>
  Cases_on `call_default` >> simp[supported_expr_exists_def] >>
  rename1 `!flags. call_target <> RawCallCalldataTarget flags` >>
  Cases_on `call_target` >> simp[]
  >- metis_tac[supported_pure_shape]
  >- (split_pair_case_tac >> simp[] >> metis_tac[supported_pure_shape]) >>
  qmatch_goalsub_rename_tac `supported_exprs_exists expr_shape_root send_args` >>
  namedCases_on `send_args` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "v rest2"] >> simp[] >>
  namedCases_on `rest2` ["", "g rest3"] >> simp[]
  >- (Cases_on `t` >> simp[supported_expr_exists_def] >>
      metis_tac[supported_pure_shape]) >>
  Cases_on `rest3` >> simp[] >>
  Cases_on `t` >> simp[supported_expr_exists_def] >>
  metis_tac[supported_pure_shape]
QED

Theorem supported_assignment_shape[local]:
  supported_assignment tops bindings target e ==>
  ~supported_assignment_exists expr_shape_root target /\
  ~supported_expr_exists expr_shape_root e
Proof
  Cases_on `target` >> simp[supportedStmtsTheory.supported_assignment_def] >>
  rename1 `BaseTarget bt` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_assignment_def,
       supported_assignment_exists_def, supported_expr_exists_def]
  >- (rpt strip_tac >> metis_tac[supported_expr_shape])
  >- metis_tac[supported_pure_shape]
  >- (qmatch_goalsub_rename_tac `supported_target_exists expr_shape_root parent` >> Cases_on `parent` >>
      simp[supported_expr_exists_def] >> metis_tac[supported_pure_shape]) >>
  qmatch_goalsub_rename_tac `supported_target_exists expr_shape_root parent` >> Cases_on `parent` >>
  simp[supported_expr_exists_def] >> metis_tac[supported_pure_shape]
QED

Theorem supported_aug_target_shape[local]:
  supported_aug_target tops bindings target ==>
  ~supported_target_exists expr_shape_root target
Proof
  Cases_on `target` >>
  simp[supportedStmtsTheory.supported_aug_target_def, supported_expr_exists_def]
QED

Theorem supported_append_target_shape[local]:
  supported_append_target tops target ==>
  ~supported_target_exists expr_shape_root target
Proof
  Cases_on `target` >>
  simp[supportedStmtsTheory.supported_append_target_def, supported_expr_exists_def]
QED

Theorem supported_string_reason_shape[local]:
  supported_string_reason tops e ==>
  ~supported_expr_exists expr_shape_root e
Proof
  Cases_on `e` >>
  simp[supportedStmtsTheory.supported_string_reason_def,
       supported_expr_exists_def, expr_shape_root_def] >>
  metis_tac[supported_pure_shape, supported_expr_exists_def, expr_shape_root_def]
QED

Theorem supported_assert_reason_shape[local]:
  supported_assert_reason tops reason ==>
  ~supported_assert_exists expr_shape_root reason
Proof
  Cases_on `reason` >>
  simp[supportedStmtsTheory.supported_assert_reason_def, supported_assert_exists_def] >>
  metis_tac[supported_string_reason_shape]
QED

Theorem supported_raise_reason_shape[local]:
  supported_raise_reason tops reason ==>
  ~supported_raise_exists expr_shape_root reason
Proof
  Cases_on `reason` >>
  simp[supportedStmtsTheory.supported_raise_reason_def, supported_raise_exists_def] >>
  metis_tac[supported_string_reason_shape]
QED

Theorem supported_log_shape[local]:
  supported_log tops id es ==> ~supported_exprs_exists expr_shape_root es
Proof
  simp[supportedStmtsTheory.supported_log_def] >>
  metis_tac[supported_pure_shape]
QED

Theorem supported_iterator_shape[local]:
  supported_iterator tops ty iter n ==>
  ~supported_iterator_exists expr_shape_root iter
Proof
  Cases_on `iter` >>
  simp[supportedStmtsTheory.supported_iterator_def, supported_iterator_exists_def]
  >- (Cases_on `e` >> simp[supported_expr_exists_def, expr_shape_root_def]) >>
  qmatch_goalsub_rename_tac `supported_expr_exists expr_shape_root start_expr` >>
  Cases_on `start_expr` >> simp[]
  >~ [`Literal lit_ty lit`]
  >- (simp[supported_expr_exists_def, expr_shape_root_def] >>
      qmatch_goalsub_rename_tac `supported_expr_exists expr_shape_root finish_expr` >>
      Cases_on `finish_expr` >>
      simp[supported_expr_exists_def, expr_shape_root_def] >>
      metis_tac[supported_pure_shape, supported_expr_exists_def, expr_shape_root_def]) >>
  metis_tac[supported_pure_shape]
QED

Theorem supported_stmts_shape[local]:
  (!tops bindings s. supported_stmt tops bindings s ==>
    ~supported_stmt_expr_exists expr_shape_root s) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    ~supported_stmts_expr_exists expr_shape_root ss)
Proof
  ho_match_mp_tac supportedStmtsTheory.supported_stmt_ind >>
  rw[supportedStmtsTheory.supported_stmt_def, supported_stmt_expr_exists_def,
     supported_expr_exists_def] >>
  metis_tac[supported_pure_shape, supported_expr_shape,
    supported_assignment_shape, supported_aug_target_shape,
    supported_append_target_shape, supported_assert_reason_shape,
    supported_raise_reason_shape, supported_log_shape, supported_iterator_shape]
QED

Theorem supported_function_body_shape:
  !tops vis args body.
    supported_function_body tops vis args body ==>
    ~supported_stmts_expr_exists expr_shape_root body
Proof
  simp[supported_function_body_def] >>
  metis_tac[supported_stmts_shape]
QED

Theorem add_module_var_locations_static:
  !tops vars.
    (!n loc. FLOOKUP vars n = SOME loc ==> static_loc loc) ==>
    !n loc. FLOOKUP (add_module_var_locations tops vars) n = SOME loc ==>
      static_loc loc
Proof
  Induct_on `tops` >- simp[add_module_var_locations_def] >>
  rpt gen_tac >> strip_tac >>
  simp[Once add_module_var_locations_def] >>
  first_x_assum match_mp_tac >>
  Cases_on `h` >> simp[] >>
  rpt (CASE_TAC >> simp[]) >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs(), static_loc_def] >>
  metis_tac[]
QED

Theorem allocate_args_static:
  !sft args off vars.
    (!n loc. FLOOKUP vars n = SOME loc ==> static_loc loc) ==>
    !n loc. FLOOKUP (FST (allocate_args sft args off vars)) n = SOME loc ==>
      static_loc loc
Proof
  gen_tac >> Induct >> simp[allocate_args_def] >>
  Cases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[allocate_args_def] >> first_x_assum match_mp_tac >>
  rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs(), static_loc_def] >>
  metis_tac[]
QED

Theorem allocate_locals_static:
  !sft locals off vars.
    (!n loc. FLOOKUP vars n = SOME loc ==> static_loc loc) ==>
    !n loc. FLOOKUP (FST (allocate_locals sft locals off vars)) n = SOME loc ==>
      static_loc loc
Proof
  gen_tac >> Induct >> simp[allocate_locals_def] >>
  Cases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[Once allocate_locals_def] >>
  rpt (CASE_TAC >> simp[]) >> first_x_assum match_mp_tac >>
  rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs(), static_loc_def] >>
  metis_tac[]
QED

Theorem build_compile_env_static:
  !tops vis mut fname args ret body use_trans.
    cenv_static_ok
      (build_compile_env tops vis mut fname args ret body use_trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!n loc. FLOOKUP (add_module_var_locations tops FEMPTY) n = SOME loc ==>
     static_loc loc` by
    (match_mp_tac add_module_var_locations_static >> simp[]) >>
  drule allocate_args_static >>
  disch_then (qspecl_then
    [`get_struct_fields (make_struct_fields_map tops)`, `args`, `0`] mp_tac) >>
  gvs[] >> strip_tac >>
  Cases_on `vis = External` >>
  gvs[allocate_internal_special_vars_def, AllCaseEqs(), cenv_static_ok_def] >>
  drule allocate_locals_static >>
  metis_tac[pairTheory.FST]
QED

Theorem classify_functions_external_source:
  !tops mut nr rr fname args defaults ret body.
    MEM (mut,nr,rr,fname,args,defaults,ret,body)
      (FST (classify_functions tops)) ==>
    MEM (FunctionDecl External mut nr rr fname args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >>
  rpt gen_tac >>
  simp[classify_functions_def, Once listTheory.FOLDR] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> fs[classify_functions_def] >>
  Cases_on `h` >> simp[classify_function_def] >>
  rpt CASE_TAC >> gvs[] >>
  metis_tac[classify_functions_def]
QED

Theorem MEM_classify_internal:
  !tops mut nr rr name args dflts ret body.
    MEM (mut,nr,rr,name,args,dflts,ret,body)
      (FST (SND (classify_functions tops))) <=>
    MEM (FunctionDecl Internal mut nr rr name args dflts ret body) tops
Proof
  Induct >> simp[classify_functions_def] >>
  gen_tac >> fs[classify_functions_def] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> Cases_on `h` >>
  gvs[classify_function_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >>
  simp[classify_function_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem classify_functions_fallback_mem:
  !tops mut nr rr fname args defaults ret body.
    FST (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    MEM (FunctionDecl External mut nr rr fname args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >>
  rpt gen_tac >>
  simp[classify_functions_def] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >>
  Cases_on `h` >> simp[classify_function_def] >>
  rpt (CASE_TAC >> simp[]) >>
  strip_tac >> gvs[] >>
  gvs[classify_functions_def] >>
  metis_tac[]
QED

(* build_compile_env maps module variables to storage/transient slots and
   arguments and locals to MemLoc; external functions have no return PC. *)
Theorem package_external_fn_shape_ok:
  !tops use_trans nkey_map target src.
    supported_program tops /\ MEM src (FST (classify_functions tops)) ==>
    external_fn_shape_ok
      (set_external_package_target target
         (package_external_fn tops use_trans nkey_map src))
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `src` >>
  drule classify_functions_external_source >> strip_tac >>
  drule_all supported_program_function >> strip_tac >>
  drule supported_function_body_shape >> strip_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       external_fn_shape_ok_def] >>
  rpt CASE_TAC >>
  fs[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
     cenv_static_ok_def, build_compile_env_external_no_return_pc] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem package_internal_fn_shape_ok:
  !tops use_trans nkey_map target src.
    supported_program tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
         (package_internal_fn tops use_trans nkey_map F 0 src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  drule_all supported_program_function >>
  strip_tac >> drule supported_function_body_shape >> strip_tac >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, internal_fn_shape_ok_def,
       cenv_static_ok_def] >>
  pure_rewrite_tac[GSYM cenv_static_ok_def] >>
  irule build_compile_env_static
QED

Theorem package_fallback_fn_shape_ok:
  !tops use_trans nkey_map target.
    supported_program tops ==>
    fallback_shape_ok
      (set_fallback_package_target target
         (package_fallback_fn tops use_trans nkey_map
            (FST (SND (SND (classify_functions tops))))))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FST (SND (SND (classify_functions tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def,
          fallback_shape_ok_def] >>
  rename1 `_ = SOME src` >> PairCases_on `src` >>
  drule classify_functions_fallback_mem >> strip_tac >>
  drule_all supported_program_function >>
  disch_then (assume_tac o MATCH_MP supported_function_body_shape) >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       fallback_shape_ok_def, build_compile_env_external_no_return_pc] >>
  simp[cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

(* ===== Labels ===== *)

Theorem compiler_label_prefix:
  !l. compiler_label l ==> ?rest. l = STRING #"@" rest
Proof
  rw[compiler_label_def, compiler_labels_future_def, fresh_label_output_def]
QED

Theorem internal_label_ok_append[local]:
  !l. internal_label_ok l ==> ?rest. l = "internal " ++ rest
Proof
  REWRITE_TAC [internal_label_ok_def, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem internal_label_not_reserved[local]:
  !l. internal_label_ok l ==> l <> "__entry" /\ ~reserved_label l
Proof
  gen_tac >> disch_then (strip_assume_tac o MATCH_MP internal_label_ok_append) >>
  pop_assum SUBST_ALL_TAC >> simp[reserved_label_def]
QED

Theorem jump_label_ok_names:
  !l. jump_label_ok l ==>
      l <> "__entry" /\ ~reserved_label l /\
      !n. internal_label_ok n ==> l <> n
Proof
  gen_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [jump_label_ok_def])
  >- (imp_res_tac compiler_label_prefix >> pop_assum SUBST_ALL_TAC >>
      simp[internal_label_ok_def, reserved_label_def])
  >> qpat_x_assum `isPREFIX _ _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[internal_label_ok_def, reserved_label_def]
QED

(* ===== Successors and instructions of a block list ===== *)

Theorem MEM_fn_insts_blocks_iff:
  !bbs inst. MEM inst (fn_insts_blocks bbs) <=>
             ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem get_successors_jump_label_ok:
  !internal inst l.
    lowered_inst_ok internal inst /\ MEM l (get_successors inst) ==>
    jump_label_ok l
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >>
  gvs[get_successors_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM op inst.inst_operands` >>
  Cases_on `op` >> gvs[venomStateTheory.get_label_def] >>
  gvs[lowered_inst_ok_def, inst_jump_labels_ok_def]
QED

Theorem bb_succs_jump_label_ok:
  !internal bb l.
    EVERY (lowered_inst_ok internal) bb.bb_instructions /\
    MEM l (bb_succs bb) ==> jump_label_ok l
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE] >>
  rename1 `LAST (i::is)` >>
  match_mp_tac
    (Q.SPECL [`internal`, `LAST (i::is)`, `l`] get_successors_jump_label_ok) >>
  gvs[EVERY_MEM] >>
  `MEM (LAST (i::is)) (i::is)` by simp[MEM_LAST] >>
  fs[] >> metis_tac[]
QED

(* One packaged function whose entry label no block jumps to. *)
Theorem lowered_fn_ok:
  !b fn insts.
    fn.fn_blocks <> [] /\ (HD fn.fn_blocks).bb_label = fn.fn_name /\
    ~reserved_label fn.fn_name /\ ~jump_label_ok fn.fn_name /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) fn.fn_blocks)) /\
    EVERY (\bb. EVERY (lowered_inst_ok b) bb.bb_instructions) fn.fn_blocks /\
    opaque_insts_ok insts /\
    (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
    fn_shape_ok fn /\ EVERY (lowered_inst_ok b) (fn_insts fn) /\
    first_block_no_preds fn
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (lowered_inst_ok b) (fn_insts fn)`
    by (gvs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
        metis_tac[]) >>
  `EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks`
    by (Cases_on `fn.fn_blocks` >> gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
        metis_tac[jump_label_ok_names]) >>
  rpt conj_tac
  >- (gs[fn_shape_ok_def, fn_entry_label_def, entry_block_def, NULL_EQ] >>
      conj_tac >- metis_tac[opaque_insts_ok_opaque_use_ok] >>
      gvs[EVERY_MEM, lowered_inst_ok_def])
  >- simp[]
  >> simp[first_block_no_preds_def, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  `EVERY (lowered_inst_ok b) bb.bb_instructions`
    by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all bb_succs_jump_label_ok >> metis_tac[]
QED

Theorem LIST_REL_MEM_MAP2[local]:
  !R f xs ys z.
    LIST_REL R xs ys /\ MEM z (MAP2 f xs ys) ==>
    ?x y. R x y /\ MEM x xs /\ MEM y ys /\ z = f x y
Proof
  Induct_on `xs` >> Cases_on `ys` >> rw[MAP2] >> metis_tac[]
QED

Theorem internal_fns_ok:
  !descs segs insts fn.
    LIST_REL internal_segment_ok descs segs /\
    EVERY (\d. internal_label_ok (FST d)) descs /\
    opaque_insts_ok insts /\
    (!inst. MEM inst (FLAT (MAP (\bb. bb.bb_instructions) (FLAT segs))) ==>
            MEM inst insts) /\
    MEM fn (MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                            (SND (SND d))) descs segs) ==>
    fn_shape_ok fn /\ EVERY (lowered_inst_ok T) (fn_insts fn) /\
    first_block_no_preds fn
Proof
  rpt gen_tac >> strip_tac >>
  drule_all LIST_REL_MEM_MAP2 >> strip_tac >> gvs[] >>
  PairCases_on `x` >> fs[internal_segment_ok_def] >>
  `internal_label_ok x0` by (fs[EVERY_MEM] >> res_tac >> fs[]) >>
  `~jump_label_ok x0` by metis_tac[jump_label_ok_names] >>
  `~reserved_label x0` by metis_tac[internal_label_not_reserved] >>
  match_mp_tac
    (Q.SPECL [`T`, `mk_internal_function x0 y x1 x2`, `insts`] lowered_fn_ok) >>
  gs[mk_internal_function_metadata] >> rpt conj_tac
  >~ [`EVERY jump_label_ok _`] >- gvs[jump_label_ok_def, EVERY_MEM]
  >> rw[fn_insts_def, MEM_fn_insts_blocks_iff, mk_internal_function_metadata] >>
  first_x_assum irule >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

(* ===== The packaged unit ===== *)

Theorem mk_raw_function_fields[local]:
  (mk_raw_function n bs).fn_name = n /\
  (mk_raw_function n bs).fn_blocks = bs
Proof
  simp[mk_raw_function_def]
QED

Theorem lowered_unit_source_ok:
  !entry descs segs data.
    entry <> [] /\ (HD entry).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry)) /\
    EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions) entry /\
    LIST_REL internal_segment_ok descs segs /\
    EVERY (\d. internal_label_ok (FST d)) descs /\
    opaque_insts_ok
      (FLAT (MAP (\bb. bb.bb_instructions) (entry ++ FLAT segs))) ==>
    o1_source_unit_ok
      <| cu_context :=
           mk_venom_context
             (mk_raw_function "__entry" entry ::
              MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                              (SND (SND d))) descs segs)
             (SOME "__entry");
         cu_data_segment := data |>
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `insts = FLAT (MAP (\bb. bb.bb_instructions) (entry ++ FLAT segs))` >>
  qabbrev_tac `ifns = MAP2 (\d seg. mk_internal_function (FST d) seg
                                     (FST (SND d)) (SND (SND d))) descs segs` >>
  `~jump_label_ok "__entry"` by metis_tac[jump_label_ok_names] >>
  `~reserved_label "__entry"` by EVAL_TAC >>
  `!inst. MEM inst (fn_insts (mk_raw_function "__entry" entry)) ==>
          MEM inst insts`
    by (rw[fn_insts_def, mk_raw_function_fields, MEM_fn_insts_blocks_iff,
           Abbr `insts`, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `fn_shape_ok (mk_raw_function "__entry" entry) /\
   EVERY (lowered_inst_ok F) (fn_insts (mk_raw_function "__entry" entry)) /\
   first_block_no_preds (mk_raw_function "__entry" entry)`
    by (match_mp_tac
          (Q.SPECL [`F`, `mk_raw_function "__entry" entry`, `insts`]
             lowered_fn_ok) >>
        gs[mk_raw_function_fields]) >>
  `!fn. MEM fn ifns ==>
        fn_shape_ok fn /\ EVERY (lowered_inst_ok T) (fn_insts fn) /\
        first_block_no_preds fn`
    by (rpt gen_tac >> strip_tac >>
        match_mp_tac (Q.SPECL [`descs`, `segs`, `insts`, `fn`] internal_fns_ok) >>
        gvs[Abbr `ifns`, Abbr `insts`, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[]) >>
  `entry_fn_no_ret (mk_raw_function "__entry" entry)`
    by (simp[contextCodegenRelTheory.entry_fn_no_ret_def,
             mk_raw_function_fields, EVERY_MEM] >>
        rpt strip_tac >> fs[EVERY_MEM, lowered_inst_ok_def] >> res_tac) >>
  `get_params (HD entry).bb_instructions = []`
    by (Cases_on `entry` >> fs[] >> rename1 `get_params bb0.bb_instructions` >>
        Cases_on `bb0.bb_instructions` >>
        fs[stackPlanGenTheory.get_params_def, lowered_inst_ok_def]) >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode)
     (fn_insts (mk_raw_function "__entry" entry))`
    by fs[EVERY_MEM, lowered_inst_ok_def] >>
  `EVERY fn_shape_ok ifns /\ EVERY first_block_no_preds ifns`
    by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn))
     ifns`
    by (simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
        fs[EVERY_MEM, lowered_inst_ok_def]) >>
  `!fn. MEM fn ifns ==>
        EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn)`
    by (rpt strip_tac >> res_tac >> fs[EVERY_MEM, lowered_inst_ok_def]) >>
  simp[o1_source_unit_ok_def, unit_shape_ok_def, entry_fn_first_def,
       mk_venom_context_def, internal_termination_ok_def,
       mk_raw_function_fields] >>
  rpt strip_tac >> gvs[] >> res_tac >> fs[EVERY_MEM]
QED

(* package_internal_blocks splits the stream exactly at the segments. *)
Theorem package_internal_blocks_segments:
  !descs segs entry.
    LIST_REL internal_segment_ok descs segs /\
    ALL_DISTINCT (MAP FST descs) /\
    EVERY (\d. ~compiler_label (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) entry)) descs ==>
    package_internal_blocks descs (entry ++ FLAT segs) =
      SOME (entry,
            MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                            (SND (SND d))) descs segs)
Proof
  Induct
  >- rw[package_internal_blocks_def] >>
  PairCases >> rw[LIST_REL_CONS1] >>
  rename1 `internal_segment_ok _ seg` >>
  rename1 `LIST_REL internal_segment_ok descs ys` >>
  `?bb tl. seg = bb :: tl` by (Cases_on `seg` >> gvs[internal_segment_ok_def]) >>
  fs[internal_segment_ok_def] >>
  `split_blocks_at h0 (entry ++ bb :: (tl ++ FLAT ys)) =
     SOME (entry, bb :: (tl ++ FLAT ys))`
    by (irule split_blocks_at_append_delimiter >> gs[]) >>
  gs[package_internal_blocks_def] >>
  first_x_assum (qspecl_then [`ys`, `bb :: tl`] mp_tac) >>
  impl_tac
  >- (gvs[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  simp[]
QED

(* ===== Runtime lowering ===== *)

Theorem internal_name_not_entry_label:
  !n entry.
    internal_label_ok n /\ entry <> [] /\ (HD entry).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry)) ==>
    ~compiler_label n /\ ~MEM n (MAP (\bb. bb.bb_label) entry)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> imp_res_tac compiler_label_prefix >>
      imp_res_tac internal_label_ok_append >> gvs[]) >>
  `n <> "__entry"` by metis_tac[internal_label_not_reserved] >>
  Cases_on `entry` >> gvs[EVERY_MEM] >> metis_tac[jump_label_ok_names]
QED

Theorem run_lowering_source_unit_ok:
  !selectors external_fns internal_fns fallback_fn rpolicy bucket_count
   fn_metadata_bytes dense_buckets entry_info unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
      SOME unit /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) ==>
    o1_source_unit_ok unit
Proof
  rpt gen_tac >> strip_tac >>
  `lowering_policy_ok rpolicy`
    by (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime selectors external_fns internal_fns
              fallback_fn Linear bucket_count fn_metadata_bytes dense_buckets
              entry_info (initial_compile_state "__entry")` >>
  rename1 `_ = (u, st1)` >> Cases_on `u` >>
  drule_all compile_generate_runtime_shape >> strip_tac >>
  `opaque_insts_ok
     (FLAT (MAP (\bb. bb.bb_instructions) (entry_blocks ++ FLAT segs)))`
    by (qpat_x_assum `shape_state st1` mp_tac >>
        simp[shape_state_def, state_insts_def] >>
        qpat_x_assum `all_blocks st1 = _` (fn th => simp[th])) >>
  `package_internal_blocks (internal_fn_descriptors internal_fns)
     (entry_blocks ++ FLAT segs) =
   SOME (entry_blocks,
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors internal_fns)
              segs)`
    by (match_mp_tac package_internal_blocks_segments >> ASM_REWRITE_TAC [] >>
        REWRITE_TAC [EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
        match_mp_tac internal_name_not_entry_label >> fs[EVERY_MEM]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks st1 = _` (assume_tac o REWRITE_RULE [all_blocks_def]) >>
  gs[run_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[] >>
  irule lowered_unit_source_ok >> gs[]
QED

(* ===== Source side: selectors and internal names ===== *)

Theorem build_selectors_fn_labels:
  !tenv fs. EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) (build_selectors tenv fs)
Proof
  gen_tac >> Induct >> simp[build_selectors_def] >>
  PairCases >> fs[build_selectors_def, compute_selector_def, IS_PREFIX_APPEND]
QED

Theorem MEM_supported_function_names:
  !tops name. MEM name (supported_function_names tops) <=>
    ?vis mut nr rr args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops
Proof
  Induct >> simp[supported_function_names_def] >>
  gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def] >> metis_tac[]
QED

Theorem source_internal_fn_descriptor_label[simp]:
  !tops is_ctor mut nr rr name args dflts ret body.
    FST (source_internal_fn_descriptor tops is_ctor
      (mut,nr,rr,name,args,dflts,ret,body)) =
    internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) is_ctor
Proof
  simp[source_internal_fn_descriptor_def]
QED

Theorem classified_internal_names_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
    ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
      (FST (SND (classify_functions tops))))
Proof
  Induct >> simp[classify_functions_def, supported_function_names_def] >>
  gen_tac >> fs[classify_functions_def] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> Cases_on `h` >>
  gvs[classify_function_def, supported_function_names_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> simp[]
  >- (IF_CASES_TAC >> simp[]) >>
  rpt strip_tac >> simp[] >>
  gvs[MEM_MAP] >>
  rename1 `MEM payload acc1` >> PairCases_on `payload` >> gvs[] >>
  `MEM (payload0,payload1,payload2,payload3,payload4,payload5,payload6,payload7)
    (FST (SND (classify_functions tops)))` by
    simp[classify_functions_def] >>
  drule (iffLR MEM_classify_internal) >>
  metis_tac[MEM_supported_function_names]
QED

(* Labels are distinct when equal labels mean equal names and the names are
   distinct. *)
Theorem ALL_DISTINCT_MAP_name_reflect[local]:
  !l f. ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p)))) l) /\
        (!x y. MEM x l /\ MEM y l /\ f x = f y ==>
               FST (SND (SND (SND x))) = FST (SND (SND (SND y)))) ==>
        ALL_DISTINCT (MAP f l)
Proof
  Induct >> rw[MEM_MAP] >- metis_tac[] >>
  first_x_assum irule >> metis_tac[]
QED

(* Each internal tuple of classify_functions comes from a FunctionDecl
   Internal in tops (MEM_classify_internal), and its label is
   internal_fn_label of its id and name (internal_fn_label_prefix).  Equal
   labels have equal ids (internal_fn_label_id_11), hence equal names
   (build_func_ids_11); the names are a sublist of supported_function_names
   tops, which supported_declaration_names makes ALL_DISTINCT. *)
Theorem supported_internal_descriptors_ok:
  !tops is_ctor.
    supported_program tops ==>
    EVERY (\d. internal_label_ok (FST d))
      (MAP (source_internal_fn_descriptor tops is_ctor)
         (FST (SND (classify_functions tops)))) /\
    ALL_DISTINCT
      (MAP FST (MAP (source_internal_fn_descriptor tops is_ctor)
                  (FST (SND (classify_functions tops)))))
Proof
  rpt strip_tac
  >- (rw[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
      REWRITE_TAC [internal_label_ok_def, internal_fn_label_prefix]) >>
  REWRITE_TAC [MAP_MAP_o] >>
  irule ALL_DISTINCT_MAP_name_reflect >> rpt conj_tac
  >~ [`ALL_DISTINCT _`]
  >- (irule classified_internal_names_distinct >>
      drule supported_program_names >>
      metis_tac[supported_declaration_names_unique]) >>
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >>
  imp_res_tac internal_fn_label_id_11 >>
  imp_res_tac (iffLR MEM_classify_internal) >>
  metis_tac[build_func_ids_11, function_visibility_distinct]
QED

(* S2's statement, proved from the generator and source lemmas above.
   package_internal_blocks splits the block stream at each internal entry
   label; supported_internal_descriptors_ok keeps those labels apart from
   each other and from every other label. *)
Theorem lower_vyper_runtime_unit_source_unit_ok_names:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops ==>
    o1_source_unit_ok unit
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  simp[] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac supported_internal_descriptors_ok >>
  impl_tac >- first_assum ACCEPT_TAC >>
  REWRITE_TAC [pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl)
     (build_selectors (type_env tops) exts)`
    by REWRITE_TAC [build_selectors_fn_labels] >>
  `!x. MEM x exts ==>
       external_fn_shape_ok
         (set_external_package_target rpolicy.rpol_target
            (package_external_fn tops F (assign_nkeys tops 0) x))`
    by (rpt strip_tac >> irule package_external_fn_shape_ok >> gs[]) >>
  `!x. MEM x ints ==>
       internal_fn_shape_ok
         (set_internal_package_target rpolicy.rpol_target
            (package_internal_fn tops F (assign_nkeys tops 0) F 0 x))`
    by (rpt strip_tac >> irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok
     (set_fallback_package_target rpolicy.rpol_target
        (package_fallback_fn tops F (assign_nkeys tops 0) fb))`
    by (qspecl_then [`tops`, `F`, `assign_nkeys tops 0`,
                     `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >>
        gs[]) >>
  drule run_lowering_source_unit_ok >> disch_then match_mp_tac >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP, EVERY_MEM] >>
  fs[MEM_MAP, PULL_EXISTS]
QED
