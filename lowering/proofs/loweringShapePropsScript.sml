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
 *   expr_shape_root            — the two source forms whose lowering breaks
 *                                the shape (msg.gas, raw_call(msg.data))
 *   cenv_shape_ok, cenv_static_ok, value_shape_ok, loop_ctx_shape_ok
 *   external_fn_shape_ok, fallback_shape_ok, internal_fn_shape_ok
 *   internal_segment_ok        — one internal function's blocks
 *   internal_name_ok           — internal names that cannot collide with
 *                                lowering labels
 *   compile_expr_shape, compile_stmt_shape, compile_*_shape
 *   compile_generate_runtime_shape — the whole runtime block stream
 *   package_internal_blocks_segments
 *   run_lowering_source_unit_ok
 *   supported_function_body_shape, package_*_shape_ok — supported_program
 *                                gives the generator side conditions
 *)
Theory loweringShapeProps
Ancestors
  list rich_list loweringShapeDefs compileEnv context emitHelper
  exprLowering stmtLowering moduleLowering vyperCompiler compileVyper abiEncoder
  supportedProgram supportedNames supportedStmtTraverse supportedExprTraverse
  unitShapeDefs venomInst vyperAST

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
   lowers to DALLOCA (and DELEGATECALL with is_delegate_call); a builtin
   with too few arguments compiles HD []. *)
Definition expr_shape_root_def:
  expr_shape_root e <=>
    (?ty es. e = Builtin ty (Env MsgGas) es) \/
    (?ty flags es d. e = Call ty (RawCallCalldataTarget flags) es d) \/
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
  internal_segment_ok (name : string, has_ret_buf : bool, rc : num) seg <=>
    seg <> [] /\ (HD seg).bb_label = name /\
    EVERY compiler_label (TL (MAP (\bb. bb.bb_label) seg)) /\
    EVERY (\bb. EVERY (lowered_inst_ok T) bb.bb_instructions) seg
End

(* Internal entry labels are the raw function names, so a name must avoid
   the reserved labels and every label the lowering itself makes: "__entry",
   compiler labels ("@..."), and external entry labels ("fn_" ++ name). *)
Definition internal_name_ok_def:
  internal_name_ok name <=>
    supported_internal_name name /\ name <> "__entry" /\
    ~isPREFIX "@" name /\ ~isPREFIX "fn_" name
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

(* For alan, by compile_expr_ind; one case per compile_expr_body clause and
   builtin.  The builtin families (abiEncoder, builtin*, context copy loops)
   are plain shape_step facts under plain operands.  Under value_shape_ok no
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
  cheat
QED

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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
           inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
       inst_shape_ok_def, jump_labels_ok_def, mk_inst_def,
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
            jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
        jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
       jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
       jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
       jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
       jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
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
       jump_labels_ok_def, mk_inst_def, is_read0_opcode_def,
       label_positions_ok_def, is_terminator_def, is_param_opcode_def,
       label_or_plain_def, plain_operand_def] >> metis_tac[]
QED

Finalise compile_ensure_in_memory_shape

(* Shared helper of every value consumer; weakly frozen. *)
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
       label_positions_ok_def, is_read0_opcode_def, jump_labels_ok_def,
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
      label_positions_ok_def, is_read0_opcode_def, jump_labels_ok_def,
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


(* The cenv a statement body runs under: one more plain PtrVar local. *)
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
       raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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
           jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
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
  jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
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

Theorem compile_safe_pow_shape[local]:
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
Finalise compile_safe_pow_shape

Theorem compile_mul_overflow_check_shape[local]:
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
Finalise compile_mul_overflow_check_shape

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

Theorem stmt_shape_stable_loop_context[local]:
  !src dst ctr b.
    shape_stable (\st. plain_operand st src /\
      (plain_operand st dst /\ (plain_operand st (Var ctr) /\ b)))
Proof
  rpt gen_tac >>
  simp[shape_stable_conj, stmt_shape_stable_plain, stmt_shape_stable_const]
QED

fun stmt_sequence pre first_step =
  irule shape_step_ignore_bind >> qexists_tac pre >>
  reverse conj_tac >- first_step >> gen_tac >> BETA_TAC;
val stmt_loop_stability = simp[shape_stable_conj, stmt_shape_stable_plain];

Theorem compile_word_copy_loop_noncode_shape[local]:
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
Finalise compile_word_copy_loop_noncode_shape

Theorem compile_storage_to_memory_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_storage_to_memory src dst n) (\u st. T)
Proof
  simp[compile_storage_to_memory_def, compile_word_copy_loop_noncode_shape]
QED

Theorem compile_memory_to_storage_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_memory_to_storage src dst n) (\u st. T)
Proof
  simp[compile_memory_to_storage_def, compile_word_copy_loop_noncode_shape]
QED

Theorem compile_transient_to_memory_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_transient_to_memory src dst n) (\u st. T)
Proof
  simp[compile_transient_to_memory_def, compile_word_copy_loop_noncode_shape]
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

Theorem stmt_typed_copy_loop_shape[local]:
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
Finalise stmt_typed_copy_loop_shape

Theorem compile_typed_copy_shape[local]:
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
Finalise compile_typed_copy_shape

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


(* For alan, by compile_stmt_ind.  internal is IS_SOME ce_return_pc: Return
   emits RET exactly when ce_return_pc is SOME, STOP/RETURN otherwise. *)
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

Theorem compile_abi_encode_dyn_static_loop_shape[local]:
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
Finalise compile_abi_encode_dyn_static_loop_shape

Theorem compile_abi_encode_shape[local]:
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
Finalise compile_abi_encode_shape


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

Theorem compile_dynarray_append_shape[local]:
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
Finalise compile_dynarray_append_shape


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
  cheat
QED

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
           jump_labels_ok_def, label_or_plain_def, plain_operand_def,
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
           jump_labels_ok_def]) >>
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
           jump_labels_ok_def, label_or_plain_def, plain_operand_def,
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
           is_terminator_def, is_param_opcode_def, jump_labels_ok_def,
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
       jump_labels_ok_def, label_or_plain_def,
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
       jump_labels_ok_def, jump_label_ok_def, is_terminator_def, is_param_opcode_def,
       is_read0_opcode_def, label_positions_ok_def,
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

(* Ordinary emissions may establish instruction validity from their input. *)

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
        jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
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
      label_positions_ok_def, is_read0_opcode_def, jump_labels_ok_def,
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
           raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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

Theorem materialize_internal_params_shape[local]:
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
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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
    inst_shape_ok_def, jump_labels_ok_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def] >>
  simp[shape_step_def, label_or_plain_def] >> rpt strip_tac >>
  `~is_label_operand x /\ ~is_label_operand h2` by
    (conj_tac
     >- (qpat_x_assum `plain_operand st x` mp_tac >>
         simp[plain_operand_def]) >>
     qpat_x_assum `plain_operand st h2` mp_tac >> simp[plain_operand_def]) >>
  first_x_assum drule_all >> simp[]
QED
Finalise materialize_internal_params_shape

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
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def] >>
  simp[shape_step_def] >> metis_tac[]
QED

(* Bounded opcode checks shared by the straight-line lock stages. *)
val intfn_lock_simps =
  [shape_stable_def, label_or_plain_def, plain_operand_def,
   stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
   mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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
      Cases_on `pc` >> simp intfn_lock_simps >>
      rewrite_tac[shape_step_def, retpc_operand_def] >>
      simp[] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `INVALID`, `[]`, `[]`]
    shape_step_emit_inst) >>
  simp intfn_lock_simps >> rewrite_tac[shape_step_def] >> metis_tac[]
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

Theorem internal_alloc_body_suffix_shape[local]:
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
          simp intfn_lock_simps >> rewrite_tac[shape_step_def] >> metis_tac[]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  Cases_on `is_nr` >> simp[]
  >- (irule compile_nonreentrant_lock_shape) >>
  irule shape_step_return >> simp[]
QED
Finalise internal_alloc_body_suffix_shape

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
        shape_step_emit_op) >> simp intfn_lock_simps) >>
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
Resume compile_internal_function_shape[suffix]:
  Cases_on `cenv2.ce_return_pc = SOME (PtrVar pc 0)`
  >- (simp[comp_ignore_bind_def] >> irule shape_step_conseq >>
      irule_at Any (SRULE [comp_ignore_bind_def, comp_bind_assoc,
        internal_comp_bind_return] internal_alloc_body_suffix_shape) >> simp[]) >>
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
  fs[shape_extends_def, fragExecTheory.cs_extends_def] >>
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
           raw_opcode_ok_def, inst_shape_ok_def, jump_labels_ok_def,
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

(* supported_expr rejects Env MsgGas and every raw_call form, and accepts
   builtins only at the arity their dispatcher reads. *)
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

Theorem jump_label_ok_names:
  !l. jump_label_ok l ==>
      l <> "__entry" /\ ~reserved_label l /\
      !n. internal_name_ok n ==> l <> n
Proof
  gen_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [jump_label_ok_def])
  >- (imp_res_tac compiler_label_prefix >> pop_assum SUBST_ALL_TAC >>
      simp[internal_name_ok_def, reserved_label_def])
  >> qpat_x_assum `isPREFIX _ _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[internal_name_ok_def, reserved_label_def]
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
  gvs[lowered_inst_ok_def, jump_labels_ok_def]
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
    EVERY (\d. internal_name_ok (FST d)) descs /\
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
  `internal_name_ok x0` by (fs[EVERY_MEM] >> res_tac >> fs[]) >>
  `~jump_label_ok x0` by metis_tac[jump_label_ok_names] >>
  `~reserved_label x0`
    by gvs[internal_name_ok_def, supported_internal_name_def,
           reserved_label_def] >>
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
    EVERY (\d. internal_name_ok (FST d)) descs /\
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
    internal_name_ok n /\ entry <> [] /\ (HD entry).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry)) ==>
    ~compiler_label n /\ ~MEM n (MAP (\bb. bb.bb_label) entry)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> imp_res_tac compiler_label_prefix >>
      gvs[internal_name_ok_def]) >>
  `n <> "__entry"` by fs[internal_name_ok_def] >>
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
    EVERY (\d. internal_name_ok (FST d)) (internal_fn_descriptors internal_fns) /\
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

(* For alan, by induction on tops through classify_function: each internal
   tuple comes from a FunctionDecl Internal in tops, so its name meets the
   premise, and the internal names are a sublist of
   supported_function_names tops, which supported_declaration_names makes
   ALL_DISTINCT. *)
Theorem MEM_supported_function_names:
  !tops name. MEM name (supported_function_names tops) <=>
    ?vis mut nr rr args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops
Proof
  Induct >> simp[supported_function_names_def] >>
  gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def] >> metis_tac[]
QED

Theorem source_internal_fn_descriptor_name[simp]:
  !tops mut nr rr name args dflts ret body.
    FST (source_internal_fn_descriptor tops
      (mut,nr,rr,name,args,dflts,ret,body)) = name
Proof
  simp[source_internal_fn_descriptor_def]
QED

Theorem classified_internal_names_distinct:
  !tops envtops. ALL_DISTINCT (supported_function_names tops) ==>
    ALL_DISTINCT (MAP FST (MAP (source_internal_fn_descriptor envtops)
      (FST (SND (classify_functions tops)))))
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

Theorem supported_internal_descriptors_ok:
  !tops.
    supported_program tops /\
    (!mut nr rr name args dflts ret body.
       MEM (FunctionDecl Internal mut nr rr name args dflts ret body) tops ==>
       internal_name_ok name) ==>
    EVERY (\d. internal_name_ok (FST d))
      (MAP (source_internal_fn_descriptor tops)
         (FST (SND (classify_functions tops)))) /\
    ALL_DISTINCT
      (MAP FST (MAP (source_internal_fn_descriptor tops)
                  (FST (SND (classify_functions tops)))))
Proof
  rpt strip_tac
  >- (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
      rename1 `MEM payload (FST (SND (classify_functions tops)))` >>
      PairCases_on `payload` >> gvs[] >>
      drule (iffLR MEM_classify_internal) >> metis_tac[]) >>
  irule classified_internal_names_distinct >>
  drule supported_program_names >>
  metis_tac[supported_declaration_names_unique]
QED

(* S2 with the internal-name premise.  Without it S2 is false: an internal
   function named "fn_foo" next to an external "foo" makes both entry
   labels "fn_foo", so the internal function's blocks include external code
   ending in STOP. *)
Theorem lower_vyper_runtime_unit_source_unit_ok_names:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    (!mut nr rr name args dflts ret body.
       MEM (FunctionDecl Internal mut nr rr name args dflts ret body) tops ==>
       internal_name_ok name) ==>
    o1_source_unit_ok unit
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  simp[] >> strip_tac >>
  qspec_then `tops` mp_tac supported_internal_descriptors_ok >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  ASM_REWRITE_TAC [pairTheory.FST, pairTheory.SND] >> strip_tac >>
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
