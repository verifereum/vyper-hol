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

(* Shared helper of every value consumer; weakly frozen. *)
Theorem unwrap_value_shape:
  !cenv v internal.
    shape_step internal compiler_label
      (\st. cenv_shape_ok st cenv /\ value_shape_ok st v)
      (unwrap_value cenv v) (\op st. plain_operand st op)
Proof
  cheat
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

Theorem compile_alloc_buffer_shape[local]:
  !internal size.
    shape_step internal compiler_label (\st. T)
      (compile_alloc_buffer size)
      (\b st. plain_operand st b.buf_operand)
Proof
  map_every qx_gen_tac [`internal`, `nbytes`] >> simp[compile_alloc_buffer_def] >>
  irule shape_step_bind >> qexists_tac `\op st. plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  mp_tac (Q.SPECL [`internal`, `compiler_label`, `\st. T`, `ALLOCA`,
    `[Lit (n2w nbytes)]`] shape_step_emit_op) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
       mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
       label_positions_ok_def, is_param_opcode_def]
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

Theorem compile_ptr_load_shape[local]:
  !internal is_ctor loc op.
    loc <> LocCode ==>
    shape_step internal compiler_label (\st. plain_operand st op)
      (compile_ptr_load is_ctor loc op) (\x st. plain_operand st x)
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ptr_load_def] >>
  stmt_plain_emit
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

Theorem compile_word_copy_loop_shape[local]:
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
Resume compile_word_copy_loop_shape[loop]:
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
Resume compile_word_copy_loop_shape[initial_assign]:
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_word_copy_loop_shape[copy]:
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
Resume compile_word_copy_loop_shape[destination]:
  qx_gen_tac `loaded` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\off st. plain_operand st off /\ (plain_operand st loaded /\ plain_operand st (Var ctr))` >> conj_tac
  >- suspend "store" >>
  ho_match_mp_tac stmt_shape_frame >>
  qexists_tac `\st. plain_operand st dst /\ plain_operand st (Var ctr)` >>
  simp[shape_stable_conj, stmt_shape_stable_plain, stmt_word_offset_shape]
QED
Resume compile_word_copy_loop_shape[store]:
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
Resume compile_word_copy_loop_shape[increment]:
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
Finalise compile_word_copy_loop_shape

Theorem compile_storage_to_memory_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_storage_to_memory src dst n) (\u st. T)
Proof
  simp[compile_storage_to_memory_def, compile_word_copy_loop_shape]
QED

Theorem compile_memory_to_storage_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_memory_to_storage src dst n) (\u st. T)
Proof
  simp[compile_memory_to_storage_def, compile_word_copy_loop_shape]
QED

Theorem compile_transient_to_memory_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_transient_to_memory src dst n) (\u st. T)
Proof
  simp[compile_transient_to_memory_def, compile_word_copy_loop_shape]
QED

Theorem compile_memory_to_transient_shape[local]:
  !internal src dst n.
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_memory_to_transient src dst n) (\u st. T)
Proof
  simp[compile_memory_to_transient_def, compile_word_copy_loop_shape]
QED

Theorem compile_slot_to_memory_shape[local]:
  !internal src dst n loc.
    loc <> LocCode ==>
    shape_step internal compiler_label
      (\st. plain_operand st src /\ plain_operand st dst)
      (compile_slot_to_memory src dst n loc) (\u st. T)
Proof
  simp[compile_slot_to_memory_def, compile_word_copy_loop_shape]
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

Theorem compile_nonreentrant_unlock_shape[local]:
  !internal nkey use_transient is_view.
    shape_step internal compiler_label (\st. T)
      (compile_nonreentrant_unlock nkey use_transient is_view) (\x st. T)
Proof
  rpt gen_tac >> simp[compile_nonreentrant_unlock_def] >>
  Cases_on `is_view` >- (simp[] >> irule shape_step_return >> simp[]) >>
  Cases_on `use_transient` >> simp[] >> stmt_plain_void_drop >>
  simp[stmt_shape_stable_const]
QED

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
      simp[] >> irule compile_word_copy_loop_shape >> simp[]]) >>
   irule shape_step_return >> simp[])
QED
Finalise compile_dynarray_append_shape

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

Theorem compile_get_target_ptr_shape[local]:
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
Finalise compile_get_target_ptr_shape

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

(* Straight-line code, fresh labels and JMPs to the selector labels. *)
Theorem compile_selector_dispatch_linear_shape:
  !selectors fallback_lbl.
    EVERY (\(sel, lbl). jump_label_ok lbl) selectors /\
    jump_label_ok fallback_lbl ==>
    shape_step F jump_label_ok (\st. T)
      (compile_selector_dispatch_linear selectors fallback_lbl) (\x st. T)
Proof
  cheat
QED

(* Each body opens its "fn_" entry block, then compile_guarded_body via
   compile_stmt_shape with ce_return_pc = NONE. *)
Theorem compile_external_fn_bodies_shape:
  !fns.
    EVERY external_fn_shape_ok fns ==>
    shape_step F jump_label_ok (\st. T) (compile_external_fn_bodies fns)
      (\x st. T)
Proof
  cheat
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
  cheat
QED

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
  cheat
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
  cheat
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
  cheat
QED

(* ===== Source side conditions from supported_program ===== *)

(* supported_expr rejects Env MsgGas and every raw_call form, and accepts
   builtins only at the arity their dispatcher reads. *)
Theorem supported_function_body_shape:
  !tops vis args body.
    supported_function_body tops vis args body ==>
    ~supported_stmts_expr_exists expr_shape_root body
Proof
  cheat
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
  cheat
QED

Theorem package_internal_fn_shape_ok:
  !tops use_trans nkey_map target src.
    supported_program tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
         (package_internal_fn tops use_trans nkey_map F 0 src))
Proof
  cheat
QED

Theorem package_fallback_fn_shape_ok:
  !tops use_trans nkey_map target.
    supported_program tops ==>
    fallback_shape_ok
      (set_fallback_package_target target
         (package_fallback_fn tops use_trans nkey_map
            (FST (SND (SND (classify_functions tops))))))
Proof
  cheat
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
  cheat
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
