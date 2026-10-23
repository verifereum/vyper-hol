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

(* For alan, by compile_stmt_ind.  internal is IS_SOME ce_return_pc: Return
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

Theorem compile_alloc_buffer_shape:
  !size. shape_step F compiler_label (\st. T)
    (compile_alloc_buffer size) (\buf st. plain_operand st buf.buf_operand)
Proof
  qx_gen_tac `sz` >> simp[compile_alloc_buffer_def] >>
  irule shape_step_bind >>
  qexists_tac `\op st. T /\ plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`, `ALLOCA`,
    `[Lit (n2w sz)]`] shape_step_emit_op) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
       mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       jump_labels_ok_def, is_terminator_def, is_param_opcode_def,
       is_read0_opcode_def, label_positions_ok_def]
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

Theorem compile_nonreentrant_unlock_shape:
  !nkey transient view. shape_step F compiler_label (\st. T)
    (compile_nonreentrant_unlock nkey transient view) (\x st. T)
Proof
  rpt gen_tac >> Cases_on `view` >> pure_rewrite_tac[compile_nonreentrant_unlock_def, COND_CLAUSES]
  >- (irule shape_step_return >> simp[]) >>
  Cases_on `transient` >> pure_rewrite_tac[COND_CLAUSES] >> extbodies_void_end `[]`
QED

Theorem compile_nonreentrant_lock_shape:
  !nkey transient view. shape_step F compiler_label (\st. T)
    (compile_nonreentrant_lock nkey transient view) (\x st. T)
Proof
  rpt gen_tac >> Cases_on `transient` >>
  pure_rewrite_tac[compile_nonreentrant_lock_def, COND_CLAUSES] >>
  extbodies_from_true_tac >>
  extbodies_emit_bind `\cur st. EVERY (plain_operand st) [cur]` `cur`
    (extbodies_emit_bind `\locked st. EVERY (plain_operand st) [locked; cur]` `locked`
      (extbodies_emit_bind `\nl st. EVERY (plain_operand st) [nl; locked; cur]` `nl`
        (extbodies_void_bind `\u st. EVERY (plain_operand st) [nl; locked; cur]`
          (Cases_on `view` >> pure_rewrite_tac[COND_CLAUSES]
           >- (irule shape_step_return >> simp[]) >>
           extbodies_void_end `[nl; locked; cur]`))))
QED

Theorem compile_guarded_body_shape:
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
Resume compile_guarded_body_shape[statements]:
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
Resume compile_guarded_body_shape[termination]:
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\cs st. cs = st /\ T` >> conj_tac
  >- (qx_gen_tac `cs` >> BETA_TAC >> Cases_on `block_is_terminated cs` >>
      pure_asm_rewrite_tac[COND_CLAUSES]
      >- (irule shape_step_return >> simp[]) >>
      suspend "epilogue") >>
  qspec_then `\st. T` mp_tac (Q.SPECL [`F`, `compiler_label`] shape_step_comp_get) >>
  simp[]
QED
Resume compile_guarded_body_shape[epilogue]:
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
Finalise compile_guarded_body_shape

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
      irule compile_guarded_body_shape >> simp[]) >>
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
