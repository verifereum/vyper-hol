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
  exprLowering stmtLowering moduleLowering vyperCompiler compileVyper
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

Theorem expr_shape_field_member[local]:
  ~supported_fields_exists p fields /\ MEM (name,e) fields ==>
  ~supported_expr_exists p e
Proof
  simp[supported_fields_exists_every, EXISTS_MEM] >> metis_tac[pairTheory.SND]
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
           jump_labels_ok_def,
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

Theorem shape_step_emit_inst_guarded[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
  (!st id. R st /\ EVERY (label_or_plain st) ops ==>
     lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (label_or_plain st) ops) (emit_inst opc ops outs)
    (\v st. R st)
Proof
  rpt gen_tac >> strip_tac >> simp[shape_step_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`internal`, `compiler_label`, `R`, `opc`, `ops`, `outs`]
                  shape_step_emit_inst) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[shape_step_def] >> disch_then drule_all >> simp[]
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
  irule_at Any shape_step_emit_inst_guarded >>
  qexists_tac `\st. R st /\ EVERY (plain_operand st) ops` >>
  conj_tac
  >- (ho_match_mp_tac shape_stable_conj >>
      simp[shape_stable_plain_operands]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  simp[EVERY_MEM, label_or_plain_def]
QED

Theorem compile_alloc_buffer_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_alloc_buffer nbytes)
    (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  strip_tac >> simp[compile_alloc_buffer_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
  >- (mp_tac (Q.SPECL [`internal`, `compiler_label`, `R`, `ALLOCA`,
                        `[Lit (n2w nbytes)]`] shape_step_emit_op) >>
      simp[SF ETA_ss, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
           inst_shape_ok_def, label_positions_ok_def, jump_labels_ok_def,
           is_read0_opcode_def,
           is_terminator_def, is_param_opcode_def, label_or_plain_def,
           plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

Theorem compile_ptr_load_shape[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st op)
    (compile_ptr_load is_ctor loc op)
    (\v st. R st /\ plain_operand st v)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `emit_op opc [op]` >>
  mp_tac (Q.SPECL [`internal`, `R`, `opc`, `[op]`]
                  shape_step_emit_op_plain) >>
  simp[Abbr `opc`, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
       plain_operand_def]
QED

Theorem compile_ptr_store_shape[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst /\ plain_operand st v)
    (compile_ptr_store is_ctor loc dst v) (\u st. R st)
Proof
  Cases_on `loc` >> simp[compile_ptr_store_def] >> strip_tac >> (
  qmatch_goalsub_abbrev_tac `emit_void opc ops` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. R st /\ EVERY (plain_operand st) ops`, `\u st. R st`] >>
  conj_tac >- simp[] >> conj_tac >- simp[Abbr `ops`] >>
  conj_tac >- simp[] >>
  ho_match_mp_tac shape_step_emit_void_plain >>
      simp[Abbr `opc`, Abbr `ops`, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
           jump_labels_ok_def, is_read0_opcode_def, is_terminator_def,
           is_param_opcode_def, plain_operand_def])
QED

Theorem compile_copy_memory_dynamic_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst /\ plain_operand st src /\
          plain_operand st len)
    (compile_copy_memory_dynamic dst src len) (\u st. R st)
Proof
  strip_tac >> simp[compile_copy_memory_dynamic_def] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. R st /\ EVERY (plain_operand st) [dst; src; len]`, `\u st. R st`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac shape_step_emit_void_plain >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
       plain_operand_def]
QED

Theorem compile_copy_memory_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst /\ plain_operand st src)
    (compile_copy_memory dst src nbytes) (\u st. R st)
Proof
  strip_tac >> Cases_on `nbytes` >> simp[compile_copy_memory_def]
  >- (irule shape_step_return >> simp[]) >>
  mp_tac (Q.INST [`len` |-> `Lit (n2w (SUC n))`]
    compile_copy_memory_dynamic_shape) >>
  simp[compile_copy_memory_dynamic_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_with_byte_offset_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st base_op)
    (compile_with_byte_offset base_op offset) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_with_byte_offset_def] >>
  Cases_on `offset = 0` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  mp_tac (Q.SPECL [`internal`, `R`, `ADD`, `[base_op; Lit (n2w offset)]`]
    shape_step_emit_op_plain) >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
       plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

(* Consequence adaptation is shared by plain-operand primitive consumers. *)
Theorem shape_step_assume_pure[local]:
  (b ==> shape_step internal LP P m Q) ==>
  shape_step internal LP (\st. b /\ P st) m Q
Proof
  simp[shape_step_def] >> metis_tac[]
QED

val shape_opcode_tac =
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
       plain_operand_def, label_or_plain_def,
       stackPlanTypesTheory.is_label_operand_def];

fun shape_under_tac rule frame =
  irule shape_step_conseq >>
  irule_at Any rule >>
  qexists_tac frame >> simp[];

Theorem compile_bytestring_copy_len_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_bytestring_copy_len val_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  qx_gen_tac `src_len` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  qx_gen_tac `padded_len` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  qx_gen_tac `rounded` >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_store_bytestring_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst_op /\ plain_operand st val_op)
    (compile_store_bytestring val_op dst_op) (\u st. R st)
Proof
  strip_tac >> simp[compile_store_bytestring_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. (R st /\ plain_operand st dst_op /\ plain_operand st val_op) /\
                      plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_bytestring_copy_len_shape
        `\st. R st /\ plain_operand st dst_op /\ plain_operand st val_op` >>
      ho_match_mp_tac shape_stable_conj >> simp[] >>
      mp_tac (Q.SPEC `[dst_op; val_op]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `copy_len` >> simp[] >>
  shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED

Theorem compile_word_copy_loop_shape[local]:
  shape_stable R /\ load_loc <> LocCode /\ store_loc <> LocCode ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st src /\ plain_operand st dst)
    (compile_word_copy_loop src dst word_count load_loc store_loc is_ctor)
    (\u st. R st)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src; dst]` shape_stable_plain_operands) >> simp[]) >>
  simp[compile_word_copy_loop_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `cond_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\ctr st. P st /\ plain_operand st (Var ctr)` >> conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >> simp[]) >>
  qx_gen_tac `ctr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var ctr]` shape_stable_plain_operands) >> simp[]) >>
  suspend "loop_tail"
QED

Resume compile_word_copy_loop_shape[loop_tail]:
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `done_op` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> suspend "copy"
QED

Resume compile_word_copy_loop_shape[copy]:
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (Cases_on `word_scale load_loc = 1` >> simp[]
      >- (shape_under_tac shape_step_emit_op_plain `C` >>
          simp[Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
      match_mp_tac shape_step_bind >>
      qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `C` >>
          simp[Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `src_off` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. C st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_ptr_load_shape `C`) >>
  qx_gen_tac `loaded` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[SF ETA_ss] >>
     mp_tac (Q.SPEC `[loaded]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. L st /\ plain_operand st op` >> conj_tac
  >- (Cases_on `word_scale store_loc = 1` >> simp[]
      >- (shape_under_tac shape_step_emit_op_plain `L` >>
          simp[Abbr `L`, Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
      match_mp_tac shape_step_bind >>
      qexists_tac `\op st. L st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `L` >>
          simp[Abbr `L`, Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `L` >>
      simp[Abbr `L`, Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `dst_off` >> simp[] >> suspend "store_finish"
QED

Resume compile_word_copy_loop_shape[store_finish]:
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac compile_ptr_store_shape `C` >> simp[Abbr `L`]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `new_ctr` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st new_ctr` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[new_ctr]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_new_block `C` >>
  qexists_tac `compiler_label` >> simp[Abbr `C`, Abbr `P`]
QED
Finalise compile_word_copy_loop_shape

Theorem compile_storage_to_memory_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st src /\ plain_operand st dst)
    (compile_storage_to_memory src dst word_count) (\u st. R st)
Proof
  simp[compile_storage_to_memory_def] >> strip_tac >>
  irule compile_word_copy_loop_shape >> simp[]
QED

Theorem compile_transient_to_memory_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st src /\ plain_operand st dst)
    (compile_transient_to_memory src dst word_count) (\u st. R st)
Proof
  simp[compile_transient_to_memory_def] >> strip_tac >>
  irule compile_word_copy_loop_shape >> simp[]
QED

Theorem compile_ensure_in_memory_shape[local]:
  shape_stable R /\ loc <> LocCode ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st ptr_op)
    (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor)
    (\op st. R st /\ plain_operand st op)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[ptr_op]` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `loc` >> gvs[] >> simp[compile_ensure_in_memory_def]
  >- (irule shape_step_return >> simp[Abbr `P`])
  >- suspend "storage"
  >- suspend "transient"
  >> suspend "calldata"
QED

fun shape_ensure_slots_tac copy_rule =
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. P st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. B st` >> conj_tac
  >- (Cases_on `word_count = 1` >> simp[]
      >- (match_mp_tac shape_step_bind >>
          qexists_tac `\op st. B st /\ plain_operand st op` >> conj_tac
          >- (shape_under_tac shape_step_emit_op_plain `B` >>
              simp[Abbr `B`, Abbr `P`] >> shape_opcode_tac) >>
          gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `B` >>
          simp[Abbr `B`] >> shape_opcode_tac) >>
      match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. B st` >> conj_tac
      >- (shape_under_tac copy_rule `B` >> simp[Abbr `B`, Abbr `P`]) >>
      gen_tac >> simp[] >> irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `B`, Abbr `P`];

Resume compile_ensure_in_memory_shape[storage]:
  shape_ensure_slots_tac compile_storage_to_memory_shape
QED
Resume compile_ensure_in_memory_shape[transient]:
  shape_ensure_slots_tac compile_transient_to_memory_shape
QED
Resume compile_ensure_in_memory_shape[calldata]:
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `P` >>
      simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `len_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. L st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `B` >>
      simp[Abbr `B`, Abbr `L`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. B st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `B` >>
      simp[Abbr `B`] >> shape_opcode_tac) >>
  qx_gen_tac `data_ptr` >> simp[] >> suspend "calldata_copy"
QED
Resume compile_ensure_in_memory_shape[calldata_copy]:
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. D st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `D` >>
      simp[Abbr `D`, Abbr `B`, Abbr `L`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `src_data` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. B st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain
        `\st. D st /\ plain_operand st src_data` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
      simp[Abbr `D`, Abbr `B`, Abbr `L`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[Abbr `B`, Abbr `L`, Abbr `P`]
QED
Finalise compile_ensure_in_memory_shape

(* Shared control prefix of the two typed array copy generators.
   P retains the source/destination operands and any dynamic length. *)
val shape_typed_loop_start_tac =
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `cond_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ P st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `P` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\ctr st. P st /\ plain_operand st (Var ctr)` >> conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >> simp[]) >>
  qx_gen_tac `ctr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[Var ctr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[];

Theorem compile_typed_memory_shape[local]:
  (!cenv dst dst_ty src src_ty R internal.
    shape_stable R ==> shape_step internal compiler_label
      (\st. R st /\ plain_operand st dst /\ plain_operand st src)
      (compile_store_memory_typed cenv dst dst_ty src src_ty) (\u st. R st)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off R internal.
    shape_stable R ==> shape_step internal compiler_label
      (\st. R st /\ plain_operand st dst /\ plain_operand st src)
      (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)
      (\u st. R st)) /\
  (!cenv dst dst_ty src src_ty count R internal.
    shape_stable R ==> shape_step internal compiler_label
      (\st. R st /\ plain_operand st dst /\ plain_operand st src)
      (compile_copy_sarray_typed cenv dst dst_ty src src_ty count) (\u st. R st)) /\
  (!cenv dst dst_ty cap src src_ty R internal.
    shape_stable R ==> shape_step internal compiler_label
      (\st. R st /\ plain_operand st dst /\ plain_operand st src)
      (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty) (\u st. R st)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off R internal.
    shape_stable R ==> shape_step internal compiler_label
      (\st. R st /\ plain_operand st dst /\ plain_operand st src)
      (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off)
      (\u st. R st))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED
Resume compile_typed_memory_shape[fields_nil]:
  rpt strip_tac >> simp[Once compile_store_memory_typed_def] >>
  irule shape_step_return >> simp[]
QED
Resume compile_typed_memory_shape[fields_mismatch]:
  rpt strip_tac >> simp[Once compile_store_memory_typed_def] >>
  irule shape_step_return >> simp[]
QED
Resume compile_typed_memory_shape[struct_nil]:
  rpt strip_tac >> simp[Once compile_store_memory_typed_def] >>
  irule shape_step_return >> simp[]
QED
Resume compile_typed_memory_shape[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst; src]` shape_stable_plain_operands) >> simp[]) >>
  simp[Once compile_store_memory_typed_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac compile_with_byte_offset_shape `P` >> simp[Abbr `P`]) >>
  qx_gen_tac `dst_ptr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst_ptr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. D st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac compile_with_byte_offset_shape `D` >>
      simp[Abbr `D`, Abbr `P`]) >>
  qx_gen_tac `src_ptr` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. P st` >> conj_tac
  >- (irule shape_step_conseq >>
      first_x_assum (irule_at Any) >> qexists_tac `P` >>
      simp[Abbr `D`]) >>
  gen_tac >> simp[] >>
  simp[Abbr `P`] >> first_x_assum irule >> simp[]
QED
Resume compile_typed_memory_shape[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dst_ty`
  >- (simp[Once compile_store_memory_typed_def] >>
      match_mp_tac shape_step_bind >>
      qexists_tac `\op st. R st /\ plain_operand st dst /\ plain_operand st op` >>
      conj_tac
      >- (shape_under_tac shape_step_emit_op_plain
            `\st. R st /\ plain_operand st dst` >>
          conj_tac
          >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
              mp_tac (Q.SPEC `[dst]` shape_stable_plain_operands) >> simp[]) >>
          shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >>
      shape_opcode_tac) >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- (simp[Once compile_store_memory_typed_def] >>
      shape_under_tac compile_store_bytestring_shape `R`) >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      TRY (rename1 `compile_store_memory_typed cenv dst (ArrayT dt db) src (ArrayT st sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      FIRST [first_x_assum irule >> simp[],
             shape_under_tac compile_copy_memory_shape `R`]) >>
  simp[Once compile_store_memory_typed_def] >>
  shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED
Resume compile_typed_memory_shape[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >> gvs[] >>
  (qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
   `shape_stable P` by
     (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
      mp_tac (Q.SPEC `[dst; src]` shape_stable_plain_operands) >> simp[]) >>
   simp[Once compile_store_memory_typed_def] >>
   match_mp_tac shape_step_bind >>
   qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
   >- (shape_under_tac compile_with_byte_offset_shape `P` >> simp[Abbr `P`]) >>
   qx_gen_tac `dst_ptr` >> simp[] >>
   qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
   `shape_stable D` by
     (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
      mp_tac (Q.SPEC `[dst_ptr]` shape_stable_plain_operands) >> simp[]) >>
   match_mp_tac shape_step_bind >>
   qexists_tac `\op st. D st /\ plain_operand st op` >> conj_tac
   >- (shape_under_tac compile_with_byte_offset_shape `D` >>
       simp[Abbr `D`, Abbr `P`]) >>
   qx_gen_tac `src_ptr` >> simp[] >>
   match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
   >- (irule shape_step_conseq >> first_x_assum (irule_at Any) >>
       qexists_tac `P` >> simp[Abbr `D`]) >>
   gen_tac >> simp[] >> simp[Abbr `P`] >> first_x_assum irule >> simp[])
QED
Resume compile_typed_memory_shape[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
  simp[Once compile_store_memory_typed_def]
  >- (shape_under_tac compile_copy_memory_shape `R`) >>
  (IF_CASES_TAC >- gvs[]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst; src]` shape_stable_plain_operands) >> simp[]) >>
  shape_typed_loop_start_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `lt_op` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >> shape_opcode_tac) >>
  qx_gen_tac `done_op` >> simp[] >> suspend "sarray_body"
QED
Resume compile_typed_memory_shape[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label Base _ _` >>
  `shape_stable Base` by
    (simp[Abbr `Base`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst; src]` shape_stable_plain_operands) >> simp[]) >>
  simp[Once compile_store_memory_typed_def] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. Base st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `Base` >>
      simp[Abbr `Base`] >> shape_opcode_tac) >>
  qx_gen_tac `len_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. LenFrame st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `LenFrame` >>
      simp[Abbr `LenFrame`] >> shape_opcode_tac) >>
  qx_gen_tac `too_long` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. LenFrame st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `LenFrame` >> shape_opcode_tac) >>
  qx_gen_tac `ok` >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> suspend "dyn_data"
QED
Resume compile_typed_memory_shape[dyn_data]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `Base`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. LenFrame st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `Base`] >> shape_opcode_tac) >>
  qx_gen_tac `src_data` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st len_op /\
                       plain_operand st src_data /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain
        `\st. LenFrame st /\ plain_operand st src_data` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
      simp[Abbr `LenFrame`, Abbr `Base`] >> shape_opcode_tac) >>
  qx_gen_tac `dst_data` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op; src_data; dst_data]` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\ dst_ty = src_ty`
  >- (simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `P` >>
          simp[Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac compile_copy_memory_dynamic_shape `R` >>
      simp[Abbr `P`]) >>
  gvs[] >> (IF_CASES_TAC >- gvs[]) >> shape_typed_loop_start_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `lt_op` >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >> shape_opcode_tac) >>
  qx_gen_tac `done_op` >> simp[] >> suspend "dynarray_body"
QED
val shape_typed_array_offsets_tac =
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `src_off` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_off]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. SrcFrame st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `SrcFrame` >>
      simp[Abbr `SrcFrame`, Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `dst_off_op` >> simp[];

val shape_typed_array_elements_tac =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst_off_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. D st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `D` >>
      simp[Abbr `D`, Abbr `SrcFrame`, Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `src_elem` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label E _ _` >>
  `shape_stable E` by
    (simp[Abbr `E`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_elem]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. E st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `E` >>
      simp[Abbr `E`, Abbr `D`, Abbr `SrcFrame`, Abbr `C`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `dst_elem` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (irule shape_step_conseq >> first_x_assum (irule_at Any) >>
      qexists_tac `C` >> simp[Abbr `E`, Abbr `D`, Abbr `SrcFrame`]) >>
  gen_tac >> simp[];

val shape_typed_array_finish_tac =
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. C st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `C` >>
      simp[Abbr `C`] >> shape_opcode_tac) >>
  qx_gen_tac `new_ctr` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st new_ctr` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[new_ctr]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `C`, Abbr `P`];

Resume compile_typed_memory_shape[sarray_body]:
  shape_typed_array_offsets_tac >> shape_typed_array_elements_tac >>
  shape_typed_array_finish_tac
QED
Resume compile_typed_memory_shape[dynarray_body]:
  shape_typed_array_offsets_tac >> shape_typed_array_elements_tac >>
  shape_typed_array_finish_tac
QED
Finalise compile_typed_memory_shape

Theorem compile_store_memory_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st src /\ plain_operand st dst)
    (compile_store_memory cenv src dst dst_ty src_ty) (\u st. R st)
Proof
  strip_tac >> simp[compile_store_memory_def] >>
  Cases_on `is_word_type dst_ty`
  >- (simp[] >> shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac) >>
  Cases_on `is_bytestring_type dst_ty`
  >- (simp[] >> shape_under_tac compile_store_bytestring_shape `R`) >>
  Cases_on `dst_ty = src_ty` >> simp[]
  >- (shape_under_tac compile_copy_memory_shape `R`) >>
  shape_under_tac (cj 1 compile_typed_memory_shape) `R`
QED

Theorem compile_store_byte_chunks_shape[local]:
  !data_ptr bs offset R internal.
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st data_ptr)
    (compile_store_byte_chunks data_ptr bs offset) (\u st. R st)
Proof
  recInduct compile_store_byte_chunks_ind >> conj_tac
  >- (rpt strip_tac >> simp[Once compile_store_byte_chunks_def] >>
      irule shape_step_return >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_store_byte_chunks_def] >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `P` >>
      simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac) >>
  gen_tac >> simp[Abbr `P`] >> first_x_assum irule >> simp[]
QED

Theorem compile_bytelike_literal_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label R (compile_bytelike_literal bs max_len)
    (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  strip_tac >> simp[compile_bytelike_literal_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\buf st. R st /\ plain_operand st buf.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `P` >>
      simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. P st` >> conj_tac
  >- (shape_under_tac compile_store_byte_chunks_shape `P` >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `P`]
QED

val shape_name_invalid_tac =
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `\st. T` >>
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
  >- (ho_match_mp_tac compile_bytelike_literal_shape >> simp[]) >>
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

Theorem compile_clamp_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_clamp val_op ty) (\u st. R st)
Proof
  strip_tac >> Cases_on `type_bounds ty` >> simp[compile_clamp_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (match_mp_tac shape_step_bind >>
      qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `P` >>
          simp[Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\op st. P st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `P` >> shape_opcode_tac) >>
      qx_gen_tac `ge_lo` >> simp[] >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
      `shape_stable G` by
        (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[ge_lo]` shape_stable_plain_operands) >> simp[]) >>
      match_mp_tac shape_step_bind >>
      qexists_tac `\op st. G st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `G` >>
          simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\op st. G st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `G` >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
      qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `G` >>
          simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >>
      shape_opcode_tac) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED

Theorem clamp_and_return_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st res)
    (clamp_and_return res ty) (\op st. R st /\ plain_operand st op)
Proof
  strip_tac >> simp[clamp_and_return_def] >>
  match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. R st /\ plain_operand st res` >> conj_tac
  >- (shape_under_tac compile_clamp_shape `\st. R st /\ plain_operand st res` >>
      ho_match_mp_tac shape_stable_conj >> simp[] >>
      mp_tac (Q.SPEC `[res]:operand list` shape_stable_plain_operands) >> simp[]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

(* Scalar arithmetic retains the input operands and the result across checks. *)
fun shape_safe_add_sub_tac g = (
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\res st. P st /\ plain_operand st res` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `P` >>
      simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `res` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[res]:operand list` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `type_bits ty < 256` >> simp[]
  >- (shape_under_tac clamp_and_return_shape `P` >> simp[Abbr `G`, Abbr `P`]) >>
  Cases_on `is_signed_type ty` >> simp[] >> (
    match_mp_tac shape_step_bind >>
    qexists_tac `\v st. G st /\ plain_operand st v` >> conj_tac
    >- (shape_under_tac shape_step_emit_op_plain `G` >>
        simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
    qx_gen_tac `check_op` >> simp[] >>
    qmatch_goalsub_abbrev_tac `shape_step internal compiler_label H _ _` >>
    `shape_stable H` by
      (simp[Abbr `H`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
       mp_tac (Q.SPEC `[check_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
    match_mp_tac shape_step_bind >>
    qexists_tac `\v st. H st /\ plain_operand st v` >> conj_tac
    >- (shape_under_tac shape_step_emit_op_plain `H` >>
        simp[Abbr `H`, Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
    gen_tac >> simp[])
  >~ [`comp_bind (emit_op EQ [a;b]) _`]
  >- (match_mp_tac shape_step_bind >>
      qexists_tac `\v st. G st /\ plain_operand st v` >> conj_tac
      >- (shape_under_tac shape_step_emit_op_plain `G` >>
          simp[Abbr `H`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
      qexists_tac `\u st. G st` >> conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `G` >> shape_opcode_tac) >>
      gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `G` >> simp[Abbr `H`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) g;

Theorem compile_safe_add_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_add x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_add_def] >> shape_safe_add_sub_tac
QED

Theorem compile_safe_sub_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_sub x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_sub_def] >> shape_safe_add_sub_tac
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

Theorem compile_safe_mod_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_mod x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_mod_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `yz` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ynz` all_tac >>
  shape_scalar_assert_tac `P` >>
  Cases_on `is_signed_type ty` >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_safe_decimal_div_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_decimal_div x y divisor ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_decimal_div_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `scaled` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[scaled]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. G st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `G` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `yz` >> simp[] >>
  shape_scalar_emit_bind_tac `G` `ynz` all_tac >>
  shape_scalar_assert_tac `G` >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac shape_step_emit_op_plain `G` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> ho_match_mp_tac clamp_and_return_shape >> simp[]
QED

Theorem compile_safe_div_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_div x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_div_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `yz` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ynz` all_tac >>
  shape_scalar_assert_tac `P` >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (shape_scalar_emit_bind_tac `P` `res` (simp[Abbr `P`]) >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
      `shape_stable G` by
        (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[res]:operand list` shape_stable_plain_operands) >> simp[]) >>
      Cases_on `type_bits ty = 256` >> simp[]
      >- (shape_scalar_emit_bind_tac `G` `xmin` (simp[Abbr `G`, Abbr `P`]) >>
          qmatch_goalsub_abbrev_tac `shape_step internal compiler_label H _ _` >>
          `shape_stable H` by
            (simp[Abbr `H`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
             mp_tac (Q.SPEC `[xmin]:operand list` shape_stable_plain_operands) >> simp[]) >>
          shape_scalar_emit_bind_tac `H` `ny` (simp[Abbr `H`, Abbr `G`, Abbr `P`]) >>
          shape_scalar_emit_bind_tac `H` `yn1` all_tac >>
          shape_scalar_emit_bind_tac `G` `bad` (simp[Abbr `H`]) >>
          shape_scalar_emit_bind_tac `G` `ok_op` all_tac >>
          shape_scalar_assert_tac `G` >>
          irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) >>
      Cases_on `type_bits ty < 256` >> simp[]
      >- (shape_under_tac clamp_and_return_shape `P` >> simp[Abbr `G`, Abbr `P`]) >>
      irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_mul_overflow_check_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [x;y;res])
    (compile_mul_overflow_check x y res is_signed bits) (\u st. R st)
Proof
  strip_tac >> simp[compile_mul_overflow_check_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y;res]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `is_signed` >> simp[] >>
      shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  qx_gen_tac `div_res` >> simp[] >>
    shape_scalar_emit_bind_tac `P` `div_ok` (simp[Abbr `P`]) >>
    qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
    `shape_stable G` by
      (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
       mp_tac (Q.SPEC `[div_ok]:operand list` shape_stable_plain_operands) >> simp[]) >>
    shape_scalar_emit_bind_tac `G` `yz` (simp[Abbr `G`, Abbr `P`]) >>
    shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `G`]) >>
    qmatch_goalsub_abbrev_tac `shape_step internal compiler_label H _ _` >>
    `shape_stable H` by
      (simp[Abbr `H`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
       mp_tac (Q.SPEC `[ok_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `is_signed /\ bits = 256` >> simp[]
      >- (shape_scalar_emit_bind_tac `H` `xmin` (simp[Abbr `H`, Abbr `P`]) >>
          qmatch_goalsub_abbrev_tac `shape_step internal compiler_label J _ _` >>
          `shape_stable J` by
            (simp[Abbr `J`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
             mp_tac (Q.SPEC `[xmin]:operand list` shape_stable_plain_operands) >> simp[]) >>
          shape_scalar_emit_bind_tac `J` `ny` (simp[Abbr `J`, Abbr `H`, Abbr `P`]) >>
          shape_scalar_emit_bind_tac `J` `yn1` all_tac >>
          shape_scalar_emit_bind_tac `H` `special` (simp[Abbr `J`]) >>
          shape_scalar_emit_bind_tac `H` `nspecial` all_tac >>
          shape_under_tac shape_step_emit_op_plain `H` >>
          simp[Abbr `H`, Abbr `P`] >> shape_opcode_tac) >>
      irule shape_step_return >> simp[Abbr `H`, Abbr `P`]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac
QED

Theorem compile_safe_mul_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_mul x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_mul_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `res` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[res]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
  >- (Cases_on `128 < type_bits ty` >> simp[]
      >- (shape_under_tac compile_mul_overflow_check_shape `G` >> simp[Abbr `G`, Abbr `P`]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. R st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `is_decimal_type ty` >> simp[]
      >- (Cases_on `is_signed_type ty` >> simp[] >>
          shape_under_tac shape_step_emit_op_plain `G` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac) >>
      irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) >>
  gen_tac >> simp[] >> Cases_on `type_bits ty < 256 \/ is_decimal_type ty` >> simp[]
  >- (ho_match_mp_tac clamp_and_return_shape >> simp[]) >>
  irule shape_step_return >> simp[]
QED

Theorem wrap_truncate_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st res)
    (wrap_truncate res ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[wrap_truncate_def] >> Cases_on `type_bits ty < 256` >> simp[]
  >- (Cases_on `is_signed_type ty` >> simp[] >>
      shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac) >>
  irule shape_step_return >> simp[]
QED

Theorem compile_compare_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_compare op x y ty) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `op` >> simp[compile_compare_def] >>
  TRY (rename1 `shape_step _ _ _ (comp_ignore_bind (emit_inst INVALID [] []) _) _` >>
       match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. R st` >> conj_tac
       >- (shape_under_tac shape_step_emit_inst_guarded `R` >> shape_opcode_tac) >>
       gen_tac >> simp[] >> irule shape_step_return >>
       simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >> NO_TAC) >>
  Cases_on `is_uint256 ty` >> simp[] >>
  TRY (rename1 `shape_step _ _ _ (emit_op _ _) _` >>
       shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac >> NO_TAC) >>
  shape_scalar_emit_bind_tac `R` `cmp` all_tac >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

val shape_pow_assert_exp_tac =
  shape_scalar_assert_tac `P` >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac;

val shape_pow_upper_tac =
  shape_scalar_emit_bind_tac `P` `above_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` all_tac >> shape_pow_assert_exp_tac;

Theorem compile_safe_pow_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_safe_pow x y ty base_literal exp_literal)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_safe_pow_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `base_literal` >> simp[]
  >- (Cases_on `exp_literal` >> simp[]
      >- (shape_scalar_emit_bind_tac `P` `res` (simp[Abbr `P`]) >>
          qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
          `shape_stable G` by
            (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
             mp_tac (Q.SPEC `[res]:operand list` shape_stable_plain_operands) >> simp[]) >>
          match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. G st` >> conj_tac
          >- (shape_under_tac compile_clamp_shape `G` >> simp[Abbr `G`]) >>
          gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `G`, Abbr `P`]) >>
      IF_CASES_TAC >> simp[]
      >- shape_pow_assert_exp_tac >>
      Cases_on `is_signed_type ty` >> simp[]
      >- (shape_scalar_emit_bind_tac `P` `below_op` (simp[Abbr `P`]) >>
          shape_scalar_emit_bind_tac `P` `ge_lower` all_tac >>
          qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
          `shape_stable G` by
            (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
             mp_tac (Q.SPEC `[ge_lower]:operand list` shape_stable_plain_operands) >> simp[]) >>
          shape_scalar_emit_bind_tac `G` `above_op` (simp[Abbr `G`, Abbr `P`]) >>
          shape_scalar_emit_bind_tac `G` `le_upper` all_tac >>
          shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `G`]) >> shape_pow_assert_exp_tac) >>
      shape_pow_upper_tac) >>
  IF_CASES_TAC >> simp[]
  >- (match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
      >- (Cases_on `is_signed_type ty` >> simp[]
          >- (shape_scalar_emit_bind_tac `P` `negative_op` (simp[Abbr `P`]) >>
              shape_under_tac shape_step_emit_op_plain `P` >> shape_opcode_tac) >>
          irule shape_step_return >> shape_opcode_tac) >>
      gen_tac >> simp[] >> shape_pow_assert_exp_tac) >>
  shape_pow_upper_tac
QED

Theorem compile_select_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [cond_op;then_op;else_op])
    (compile_select cond_op then_op else_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[builtinSimpleTheory.compile_select_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[cond_op;then_op;else_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `diff` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `scaled` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac
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

Theorem compile_binop_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st x /\ plain_operand st y)
    (compile_binop op x y ty base_literal exp_literal) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `op` >>
  simp[compile_binop_def, compile_safe_add_shape, compile_safe_sub_shape,
       compile_safe_mul_shape, compile_safe_mod_shape, compile_safe_pow_shape,
       compile_compare_shape] >>
  TRY (rename1 `shape_step _ _ _ (if is_decimal_type ty then _ else _) _` >>
       Cases_on `is_decimal_type ty` >> simp[compile_safe_decimal_div_shape,
                                             compile_safe_div_shape] >> NO_TAC) >>
  TRY (rename1 `shape_step _ _ _ (comp_ignore_bind (emit_inst INVALID [] []) _) _` >>
       match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. R st` >> conj_tac
       >- (shape_under_tac shape_step_emit_inst_guarded `R` >> shape_opcode_tac) >>
       gen_tac >> simp[] >> irule shape_step_return >>
       simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >> NO_TAC) >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >> simp[] >>
  TRY (rename1 `shape_step _ _ _ (emit_op _ _) _` >>
       shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac >> NO_TAC) >>
  TRY (rename1 `shape_step _ _ _ (comp_bind _ (\res. wrap_truncate res ty)) _` >>
       shape_scalar_emit_bind_tac `R` `res` all_tac >>
       ho_match_mp_tac wrap_truncate_shape >> simp[] >> NO_TAC) >>
  TRY (rename1 `shape_step _ _ _ (comp_bind _ (\res. compile_select res x y)) _` >>
       qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
       `shape_stable P` by
         (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[x;y]:operand list` shape_stable_plain_operands) >> simp[]) >>
       shape_scalar_emit_bind_tac `P` `cmp` (simp[Abbr `P`]) >>
       shape_under_tac compile_select_shape `R` >> simp[Abbr `P`] >> NO_TAC) >>
  shape_scalar_emit_bind_tac `R` `inter_op` all_tac >>
  TRY (rename1 `shape_step _ _ _ (emit_op _ _) _` >>
       shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac >> NO_TAC) >>
  shape_scalar_emit_bind_tac `R` `z` all_tac >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
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

Theorem compile_type_convert_shape[local]:
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
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
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

Finalise compile_type_convert_shape

(* Min/max keep both source operands live through the comparison. *)
fun shape_builtin_minmax_tac def =
  strip_tac >> Cases_on `use_unsigned` >> simp[def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[a;b]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `cmp` (simp[Abbr `P`]) >>
  shape_under_tac compile_select_shape `R` >> simp[Abbr `P`];

Theorem compile_builtin_min_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st a /\ plain_operand st b)
    (compile_builtin_min a b use_unsigned) (\v st. R st /\ plain_operand st v)
Proof
  shape_builtin_minmax_tac builtinSimpleTheory.compile_builtin_min_def
QED

Theorem compile_builtin_max_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st a /\ plain_operand st b)
    (compile_builtin_max a b use_unsigned) (\v st. R st /\ plain_operand st v)
Proof
  shape_builtin_minmax_tac builtinSimpleTheory.compile_builtin_max_def
QED

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
  shape_under_tac compile_select_shape `R` >> simp[Abbr `H`, Abbr `G`, Abbr `P`]
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
  >- (shape_under_tac compile_select_shape `R` >> simp[Abbr `G`, Abbr `P`]) >>
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
  simp[builtinSimpleTheory.compile_builtin_len_def, compile_ptr_load_shape]
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
  >- (irule compile_alloc_buffer_shape >> simp[]) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >>
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

(* ABI validators preserve the value whose canonical form they check. *)
val shape_abi_scalar_clamp_tac =
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[v]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `canonical_op` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `ok_op` (simp[Abbr `P`]) >>
  shape_under_tac shape_step_emit_void_plain `P` >> shape_opcode_tac;

Theorem compile_abi_int_clamp_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_int_clamp v bits signed) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `signed` >> simp[abiEncoderTheory.compile_abi_int_clamp_def] >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_abi_bytes_clamp_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_bytes_clamp v m) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_abi_bytes_clamp_def] >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_abi_clamp_basetype_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_abi_clamp_basetype v clamp) (\u st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `clamp` >>
  simp[abiEncoderTheory.compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_shape, compile_abi_bytes_clamp_shape]
  >- (irule shape_step_return >> simp[]) >>
  shape_abi_scalar_clamp_tac
QED

Theorem compile_get_element_ptr_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st v)
    (compile_get_element_ptr v offset) (\w st. R st /\ plain_operand st w)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_get_element_ptr_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_abi_zero_pad_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [bytez;len_op;count_op])
    (compile_abi_zero_pad bytez len_op count_op) (\u st. R st)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_abi_zero_pad_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[bytez;len_op;count_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `data_end` (simp[Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `pad_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[pad_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `cds` all_tac >>
  shape_under_tac shape_step_emit_void_plain `R` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_get_dynarray_elem_ptr_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st parent_op /\ plain_operand st idx_op)
    (compile_get_dynarray_elem_ptr parent_op idx_op elem_sz)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_get_dynarray_elem_ptr_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[parent_op;idx_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `data_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label G _ _` >>
  `shape_stable G` by
    (simp[Abbr `G`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `G` `offset_op` (simp[Abbr `G`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `G`, Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_abi_encode_static_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst /\ plain_operand st src)
    (compile_abi_encode_static dst src) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[abiEncoderTheory.compile_abi_encode_static_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `val_op` (simp[Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. R st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `R` >> simp[Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> shape_opcode_tac
QED

Theorem compile_abi_encode_static_info_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ plain_operand st dst /\ plain_operand st src)
    (compile_abi_encode_static_info dst src info) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> Cases_on `info` >>
  simp[abiEncoderTheory.compile_abi_encode_static_info_def, compile_abi_encode_static_shape] >>
  TRY (rename1 `shape_step _ _ _ (comp_return _) _` >>
       irule shape_step_return >> shape_opcode_tac >> NO_TAC) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. R st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> shape_opcode_tac
QED

Theorem compile_abi_encode_dyn_static_loop_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [dst;src;len_op])
    (compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src;len_op]` shape_stable_plain_operands) >> simp[]) >>
  simp[abiEncoderTheory.compile_abi_encode_dyn_static_loop_def] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `idx_buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `hdr_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  suspend "header"
QED

Resume compile_abi_encode_dyn_static_loop_shape[header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `C` `idx` (simp[Abbr `C`]) >>
  shape_scalar_emit_bind_tac `C` `cmp_op` (simp[Abbr `C`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `C` `done_op` all_tac >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> suspend "body"
QED

Resume compile_abi_encode_dyn_static_loop_shape[body]:
  shape_scalar_emit_bind_tac `C` `idx_op` (simp[Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label IdxFrame _ _` >>
  `shape_stable IdxFrame` by
    (simp[Abbr `IdxFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `IdxFrame` `src_data` (simp[Abbr `IdxFrame`, Abbr `C`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `SrcFrame` `src_off` (simp[Abbr `SrcFrame`, Abbr `IdxFrame`]) >>
  shape_scalar_emit_bind_tac `IdxFrame` `child_src` (simp[Abbr `SrcFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ChildFrame _ _` >>
  `shape_stable ChildFrame` by
    (simp[Abbr `ChildFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[child_src]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ChildFrame` `dst_data` (simp[Abbr `ChildFrame`, Abbr `IdxFrame`, Abbr `C`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label DstFrame _ _` >>
  `shape_stable DstFrame` by
    (simp[Abbr `DstFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `DstFrame` `static_off` (simp[Abbr `DstFrame`, Abbr `ChildFrame`, Abbr `IdxFrame`]) >>
  shape_scalar_emit_bind_tac `ChildFrame` `child_dst` (simp[Abbr `DstFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. IdxFrame st` >> conj_tac
  >- (shape_under_tac compile_abi_encode_static_info_shape `IdxFrame` >> simp[Abbr `ChildFrame`]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `C` `new_idx` (simp[Abbr `IdxFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `R` `len_exit` (simp[Abbr `C`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `R` `payload_size` all_tac >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED
Finalise compile_abi_encode_dyn_static_loop_shape

Theorem compile_abi_encode_shape[local]:
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
  ho_match_mp_tac abiEncoderTheory.compile_abi_encode_child_ind >>
  conj_tac >- suspend "child" >>
  conj_tac
  >- (rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
      shape_under_tac compile_abi_encode_static_shape `R`) >>
  conj_tac >- suspend "bytes" >>
  conj_tac
  >- (rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
      match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. R st` >> conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `R` >> shape_opcode_tac) >>
      gen_tac >> simp[] >> irule shape_step_return >> shape_opcode_tac) >>
  conj_tac >- suspend "array" >>
  conj_tac
  >- (rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
      irule shape_step_return >> shape_opcode_tac) >>
  conj_tac >- suspend "complex" >>
  conj_tac
  >- (rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
      irule shape_step_return >> shape_opcode_tac) >>
  conj_tac >- suspend "elements" >>
  suspend "dynamic"
QED

Resume compile_abi_encode_shape[child]:
  rpt strip_tac >>
  reverse (Cases_on `is_dyn`) >> gvs[]
  >- (simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
      `shape_stable P` by
        (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[dst;child_ptr;dyn_ptr]` shape_stable_plain_operands) >> simp[]) >>
      shape_scalar_emit_bind_tac `P` `static_op` (simp[Abbr `P`]) >>
      first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]) >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;child_ptr;dyn_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `static_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label StaticFrame _ _` >>
  `shape_stable StaticFrame` by
    (simp[Abbr `StaticFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[static_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `StaticFrame` `dyn_ofst` (simp[Abbr `StaticFrame`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label OffsetFrame _ _` >>
  `shape_stable OffsetFrame` by
    (simp[Abbr `OffsetFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dyn_ofst]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `OffsetFrame` `child_dst` (simp[Abbr `OffsetFrame`, Abbr `StaticFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. OffsetFrame st /\ plain_operand st v` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `OffsetFrame`) >>
      simp[Abbr `OffsetFrame`, Abbr `StaticFrame`, Abbr `P`]) >>
  qx_gen_tac `child_len` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[child_len]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `StaticFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `LenFrame` `new_dyn` (simp[Abbr `LenFrame`, Abbr `OffsetFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `StaticFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `StaticFrame`, Abbr `P`]
QED

Resume compile_abi_encode_shape[bytes]:
  rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `len_op` (simp[Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LenFrame` `ceil_arg` (simp[Abbr `LenFrame`]) >>
  shape_scalar_emit_bind_tac `LenFrame` `last_offset` all_tac >>
  shape_scalar_emit_bind_tac `LenFrame` `last_ptr` (simp[Abbr `LenFrame`, Abbr `P`]) >>
  shape_scalar_assert_tac `LenFrame` >>
  shape_scalar_emit_bind_tac `LenFrame` `copy_len` (simp[Abbr `LenFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `R` `ceil_arg2` (simp[Abbr `LenFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `R` `rounded_len` all_tac >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED
Resume compile_abi_encode_shape[array]:
  rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `parent_buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ParentFrame _ _` >>
  `shape_stable ParentFrame` by
    (simp[Abbr `ParentFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[parent_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. ParentFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `ParentFrame` >>
      simp[Abbr `ParentFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `ParentFrame` `len_op` (simp[Abbr `ParentFrame`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >>
      simp[Abbr `LenFrame`, Abbr `ParentFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\v st. ParentFrame st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >- (shape_scalar_emit_bind_tac `LenFrame` `dst_data` (simp[Abbr `LenFrame`, Abbr `ParentFrame`, Abbr `P`]) >>
          first_assum (fn th => shape_under_tac th `ParentFrame`) >>
          simp[Abbr `LenFrame`, Abbr `ParentFrame`, Abbr `P`]) >>
      shape_under_tac compile_abi_encode_dyn_static_loop_shape `ParentFrame` >>
      simp[Abbr `LenFrame`, Abbr `ParentFrame`, Abbr `P`]) >>
  qx_gen_tac `encoded_size` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SizeFrame _ _` >>
  `shape_stable SizeFrame` by
    (simp[Abbr `SizeFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[encoded_size]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `SizeFrame` `parent_dyn` (simp[Abbr `SizeFrame`, Abbr `ParentFrame`]) >>
  shape_scalar_emit_bind_tac `ParentFrame` `new_parent_dyn` (simp[Abbr `SizeFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. ParentFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `ParentFrame` >> simp[Abbr `ParentFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `ParentFrame`, Abbr `P`] >> shape_opcode_tac
QED
Resume compile_abi_encode_shape[complex]:
  rpt strip_tac >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  IF_CASES_TAC
  >- (gnvs[] >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
      `shape_stable P` by
        (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[dst;src]` shape_stable_plain_operands) >> simp[]) >>
      match_mp_tac shape_step_bind >>
      qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
      >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
      qx_gen_tac `dyn_buf` >> simp[] >>
      qmatch_goalsub_abbrev_tac `shape_step internal compiler_label BufFrame _ _` >>
      `shape_stable BufFrame` by
        (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
         mp_tac (Q.SPEC `[dyn_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
      match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
      >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
      gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
      qexists_tac `\u st. BufFrame st` >> conj_tac
      >- (qpat_x_assum `!b R' i. _` (qspec_then `dyn_buf` assume_tac) >>
          first_assum (fn th => shape_under_tac th `BufFrame`) >> simp[Abbr `BufFrame`, Abbr `P`]) >>
      gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >>
      simp[Abbr `BufFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gvs[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. R st` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `R`) >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> shape_opcode_tac
QED
Resume compile_abi_encode_shape[elements]:
  rpt strip_tac >> simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src;dyn_ptr]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `P` `elem_src` (simp[Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. P st` >> conj_tac
  >- (qpat_assum `!cp R' i. _` (fn th => shape_under_tac th `P`) >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >>
  qpat_x_assum `!R i. _` (mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_SYM]) >>
  disch_then (fn th => shape_under_tac th `R`) >> simp[Abbr `P`]
QED
Resume compile_abi_encode_shape[dynamic]:
  rpt strip_tac >> gvs[] >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src;len_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `idx_buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label IdxFrame _ _` >>
  `shape_stable IdxFrame` by
    (simp[Abbr `IdxFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. IdxFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `IdxFrame` >> simp[Abbr `IdxFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind >>
  qexists_tac `\b st. IdxFrame st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[SF ETA_ss]) >>
  qx_gen_tac `dyn_buf` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label C _ _` >>
  `shape_stable C` by
    (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dyn_buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `C` `init_dyn` (simp[Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `hdr_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >>
      qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  suspend "dynamic_header"
QED
Resume compile_abi_encode_shape[dynamic_header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `C` `idx` (simp[Abbr `C`, Abbr `IdxFrame`]) >>
  shape_scalar_emit_bind_tac `C` `cmp_op` (simp[Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `C` `done_op` all_tac >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded
        `\st. C st /\ plain_operand st done_op` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[done_op]` shape_stable_plain_operands) >> simp[]) >>
      shape_opcode_tac >> rpt strip_tac >> gvs[jump_label_ok_def] >>
      gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> suspend "dynamic_body"
QED

Resume compile_abi_encode_shape[dynamic_body]:
  shape_scalar_emit_bind_tac `C` `idx_op` (simp[Abbr `C`, Abbr `IdxFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LoopFrame _ _` >>
  `shape_stable LoopFrame` by
    (simp[Abbr `LoopFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[idx_op]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LoopFrame` `src_data` (simp[Abbr `LoopFrame`, Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label SrcFrame _ _` >>
  `shape_stable SrcFrame` by
    (simp[Abbr `SrcFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[src_data]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `SrcFrame` `src_off` (simp[Abbr `SrcFrame`, Abbr `LoopFrame`]) >>
  shape_scalar_emit_bind_tac `LoopFrame` `child_src` (simp[Abbr `SrcFrame`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label ChildFrame _ _` >>
  `shape_stable ChildFrame` by
    (simp[Abbr `ChildFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[child_src]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `ChildFrame` `dyn_ofst` (simp[Abbr `ChildFrame`, Abbr `LoopFrame`, Abbr `C`]) >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label OffsetFrame _ _` >>
  `shape_stable OffsetFrame` by
    (simp[Abbr `OffsetFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dyn_ofst]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `OffsetFrame` `child_dst` (simp[Abbr `OffsetFrame`, Abbr `ChildFrame`, Abbr `LoopFrame`, Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. OffsetFrame st /\ plain_operand st v` >> conj_tac
  >- (first_assum (fn th => shape_under_tac th `OffsetFrame`) >> simp[Abbr `OffsetFrame`, Abbr `ChildFrame`]) >>
  qx_gen_tac `child_len` >> simp[] >>
  suspend "dynamic_finish"
QED

Resume compile_abi_encode_shape[dynamic_finish]:
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label LenFrame _ _` >>
  `shape_stable LenFrame` by
    (simp[Abbr `LenFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[child_len]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `LenFrame` `head_off` (simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `ChildFrame`, Abbr `LoopFrame`]) >>
  shape_scalar_emit_bind_tac `LenFrame` `head_pos` (simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `ChildFrame`, Abbr `LoopFrame`, Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LenFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LenFrame` >> simp[Abbr `LenFrame`, Abbr `OffsetFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `LoopFrame` `new_dyn` (simp[Abbr `LenFrame`, Abbr `OffsetFrame`, Abbr `ChildFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. LoopFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `LoopFrame` >> simp[Abbr `LoopFrame`, Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `C` `new_idx` (simp[Abbr `LoopFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`, Abbr `IdxFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `R` `final_dyn` (simp[Abbr `C`, Abbr `IdxFrame`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED
Finalise compile_abi_encode_shape

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
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `out_buf` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. v = out_buf.buf_operand /\ (P st /\ plain_operand st v)` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `buf_op` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >> gvs[] >>
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
  >- (shape_under_tac (cj 2 compile_abi_encode_shape) `BufFrame` >> simp[Abbr `DataFrame`, Abbr `BufFrame`, Abbr `P`]) >>
  qx_gen_tac `encoded_len` >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (Cases_on `method_id_opt` >> simp[]
      >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
      shape_scalar_emit_bind_tac `BufFrame` `total_len` all_tac >>
      shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `BufFrame`, Abbr `P`]
QED

Theorem compile_getelemptr_abi_shape[local]:
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

Theorem compile_abi_decode_dyn_elem_ptr_shape[local]:
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
Theorem compile_abi_decode_shape[local]:
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

Resume compile_abi_decode_shape[primitive]:
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
  >- (ho_match_mp_tac compile_abi_clamp_basetype_shape >> simp[]) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_void_plain `R` >>
  simp[Abbr `P`] >> shape_opcode_tac
QED

Resume compile_abi_decode_shape[bytes]:
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
Resume compile_abi_decode_shape[array]:
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
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[SF ETA_ss]) >>
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
Resume compile_abi_decode_shape[complex]:
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
Resume compile_abi_decode_shape[elements]:
  rpt strip_tac >> gvs[] >> simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[dst;src_op;hi_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_getelemptr_abi_shape `P` >> simp[Abbr `P`]) >>
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
Resume compile_abi_decode_shape[dynamic]:
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
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `body_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\l st. compiler_label l /\ C st` >> conj_tac
  >- (shape_under_tac shape_step_fresh_label `C` >> qexists_tac `compiler_label` >> simp[]) >>
  qx_gen_tac `exit_lbl` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >>
  suspend "decode_header"
QED
Resume compile_abi_decode_shape[decode_header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
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
  >- (shape_under_tac shape_step_emit_inst_guarded
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
Resume compile_abi_decode_shape[decode_body]:
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
      >- (shape_under_tac compile_abi_decode_dyn_elem_ptr_shape `LoopFrame` >>
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
Resume compile_abi_decode_shape[decode_finish]:
  shape_scalar_emit_bind_tac `C` `new_i` (simp[Abbr `LoopFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `C` >> simp[Abbr `C`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >>
      shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_ignore_bind >>
  qexists_tac `\u st. C st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[Abbr `C`]
QED
Finalise compile_abi_decode_shape

Theorem lower_abi_decode_shape[local]:
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
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[SF ETA_ss]) >>
  qx_gen_tac `out_buf_alloc` >> simp[] >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\v st. v = out_buf_alloc.buf_operand /\ (DataFrame st /\ plain_operand st v)` >> conj_tac
  >- (irule shape_step_return >> simp[]) >>
  qx_gen_tac `out_buf` >> simp[] >>
  ho_match_mp_tac shape_step_assume_pure >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label BufFrame _ _` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[out_buf_alloc.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `BufFrame` `hi_op` (simp[Abbr `BufFrame`, Abbr `DataFrame`, Abbr `LenFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac (cj 1 compile_abi_decode_shape) `BufFrame` >>
      simp[Abbr `BufFrame`, Abbr `DataFrame`]) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[Abbr `BufFrame`, Abbr `DataFrame`, Abbr `LenFrame`, Abbr `P`]
QED
Finalise lower_abi_decode_shape

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
  >- (shape_under_tac compile_ptr_load_shape frame >> simp[]) >>
  Cases_on `locptr.ptr_location` >> gvs[]
  >- (irule shape_step_return >> simp[]) >>
  shape_under_tac compile_ensure_in_memory_shape frame >> simp[];

Theorem lower_value_shape[local]:
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

(* For alan, by compile_expr_ind; one case per compile_expr_body clause and
   builtin.  The builtin families (abiEncoder, builtin*, context copy loops)
   are plain shape_step facts under plain operands.  Under value_shape_ok no
   value is in LocCode, so DLOAD/DLOADBYTES are unreachable; GAS is emitted
   only as the gas operand of the call right after it. *)
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
  >- (shape_under_tac lower_value_shape `P` >> simp[Abbr `P`]) >>
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

Theorem compile_concat_shape[local]:
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
  Cases_on `infos` >> simp[compile_concat_def]
  >- (irule shape_step_return >> simp[]) >>
  PairCases_on `h'` >> simp[compile_concat_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[data_ptr;offset_op]` shape_stable_plain_operands) >> simp[]) >>
  IF_CASES_TAC >- suspend "bytestring" >> suspend "fixed"
QED
Resume compile_concat_shape[bytestring]:
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac lower_value_shape `P` >> simp[Abbr `P`]) >>
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
  >- (shape_under_tac lower_value_shape `P` >> simp[Abbr `P`]) >>
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
Finalise compile_concat_shape

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
  >- (shape_under_tac compile_store_memory_shape `P` >> simp[Abbr `P`]) >>
  gen_tac >> simp[] >> first_assum (fn th => shape_under_tac th `R`) >> simp[Abbr `P`];

Theorem compile_make_tuple_shape[local]:
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
Finalise compile_make_tuple_shape

Theorem compile_make_array_elems_shape[local]:
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
Finalise compile_make_array_elems_shape

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

Theorem compile_struct_lit_shape[local]:
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
Finalise compile_struct_lit_shape

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

Theorem compile_target_base_shape[local]:
  !target. cenv_shape_ok st cenv ==> plain_operand st (compile_target_base cenv target)
Proof
  Induct >> simp[compile_target_base_def] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `FLOOKUP cenv.ce_vars var_name` >>
  Cases_on `FLOOKUP cenv.ce_vars var_name` >> simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  rename1 `FLOOKUP cenv.ce_vars var_name = SOME loc` >>
  drule_all cenv_lookup_shape >> Cases_on `loc` >>
  simp[loc_shape_ok_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_tuple_subscript_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st base_op)
    (compile_tuple_subscript base_op offset) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_tuple_subscript_def] >>
  shape_under_tac shape_step_emit_op_plain `R` >> shape_opcode_tac
QED

Theorem compile_mapping_subscript_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [base_slot; key_op])
    (compile_mapping_subscript base_slot key_op) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_mapping_subscript_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[base_slot;key_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >>
  qexists_tac `\b st. P st /\ plain_operand st b.buf_operand` >> conj_tac
  >- (ho_match_mp_tac compile_alloc_buffer_shape >> simp[]) >>
  qx_gen_tac `scratch` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label BufFrame _ _` >>
  `shape_stable BufFrame` by
    (simp[Abbr `BufFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[scratch.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_scalar_emit_bind_tac `BufFrame` `key_ptr` (simp[Abbr `BufFrame`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. BufFrame st` >> conj_tac
  >- (shape_under_tac shape_step_emit_void_plain `BufFrame` >> simp[Abbr `BufFrame`, Abbr `P`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >> shape_under_tac shape_step_emit_op_plain `R` >>
  simp[Abbr `BufFrame`, Abbr `P`] >> shape_opcode_tac
QED

Theorem compile_array_subscript_shape[local]:
  shape_stable R /\ MEM load_opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==>
  shape_step internal compiler_label
    (\st. R st /\ EVERY (plain_operand st) [base_op; idx_op])
    (compile_array_subscript base_op idx_op dynamic_array static_count
       scale elem_size is_signed_idx load_opc)
    (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >> simp[compile_array_subscript_def] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[base_op;idx_op]` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `dynamic_array` >> simp[]
      >- (shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >>
          gvs[] >> shape_opcode_tac) >>
      irule shape_step_return >> shape_opcode_tac) >>
  qx_gen_tac `len_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label L _ _` >>
  `shape_stable L` by
    (simp[Abbr `L`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[len_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. L st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `is_signed_idx` >> simp[]
      >- (shape_under_tac shape_step_emit_op_plain `L` >> simp[Abbr `L`, Abbr `P`] >> shape_opcode_tac) >>
      irule shape_step_return >> shape_opcode_tac) >>
  qx_gen_tac `neg_op` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label N _ _` >>
  `shape_stable N` by
    (simp[Abbr `N`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[neg_op]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `N` `oob` (simp[Abbr `N`, Abbr `L`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `N` `not_oob` all_tac >>
  shape_scalar_emit_bind_tac `P` `invalid` (simp[Abbr `N`, Abbr `L`, Abbr `P`]) >>
  shape_scalar_emit_bind_tac `P` `valid` all_tac >>
  shape_scalar_assert_tac `P` >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. P st /\ plain_operand st v` >> conj_tac
  >- (Cases_on `dynamic_array` >> simp[]
      >- (shape_under_tac shape_step_emit_op_plain `P` >> simp[Abbr `P`] >> shape_opcode_tac) >>
      irule shape_step_return >> simp[Abbr `P`]) >>
  qx_gen_tac `data_ptr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step internal compiler_label D _ _` >>
  `shape_stable D` by
    (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]:operand list` shape_stable_plain_operands) >> simp[]) >>
  shape_scalar_emit_bind_tac `D` `offset_op` (simp[Abbr `D`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `D`, Abbr `P`] >> shape_opcode_tac
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


Theorem compile_acc_shape[local]:
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
  >- (ho_match_mp_tac lower_value_shape >> simp[])
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
   ho_match_mp_tac lower_value_shape >> simp[])
QED
Resume compile_acc_shape[invalid]:
  irule shape_step_uncurry >> qexists_tac `\u st. R st` >> conj_tac
  >- (gen_tac >> simp[shape_step_def, shape_extends_refl] >> shape_opcode_tac) >>
  shape_under_tac shape_step_emit_inst `R` >> shape_opcode_tac >>
  qexists_tac `compiler_label` >> simp[]
QED
Finalise compile_acc_shape

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
      >- (shape_under_tac compile_alloc_buffer_shape `\st. R st /\ plain_operand st key_op` >>
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
  >- (shape_under_tac lower_value_shape `\st. cenv_shape_ok st cenv /\ value_shape_ok st base_vv` >> simp[]) >>
  qx_gen_tac `idx_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_array_subscript_shape `\st. cenv_shape_ok st cenv` >>
      simp[cenv_shape_ok_stable] >> conj_tac
      >- (Cases_on `infer_array_location cenv base_e` >> simp[]) >>
      Cases_on `base_vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, mk_ptr_def] >> rpt strip_tac >>
  drule infer_array_location_shape >> disch_then (qspec_then `base_e` mp_tac) >> simp[];

Theorem compile_subscript_shape[local]:
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
  >- (shape_under_tac lower_value_shape `\st. T` >> simp[shape_stable_def]) >>
  qx_gen_tac `key_op` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (shape_under_tac compile_keccak256_key_shape `\st. T` >> simp[shape_stable_def]) >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `hashed_key` >> simp[] >>
  match_mp_tac shape_step_bind >> qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (shape_under_tac compile_mapping_subscript_shape `\st. T` >> simp[shape_stable_def] >>
      Cases_on `FLOOKUP cenv.ce_vars var_name` >> simp[]
      >- shape_opcode_tac >>
      rename1 `SOME local_loc` >> Cases_on `local_loc` >> shape_opcode_tac) >>
  gen_tac >> simp[] >> irule shape_step_return >>
  simp[value_shape_ok_def, mk_ptr_def]
QED
Finalise compile_subscript_shape

Theorem compile_array_membership_loop_shape[local]:
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
    ho_match_mp_tac shape_step_assume_pure >> strip_tac)
    [`entry_lbl`, `cond_lbl`, `body_lbl`, `found_lbl`, `incr_lbl`, `exit_lbl`] >>
  suspend "header"
QED
Resume compile_array_membership_loop_shape[header]:
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. C st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `C` >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
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
     >- (shape_under_tac shape_step_emit_inst_guarded `D` >>
         simp[Abbr `D`, Abbr `C`] >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
     gen_tac >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `D` `done_op` (simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `\st. D st /\ plain_operand st done_op` >>
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
  >- (shape_under_tac shape_step_emit_inst_guarded `\st. D st /\ plain_operand st match_op` >>
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
     >- (shape_under_tac shape_step_emit_inst_guarded `D` >>
         simp[Abbr `D`, Abbr `C`] >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
     gen_tac >> simp[]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >>
  shape_scalar_emit_bind_tac `D` `new_idx` (simp[Abbr `D`]) >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `\st. D st /\ plain_operand st new_idx` >>
      conj_tac
      >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
          mp_tac (Q.SPEC `[new_idx]` shape_stable_plain_operands) >> simp[]) >>
      simp[Abbr `D`] >> shape_opcode_tac) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (shape_under_tac shape_step_emit_inst_guarded `D` >> shape_opcode_tac >> simp[jump_label_ok_def]) >>
  gen_tac >> simp[] >>
  match_mp_tac shape_step_ignore_bind >> qexists_tac `\u st. D st` >> conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[] >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[Abbr `D`, Abbr `C`, Abbr `P`]) >>
  shape_under_tac shape_step_emit_op_plain `R` >> simp[Abbr `D`, Abbr `C`, Abbr `P`] >> shape_opcode_tac
QED
Finalise compile_array_membership_loop_shape

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
          shape_under_tac shape_step_emit_inst_guarded `\st. C st /\ plain_operand st valid` >>
          conj_tac
          >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
              mp_tac (Q.SPEC `[valid]` shape_stable_plain_operands) >> simp[]) >>
          shape_opcode_tac)) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> simp[] >>
  shape_under_tac compile_array_membership_loop_shape `R` >> simp[Abbr `C`, Abbr `P`] >>
  Cases_on `arr_vv` >> simp[value_shape_ok_def, vv_operand_def]
QED

Theorem shape_compile_expr_pop_body[local]:
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_expr_body cfn bfn tfn cenv ty (Pop annot target))
    (\v st. value_shape_ok st v)
Proof
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `target` >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (irule shape_step_uncurry >>
   qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> conj_tac
   >- (gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def, mk_ptr_def] >>
       metis_tac[infer_array_location_shape]) >>
   shape_under_tac compile_dynarray_pop_shape `\st. cenv_shape_ok st cenv` >>
   simp[cenv_shape_ok_stable] >>
   TRY (qmatch_goalsub_abbrev_tac
          `case pop_loc of LocMemory => MLOAD | LocStorage => SLOAD | LocTransient => TLOAD | LocCode => MLOAD | LocCalldata => MLOAD` >>
        Cases_on `pop_loc` >> simp[]) >>
   rpt strip_tac >> irule compile_target_base_shape >> simp[])
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
  >- (shape_under_tac compile_alloc_buffer_shape `R`) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >>
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

Theorem compile_clamp_extract32_shape[local]:
  shape_stable R ==>
  shape_step internal compiler_label (\st. R st /\ plain_operand st val_op)
    (compile_clamp_extract32 val_op clamp) (\v st. R st /\ plain_operand st v)
Proof
  strip_tac >>
  qabbrev_tac `P = \st. R st /\ plain_operand st val_op` >>
  `shape_stable P` by
    (simp[Abbr `P`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[val_op]` shape_stable_plain_operands) >> simp[]) >>
  Cases_on `clamp` >> simp[builtinBytesTheory.compile_clamp_extract32_def]
  >- (irule shape_step_return >> simp[Abbr `P`])
  >- (shape_scalar_emit_bind_tac `P` `canonical` (simp[Abbr `P`]) >>
      shape_scalar_emit_bind_tac `P` `eq_op` (simp[Abbr `P`]) >>
      shape_scalar_assert_tac `P` >> irule shape_step_return >> simp[Abbr `P`]) >>
  (shape_scalar_emit_bind_tac `P` `too_big` (simp[Abbr `P`]) >>
   shape_scalar_emit_bind_tac `P` `ok_op` all_tac >>
   shape_scalar_assert_tac `P` >> irule shape_step_return >> simp[Abbr `P`])
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
  >- (shape_under_tac compile_alloc_buffer_shape `D`) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `InputFrame`) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >> qx_gen_tac `in_buf` >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `InputFrame`) >> qx_gen_tac `out_buf` >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >> qx_gen_tac `in_buf` >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `InputFrame`) >> qx_gen_tac `out_buf` >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `P`) >> qx_gen_tac `in_buf` >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `InputFrame`) >> qx_gen_tac `out_buf` >>
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

Theorem compile_stage_intcall_args_shape[local]:
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
      mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
      disch_then (qspecl_then [`internal'`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
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
     mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
     disch_then (qspecl_then [`internal'`, `LP`, `st`, `st'`] mp_tac) >> simp[]) >>
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
  >- (shape_under_tac compile_alloc_buffer_shape `ValFrame`) >>
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
          >- (shape_under_tac compile_store_bytestring_shape `BufFrame` >>
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
Finalise compile_stage_intcall_args_shape

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
  >- (shape_under_tac compile_alloc_buffer_shape `VVFrame`) >>
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
  >- (shape_under_tac compile_store_memory_shape `BufFrame` >> simp[Abbr `BufFrame`]) >>
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
  >- (irule lower_value_shape >> simp[]) >>
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
  >- (irule shape_step_conseq >> irule_at Any lower_value_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `addr_op` >> simp[] >>
  qabbrev_tac `AddrFrame = \st. cenv_shape_ok st cenv /\ plain_operand st addr_op` >>
  `shape_stable AddrFrame` by
    (simp[Abbr `AddrFrame`] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
     mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. AddrFrame st /\ plain_operand st v` >> reverse conj_tac
  >- (shape_under_tac lower_value_shape `AddrFrame` >> simp[Abbr `AddrFrame`]) >>
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
  shape_under_tac lower_value_shape `ValFrame` >> simp[Abbr `ValFrame`, Abbr `AddrFrame`]
QED

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
