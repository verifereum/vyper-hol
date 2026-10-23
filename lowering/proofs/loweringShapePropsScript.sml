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
