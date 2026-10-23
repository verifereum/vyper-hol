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
