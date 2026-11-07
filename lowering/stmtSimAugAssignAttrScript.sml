(*
 * Statement simulation: an augmented assignment to a word field of a local
 * struct (#637)
 *
 * x.f op= e for a local x of struct type held through its pointer p and f
 * a field of a word_value_type.  The source takes the place x.f, reads
 * x.f's value, evaluates e, runs the operator on the two and writes the
 * result at x.f.  The lowering adds f's byte offset to p (dst), loads dst,
 * lowers e at f's type, runs compile_binop and stores the result at dst.
 *
 * The counted proof composes the zero-mark ADD/MLOAD prefix, the RHS
 * expression outcome, the checked operator and the zero-mark field store.
 * Saved operands and the complete variable/allocation frame survive each
 * stage. The exported counted load/operator interface also supports other
 * load prefixes.
 *
 * TOP-LEVEL:
 *   compile_augassign_attr_local_case
 *   compile_augassign_attr_local_stmt_frag
 *   augassign_attr_local_place
 *
 * Source/layout helpers are kept separate from counted execution helpers.
 *)

Theory stmtSimAugAssignAttr
Ancestors
  fragGasMode exprSimMemoryPath stmtSimDeclGas gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  exprBopSimDefs exprBopSimProps exprSafeOperand exprWordOperand
  exprSimFieldLayout
  exprSimSource
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec freshWrites loweringSlice  exprSimHyps exprSimOps
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimBuffer
  exprSimAttributeFields
   stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssign
  stmtSimAugAssign stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperTyping
  vyperTypeBuiltins vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeSystem
  vyperContext vyperAST vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* Observation transport changes only the source entry observations; both
   the all-tail execution and the full entry frame ignore that field. *)
Theorem expr_sim_start_gas_obs:
  expr_sim ctx func cenv cx ty e es ==>
  expr_sim ctx func cenv cx ty e (es with gas_obs := gs)
Proof
  rewrite_tac[expr_sim_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`sa`, `sb`, `op`, `s0`] mp_tac) >>
  impl_tac >- gvs[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def,
           expr_post_def, locals_kept_def]) >>
  disj2_tac >> drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `gs` mp_tac) >> simp[] >> metis_tac[]
QED

(* ===== The source ===== *)

(* A struct value of its type has every field its type lists, at that
   field's type. *)
Theorem struct_has_type_field:
  !fs vals id ftv.
    struct_has_type fs vals /\ ALOOKUP fs id = SOME ftv ==>
    ?fv. ALOOKUP vals id = SOME fv /\ value_has_type ftv fv
Proof
  Induct >> simp[] >> PairCases >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >> rw[value_has_type_def] >> gvs[] >> metis_tac[]
QED

(* x.f op= e, unless it fails with a type error: x.f's value fv is read
   and e evaluated, then the operator runs on the two, and its result is
   written at x.f. *)
Theorem eval_augassign_attr_local:
  !cx ty id fld bop e es res es' entry fs vals ftv fv.
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 ftv bop fv v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r =>
              write_place cx (MemoryPlace id [AttrSubscript fld]) r es1 =
                (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  `read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL fv, es) /\
   place_type_value cx (MemoryPlace id [AttrSubscript fld]) es =
     (INL ftv, es)` by
    simp[read_place_def, place_type_value_def, bind_def, get_scopes_def,
         lift_option_type_def, return_def, read_memory_path_def,
         evaluate_subscripts_def, subscripts_type_def, subscript_type_def,
         lift_sum_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM] >>
  Cases_on `eval_target_place cx (AttributeTarget (NameTarget id) fld) es` >>
  rename1 `_ = (r0, es0)` >>
  Cases_on `r0` >> simp[]
  >- (drule eval_target_place_attr_local >> simp[] >> strip_tac >> gvs[] >>
      asm_simp_tac (srw_ss()) [] >>
      Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r2, st0)` >>
      Cases_on `r2` >> simp[] >>
      rename1 `eval_expr cx e es = (INL raw, st0)` >>
      Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, es1)` >>
      Cases_on `r1` >> simp[] >>
      qmatch_goalsub_abbrev_tac `evaluate_binop u ftv bop fv v1` >>
      Cases_on `evaluate_binop u ftv bop fv v1` >>
      simp[lift_sum_def, return_def, raise_def]) >>
  strip_tac >> gvs[] >>
  drule eval_target_place_attr_local >> gvs[]
QED

(* Pure field-place prefix, independent of the initial observation list. *)
Theorem augassign_attr_place_reads:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
    (INL (MemoryPlace id [AttrSubscript fld]), es) /\
  read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL fv, es) /\
  place_type_value cx (MemoryPlace id [AttrSubscript fld]) es = (INL ftv, es)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def] >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, subscripts_type_def,
       subscript_type_def, lift_sum_def, extend_memory_place_def,
       get_place_def, ignore_bind_def]
QED

Theorem eval_augassign_attr_forced:
  eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
    (INL (MemoryPlace id [AttrSubscript fld]), es) /\
  read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL fv, es) /\
  place_type_value cx (MemoryPlace id [AttrSubscript fld]) es = (INL ftv, es) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od) es
Proof
  strip_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (rr, ee)` >>
  Cases_on `rr` >> simp[] >>
  rename1 `read_result cx raw ee` >>
  Cases_on `read_result cx raw ee` >> rename1 `_ = (rv, ef)` >>
  Cases_on `rv` >> simp[]
QED

Theorem eval_augassign_attr_fields:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od) es
Proof
  strip_tac >> drule_all augassign_attr_place_reads >>
  strip_tac >> irule eval_augassign_attr_forced >> simp[]
QED

Theorem eval_augassign_attr_fields_obs:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  !gs. eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
    (es with gas_obs := gs) =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od)
    (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >> irule eval_augassign_attr_fields >>
  simp[] >> metis_tac[]
QED

Theorem augassign_attr_rhs_admissible:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
  qpat_x_assum `lookup_scopes id es.scopes = _` kall_tac >>
  drule_all eval_augassign_attr_fields >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def] >> strip_tac >>
  `no_control_exc y` by
    (qpat_x_assum `bind _ _ _ = (INR y, _)` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  drule_all gas_admissible_result >>
  Cases_on `y` >> gvs[no_control_exc_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_attr_rhs_exception:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
    (INR ex, ee)
Proof
  strip_tac >> drule_all eval_augassign_attr_fields >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def]
QED

Theorem augassign_attr_rhs_normal:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v)) (write_place cx (MemoryPlace id [AttrSubscript fld])) ee
Proof
  strip_tac >> drule_all eval_augassign_attr_fields >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def]
QED

Theorem augassign_attr_rhs_exception_exec:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_attr_rhs_exception >> simp[] >> metis_tac[]
QED

Theorem augassign_attr_rhs_normal_exec:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v)) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >>
  drule_all gas_marked_exec_zero_prefix >> strip_tac >>
  `gas_marked_exec F (ctx,func)
    (do v <- bind (eval_expr cx e) (read_result cx);
        w <- lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          ftv bop fv v);
        write_place cx (MemoryPlace id [AttrSubscript fld]) w od)
    (es,s0) (marks ++ []) res fin r` by
    (irule gas_marked_exec_bind_normal >> simp[] >> metis_tac[]) >>
  drule_all eval_augassign_attr_fields_obs >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] assume_tac) >>
  gvs[gas_marked_exec_def]
QED

Theorem augassign_attr_binop_admissible:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v ee)
Proof
  strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v ee) <=>
   expr_res_ok (case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
  drule_all eval_augassign_attr_fields_obs >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`, `gs`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v` >> gvs[expr_res_ok_def] >>
  simp[lift_sum_def, raise_def] >> strip_tac >>
  drule_all gas_admissible_result >> simp[stmt_res_ok_def]
QED

Theorem augassign_attr_write_admissible:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) /\
  bop_result cx ty bop [ty; expr_type e] fv v ee = INL w /\
  write_place cx (MemoryPlace id [AttrSubscript fld]) w ee = (res, fin) ==>
  !m. res <> INR (Error (TypeError m))
Proof
  strip_tac >>
  `?actual. evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ftv bop fv v = INL actual` by
    metis_tac[bop_result_augassign_success] >>
  Cases_on `write_place cx (MemoryPlace id [AttrSubscript fld]) actual ee` >>
  rename1 `_ = (actual_res, actual_fin)` >>
  `eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
     (es with gas_obs := gs) = (actual_res, actual_fin)` by
    (drule_all eval_augassign_attr_fields_obs >>
     disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`, `gs`] mp_tac) >>
     simp[GSYM bind_assoc, bind_def, lift_sum_def, return_def]) >>
  `stmt_res_ok lctx actual_res` by metis_tac[gas_admissible_result] >>
  `res = actual_res` by
    (qspecl_then [`[AttrSubscript fld]`, `cx`, `id`, `w`, `ee`, `actual`]
       mp_tac write_place_short_memory_result >> simp[]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_attr_rhs_exempt:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (AttributeTarget (NameTarget id) fld))
    (es,s0) [] (INL (MemoryPlace id [AttrSubscript fld])) es (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  simp[bind_assoc] >>
  rewrite_tac[read_place_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, read_memory_path_def,
       evaluate_subscripts_def, lift_sum_def] >>
  rewrite_tac[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, subscripts_type_def,
       subscript_type_def, lift_sum_def] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

(* ===== The code ===== *)

(* x.f op= e on a local x held through its pointer p: the ADD of f's byte
   offset to p, an MLOAD of the sum, e lowered at the field's type, the
   operator and an MSTORE at the sum. *)
Theorem augassign_attr_local_code_parts:
  !cenv lctx ty0 ty id fld bop e sa c sf p sz sid.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Var p; Lit (n2w (struct_field_offset
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sa = (dst, sn) /\
      emit_op MLOAD [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [dst; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Var p; Lit (n2w off)] sa` >>
  Cases_on `emit_op ADD [Var p; Lit (n2w off)] sa` >>
  rename1 `_ = (dst, sn)` >>
  Cases_on `emit_op MLOAD [dst] sn` >> rename1 `_ = (cur, s1)` >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs, s2)` >>
  Cases_on `compile_binop bop cur rhs ty NONE
              (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op, s3)` >>
  Cases_on `emit_void MSTORE [dst; res_op] s3` >>
  asm_simp_tac (srw_ss())
    [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
     oneTheory.one] >>
  strip_tac >> gvs[oneTheory.one]
QED

(* ===== The load ===== *)

(* A word field of a local struct, at x's pointer plus the field's
   offset: the word the field's value is held in. *)
Theorem stmt_state_rel_field_word:
  !func cenv cx es s id p sz w0 entry fs vals flds fld ftv fv fty ctx.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w0 /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    is_word_type fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
    value_has_type ftv fv ==>
    mload (w2n (w0 + n2w (struct_field_offset flds fld))) s =
      typed_val_to_w256 ftv fv
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n w0 + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n w0) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `struct_field_offset flds fld + type_memory_size ftv <=
     type_memory_size_fields fs` by metis_tac[struct_field_offset_le] >>
  `w2n (w0 + n2w (struct_field_offset flds fld)) =
     w2n w0 + struct_field_offset flds fld` by
    (irule buffer_offset_no_wrap >>
     qexists_tac `type_memory_size_fields fs` >>
     gvs[type_memory_size_def]) >>
  `val_in_memory ftv fv (w2n w0 + struct_field_offset flds fld)
     s.vs_memory` by
    (irule fields_in_memory_field >> qexistsl_tac [`fs`, `vals`] >>
     gvs[val_in_memory_struct]) >>
  simp[GSYM mem_word_at_eq_mload] >>
  irule val_in_memory_word_type >> metis_tac[]
QED

Theorem attr_add_marked_path:
  emit_op ADD [arg; Lit (n2w off)] sa = (dst,sn) /\
  fn_has_code sa sn func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ eval_operand arg s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (w + n2w off) /\
      ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
      q.vs_inst_idx = LENGTH sn.cs_current_insts /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      (!x u. not_fresh_at sa x /\ lookup_var x s = SOME u ==>
             lookup_var x q = SOME u)
Proof
  strip_tac >>
  qabbrev_tac `q = (update_var (STRING #"%" (toString sa.cs_next_var))
    (w + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (simp[Abbr `q`, gas_marked_path_def, NoAsms] >> irule emit_op_zero_path >>
     simp[is_terminator_def] >>
     qexistsl_tac [`[arg; Lit (n2w off)]`, `dst`, `ADD`, `sn`] >>
     simp[is_terminator_def] >> gen_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- (simp[Abbr `q`, stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[Abbr `q`, eval_operand_def, update_var_def,
    lookup_var_def, not_fresh_at_def, FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem attr_load_marked_path:
  emit_op ADD [arg; Lit (n2w off)] sa = (dst,sm) /\
  emit_op MLOAD [dst] sm = (cur,sn) /\
  fn_has_code sa sn func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ eval_operand arg s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand dst t = SOME (w + n2w off) /\
      eval_operand cur t = SOME (mload (w2n (w + n2w off)) s) /\
      ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      (!x u. not_fresh_at sa x /\ lookup_var x s = SOME u ==>
             lookup_var x t = SOME u)
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\
   sa.cs_next_var <= sm.cs_next_var /\ 
   (!x. dst = Var x ==> not_fresh_at sm x)` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def,
         cs_extends_def, not_fresh_at_def] >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_split] >>
  drule_all attr_add_marked_path >> strip_tac >>
  qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var))
     (mload (w2n (w + n2w off)) q) q) with
       vs_inst_idx := SUC q.vs_inst_idx` >>
  `gas_marked_path F ctx func q 0 (OK t)` by
    (simp[Abbr `t`, NoAsms] >> irule emit_mload_marked_path >>
     simp[] >> qexistsl_tac [`dst`, `cur`, `sn`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  qexists_tac `t` >> conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[] >>
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[Abbr `t`, eval_operand_def, update_var_def,
    lookup_var_def, not_fresh_at_def,
    FLOOKUP_UPDATE, mload_def] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS]
QED

(* The certificate remains at the RHS entry, for syntactic lifting by the
   enclosing statement. Only a completed summary is prefixed here. *)
Theorem augassign_load_rhs_counted:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  gas_marked_path F ctx func s0 0 (OK sm) /\
  stmt_state_rel ctx func cenv cx es sm /\ ~sm.vs_halted /\
  sm.vs_current_bb = sa.cs_current_bb /\
  sm.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?marks.
    gas_summary_at F (ctx,func) marks
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      (\res ee t. ?v. res = INL v /\
        expr_post ctx func cenv cx e (es with gas_obs := []) sa sb sm ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r) \/
    ?err ee leaf finish.
      gas_exempt_cert F (cx_tops cx) (ctx,func)
        (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
        (es with gas_obs := [],sm) marks (err,ee) (leaf,finish)
Proof
  strip_tac >> drule expr_sim_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >>
  rewrite_tac[expr_sim_def] >> disch_then drule >>
  simp[gas_admissible_gas_obs] >>
  disch_then (qspec_then `sm` mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
      irule gas_marked_exec_zero_prefix >> qexists_tac `sm` >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem augassign_expr_post_operands:
  expr_post ctx func cenv cx e es sa sb sm ee v op t /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. cur = Var x ==> not_fresh_at sa x) /\
  (!l. dst <> Label l) /\ (!l. cur <> Label l) /\
  eval_operand dst sm = SOME addr /\ eval_operand cur sm = SOME w ==>
  eval_operand dst t = SOME addr /\ eval_operand cur t = SOME w
Proof
  rewrite_tac[expr_post_def] >> rpt strip_tac >>
  irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `sm`] >> simp[]
QED

(* Normal RHS-to-operator boundary, independent of the load instruction.
   The original RHS post remains available to the caller for entry framing. *)
Theorem augassign_load_bop_counted:
  expr_post ctx func cenv cx e es sa sb sm ee v rhs t /\
  binop_frag ctx func cenv cx bop ty ann bl el tys fv v ee /\
  compile_binop bop cur rhs ty bl el sb = (out,sc) /\
  expr_res_ok (bop_result cx ann bop tys fv v ee) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. cur = Var x ==> not_fresh_at sa x) /\
  (!l. dst <> Label l) /\ (!l. cur <> Label l) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. rhs = Var x ==> not_fresh_at sb x) /\
  eval_operand dst sm = SOME addr /\
  eval_operand cur sm = SOME (val_to_w256 fv) /\
  eval_operand rhs t = SOME (val_to_w256 v) /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?r. gas_marked_path F ctx func t 0 r /\
    ((?u result. r = OK u /\
       bop_result cx ann bop tys fv v ee = INL result /\ word_value result /\
       stmt_state_rel ctx func cenv cx ee u /\
       eval_operand out u = SOME (val_to_w256 result) /\
       eval_operand dst u = SOME addr /\
       (!x w. not_fresh_at sb x /\ lookup_var x t = SOME w ==>
              lookup_var x u = SOME w) /\
       (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
                FLOOKUP u.vs_allocas aid = SOME b) /\
       u.vs_memory = t.vs_memory /\ ~u.vs_halted /\
       u.vs_current_bb = sc.cs_current_bb /\
       u.vs_inst_idx = LENGTH sc.cs_current_insts) \/
     (exit_result r /\ expr_exit (bop_result cx ann bop tys fv v ee) r))
Proof
  strip_tac >>
  `eval_operand dst t = SOME addr /\
   eval_operand cur t = SOME (val_to_w256 fv)` by
    (fs[expr_post_def] >> conj_tac >> irule eval_operand_frame >>
     simp[] >> qexistsl_tac [`sa`, `sm`] >> simp[]) >>
  `(!x. dst = Var x ==> not_fresh_at sb x) /\
   (!x. cur = Var x ==> not_fresh_at sb x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t /\ ~t.vs_halted` by
    gvs[expr_post_def] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[binop_frag_def, binop_frag_words_def] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `r` >> simp[] >>
  irule eval_operand_frame >> simp[] >>
  qexistsl_tac [`sb`, `t`] >> simp[]
QED

Theorem augassign_attr_binop_ready:
  expr_body_pre cenv cx env e es /\
  well_formed_type (get_tenv cx) ty /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\ value_has_type ftv fv /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_sim_inv cenv cx env ee /\
  (!w. bop_result cx ty bop [ty; expr_type e] fv v est = INL w ==>
       value_has_type ftv w) /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty; expr_type e] fv v est
Proof
  strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `?raw st. eval_expr cx e (es with gas_obs := gs) = (INL raw,st) /\
            read_result cx raw st = (INL v,ee)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  drule expr_body_pre_word_result >>
  disch_then (qspecl_then [`INL v`, `ee`] mp_tac) >>
  simp[bind_def] >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `bop_result _ _ _ _ _ _ _ = _` mp_tac >>
      simp[bop_result_def, evaluate_builtin_def] >> strip_tac >>
      gvs[AllCaseEqs()] >> metis_tac[well_typed_binop_success_type]) >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  irule binop_frag_word_typed >> simp[] >>
  conj_tac
  >- (strip_tac >> Cases_on `int_literal_value e` >>
      gvs[nonneg_int_literal_def, expr_int_literal_value]) >>
  conj_tac
  >- (strip_tac >> `shift_amount_ok e` by simp[] >>
      drule_all eval_expr_shift_amount >> simp[]) >>
  qexistsl_tac [`expr_type e`, `get_tenv cx`, `ftv`, `tyv`] >> simp[]
QED

Theorem augassign_attr_rhs_word_operand[local]:
  expr_body_pre cenv cx env e es /\ word_value_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,ee) /\
  expr_post ctx func cenv cx e ep sa sb sm ee v rhs t ==>
  eval_operand rhs t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  drule expr_body_pre_word_result >>
  disch_then (qspecl_then [`INL v`, `ee`] mp_tac) >>
  impl_tac >- (simp[bind_def] >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >>
    simp[bind_def, AllCaseEqs()] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `!tv. INL v = INL tv ==> _` (qspec_then `v` mp_tac) >>
  simp[] >> strip_tac >>
  irule expr_val_rel_word >> simp[] >>
  qexistsl_tac [`cx`, `expr_type e`] >>
  fs[expr_post_def, word_value_type_word]
QED

Theorem augassign_attr_operator_counted:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\ value_has_type ftv fv /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) /\
  expr_post ctx func cenv cx e (es with gas_obs := []) sa sb sm
    (ee with gas_obs := []) v rhs t /\
  lower_value compile_expr cenv ty e sa = (rhs,sb) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (out,sc) /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] fv v (ee with gas_obs := [])) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ safe_operand sa dst /\ safe_operand sa cur /\
  eval_operand dst sm = SOME addr /\ eval_operand cur sm = SOME (val_to_w256 fv) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?r. gas_marked_path F ctx func t 0 r /\
    ((?u result. r = OK u /\
       bop_result cx ty bop [ty;expr_type e] fv v (ee with gas_obs := []) = INL result /\
       word_value result /\ stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u /\
       eval_operand out u = SOME (val_to_w256 result) /\ eval_operand dst u = SOME addr /\
       (!x w. not_fresh_at sb x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
       (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
       u.vs_memory = t.vs_memory /\ ~u.vs_halted /\
       u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts) \/
     (exit_result r /\ expr_exit (bop_result cx ty bop [ty;expr_type e] fv v
       (ee with gas_obs := [])) r))
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []) =
     (INL v,ee with gas_obs := [])` by metis_tac[gas_marked_exec_observation] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `well_formed_type (get_tenv cx) ty` by simp[well_formed_type_def] >>
  drule_all augassign_attr_binop_ready >>
  disch_then (qspecl_then [`func`, `ee with gas_obs := []`, `ctx`] strip_assume_tac) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `!name vt. FLOOKUP env.var_types name = SOME vt ==>
     well_formed_type env.type_defs vt` by
    (rpt strip_tac >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule_all expr_sim_inv_local >> strip_tac >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `safe_operand sb rhs` by
    (irule lower_value_word_safe_operand >>
     goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     qexists_tac `env` >> fs[expr_body_pre_def, word_value_type_word] >> metis_tac[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, fragGasPathTheory.gas_path_normal]) >>
  `eval_operand rhs t = SOME (val_to_w256 v)` by
    (irule augassign_attr_rhs_word_operand >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, ci_mono_def, pairTheory.SND] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) augassign_load_bop_counted >>
  disch_then (drule_at (Pat `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`dst`, `addr`] mp_tac) >>
  impl_tac >- fs[safe_operand_def] >> simp[]
QED

(* ===== The statement ===== *)

(* Writing v at x.f for x a local of struct type sid in a state the
   expression invariant holds of, f one of sid's fields: unless it fails
   with a type error, x's value gets v at f, x's struct being laid out as
   the lowering's struct table says. *)
Theorem write_attr_local_typed:
  !cx cenv env id fld sid fty fsz es1 v res es'.
    write_place cx (MemoryPlace id [AttrSubscript fld]) v es1 = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) /\
    expr_sim_inv cenv cx env es1 /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    res = INL () /\
    ?pre env1 entry rest fs vals ftv.
      find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
      entry.type = StructTV fs /\ entry.value = StructV vals /\
      fields_layout (get_struct_fields cenv.ce_struct_fields
                       (nsid_to_string sid)) fs /\
      struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
      evaluate_type (get_tenv cx) fty = SOME ftv /\
      es' = es1 with scopes :=
        pre ++ (env1 |+ (id, entry with
                  <|value := StructV (AFUPDKEY fld (K v) vals);
                    popped := []|>)) :: rest
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field >> strip_tac >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem write_attr_local_gas_obs:
  write_place cx (MemoryPlace id [AttrSubscript fld]) v ee = (res,ff) ==>
  write_place cx (MemoryPlace id [AttrSubscript fld]) v
    (ee with gas_obs := obs) = (res,ff with gas_obs := obs)
Proof
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id ee.scopes` >> simp[raise_def] >>
  rename1 `find_containing_scope _ _ = SOME q` >> PairCases_on `q` >>
  simp[replace_memory_entry_def, bind_def, ignore_bind_def,
       assert_def, raise_def, return_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts q2.type q2.value [AttrSubscript fld]` >>
  simp[return_def, raise_def, bind_def, set_scopes_def] >>
  Cases_on `assign_subscripts q2.type q2.value [AttrSubscript fld] (Replace v)` >>
  simp[return_def, raise_def, bind_def, set_scopes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem augassign_attr_write_all_obs:
  write_place cx (MemoryPlace id [AttrSubscript fld]) v ee = (res,ff) /\
  (!m. res <> INR (Error (TypeError m))) /\
  expr_sim_inv cenv cx env ee /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  res = INL () /\
  ?pre env1 entry rest fs vals.
    find_containing_scope id ee.scopes = SOME (pre,env1,entry,rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME tv /\
    store_lays_out tv tv v /\
    !obs. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := obs) =
      (INL (),ee with <|scopes := pre ++
        (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
          popped := []|>)) :: rest; gas_obs := obs|>)
Proof
  strip_tac >> drule_all write_attr_local_typed >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule store_lays_out_typed >> simp[] >>
      qexistsl_tac [`ty`, `get_tenv cx`] >> simp[]) >>
  drule write_attr_local_gas_obs >> simp[]
QED

(* The store boundary is stated in terms of the saved address and the
   current source layout, not the struct value before evaluation of e. *)
Theorem augassign_attr_store_post_path:
  emit_op ADD [baddr; Lit (n2w off)] sm = (dst,sn) /\
  emit_void MSTORE [dst;op] su = ((),sf) /\
  eval_operand dst t = SOME (w0 + n2w off) /\ lookup_var p t = SOME w0 /\
  eval_operand op t = SOME (typed_val_to_w256 ftv v) /\
  stmt_state_rel ctx func cenv cx ee t /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id ee.scopes = SOME (pre,env1,entry,rest) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
  off = struct_field_offset flds fld /\ fn_has_code su sf func /\
  ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\ ~block_is_terminated sf /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
    (ee with gas_obs := tail) =
    (INL (),ee with <|scopes := pre ++
      (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
        popped := []|>)) :: rest; gas_obs := tail|>)) ==>
  ?ff t'. gas_marked_exec F (ctx,func)
    (write_place cx (MemoryPlace id [AttrSubscript fld]) v)
    (ee with gas_obs := [],t) [] (INL ()) ff (OK t') /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff t'
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var)) t = SOME (w0 + n2w off)` by
    gvs[eval_operand_def] >>
  gvs[] >>
  drule_at (Pat `emit_void _ _ _ = _`) assign_attr_local_store_marked_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fields_layout _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `store_lays_out _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME (_ + n2w _)`)) >>
  disch_then (qspecl_then [`vals`, `fld`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`ee with scopes := pre ++
    (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
      popped := []|>)) :: rest`, `t'`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  metis_tac[]
QED

Theorem augassign_attr_store_continuation_exec:
  br = INL w /\
  gas_marked_exec F (ctx,func)
    (write_place cx (MemoryPlace id [AttrSubscript fld]) w)
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] res fin r
Proof
  strip_tac >> gvs[gas_marked_exec_def, bind_def, lift_sum_def, return_def]
QED

Theorem augassign_attr_error_continuation_exec:
  br = INR err /\ gas_marked_path F ctx func u 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] (INR (Error err)) (ee with gas_obs := []) r
Proof
  strip_tac >> gvs[gas_marked_exec_def, bind_def, lift_sum_def, raise_def]
QED

Theorem augassign_attr_normal_summary[local]:
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = SOME (ty,fsz) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es /\
  lookup_scopes id es.scopes = SOME entry /\ entry.type = StructTV fs /\
  entry.value = StructV vals /\ ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\ value_has_type ftv fv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s0 = SOME w0 /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] sa = (dst,sn) /\
  emit_op MLOAD [dst] sn = (cur,s1) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE (if bop = Exp then expr_int_literal e else NONE)
    s2 = (out,s3) /\ emit_void MSTORE [dst;out] s3 = ((),sb) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated sb /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  gas_marked_path F ctx func s0 0 (OK t) /\ t.vs_allocas = s0.vs_allocas /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  eval_operand dst t = SOME (w0 + n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) /\
  eval_operand cur t = SOME (val_to_w256 fv) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t') /\
  expr_post ctx func cenv cx e (es with gas_obs := []) s1 s2 t
    (ee with gas_obs := []) v rhs t' /\
  t'.vs_current_bb = s2.cs_current_bb /\ t'.vs_inst_idx = LENGTH s2.cs_current_insts ==>
  gas_summary_at F (ctx,func) marks
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []) =
     (INL v,ee with gas_obs := [])` by metis_tac[gas_marked_exec_observation] >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] fv v (ee with gas_obs := []))` by
    (irule augassign_attr_binop_admissible >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `safe_operand s1 dst /\ safe_operand s1 cur` by
    metis_tac[emit_op_safe_operand, safe_operand_mono, ci_mono_emit_op,
              ci_mono_def, pairTheory.SND] >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) augassign_attr_operator_counted >>
  disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (qspecl_then [`dst`, `w0 + n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac
  >- suspend "store"
  >> suspend "operator_error"
QED
Resume augassign_attr_normal_summary[store]:
  gvs[] >>
  drule_all well_typed_binop_augassign_word >> strip_tac >>
  `word_value fv` by
    (drule_all word_value_type_typed >> simp[]) >>
  `well_formed_type (get_tenv cx) ty` by simp[well_formed_type_def] >>
  drule_all augassign_attr_binop_ready >>
  disch_then (qspecl_then [`func`, `ee with gas_obs := []`, `ctx`] strip_assume_tac) >>
  `value_has_type ftv result` by
    (first_x_assum irule >> simp[]) >>
  `?wr ff. write_place cx (MemoryPlace id [AttrSubscript fld]) result
      (ee with gas_obs := []) = (wr,ff)` by metis_tac[pairTheory.PAIR] >>
  `!m. wr <> INR (Error (TypeError m))` by
    (irule augassign_attr_write_admissible >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `is_word_type ty` by metis_tac[well_typed_binop_augassign_word, word_value_type_word] >>
  drule_at (Pat `write_place _ _ _ _ = _`) augassign_attr_write_all_obs >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (StructT _)`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_lower_value_cfn, compile_expr_ci_mono,
      ci_mono_def, pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w` by
    (fs[expr_post_def] >> rpt strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `lookup_var p u = SOME w0` by
    (first_x_assum irule >> simp[] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand out u = SOME (typed_val_to_w256 ftv result)` by
    simp[typed_val_to_w256_word_value] >>
  drule_at (Pat `emit_void _ _ _ = _`) augassign_attr_store_post_path >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `fields_layout _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ u = _`)) >>
  disch_then (drule_at (Pat `eval_operand out u = SOME (typed_val_to_w256 _ _)`)) >>
  disch_then (drule_at (Pat `ALOOKUP fs' fld = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `entry'.value = _`)) >>
  disch_then (qspecl_then [`sa`, `s0`, `lctx`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] fv v ee =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[word_value_not_bytes]) >>
  `evaluate_binop (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v = INL result` by
    (Cases_on `evaluate_binop (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v` >> gvs[]) >>
  drule_all eval_augassign_attr_fields_obs >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] assume_tac) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK t''`] >>
  simp[stmtSimDeclComposeTheory.stmt_post_end_gas_obs] >>
  fs[gas_marked_exec_def] >> simp[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >> simp[GSYM bind_assoc, bind_def, lift_sum_def, return_def]) >>
  `gas_marked_path F ctx func t' 0 (OK t'')` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]
QED
Resume augassign_attr_normal_summary[operator_error]:
  gvs[] >>
  drule_all well_typed_binop_augassign_word >> strip_tac >>
  `word_value fv` by
    (drule_all word_value_type_typed >> simp[]) >>
  `bop_result cx ty bop [ty;expr_type e] fv v ee =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[word_value_not_bytes]) >>
  Cases_on `evaluate_binop (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v` >- gvs[] >>
  gvs[] >>
  drule_all eval_augassign_attr_fields_obs >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] assume_tac) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error y)`, `ee`, `r`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> conj_tac
      >- (gen_tac >> simp[GSYM bind_assoc, bind_def, lift_sum_def, raise_def]) >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def]
QED
Finalise augassign_attr_normal_summary

(* x.f for x a local of struct type sid in a state the expression invariant
   holds of, f one of sid's fields: its place, value and type are read. *)
Theorem augassign_attr_local_place:
  !cx cenv env es id fld sid fty fsz.
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?cur ptv.
      eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
        (INL (MemoryPlace id [AttrSubscript fld]), es) /\
      read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL cur, es) /\
      place_type_value cx (MemoryPlace id [AttrSubscript fld]) es =
        (INL ptv, es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field >> strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def] >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, subscripts_type_def,
       subscript_type_def, lift_sum_def, extend_memory_place_def,
       get_place_def, ignore_bind_def]
QED

(* x.f op= e for a local x of struct type sid and f a field of sid of type
   ty, ty a word_value_type, for every outcome: e's errors and the
   operator's (overflow, division by zero) exit, and on a value the MSTORE
   writes it at f's offset in x's region.  e may call internal functions:
   its simulation at f's type is a premise. *)
Theorem compile_augassign_attr_local_case:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es.
    expr_sim ctx func cenv cx ty e es /\ expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  drule_all augassign_attr_local_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 sb` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def,
              pairTheory.SND, compile_expr_grows, compile_binop_grows] >>
  `fn_has_code sa sn func /\ fn_has_code sn s1 func /\
   fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field >> strip_tac >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `?w0. lookup_var p s0 = SOME w0` by
    metis_tac[local_word_pointer_live] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `eval_operand (Var p) s0 = SOME w0` by simp[eval_operand_def] >>
  drule_all attr_load_marked_path >> strip_tac >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_emit_op, ci_mono_def,
              pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule augassign_attr_rhs_admissible >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all augassign_load_rhs_counted >> strip_tac
  >- suspend "rhs_summary" >>
  suspend "rhs_exempt"
QED

Resume compile_augassign_attr_local_case[rhs_exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_attr_rhs_exempt >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rewrite_tac[gas_marked_exec_def] >> simp[] >>
  gen_tac >> irule (cj 1 augassign_attr_place_reads) >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Resume compile_augassign_attr_local_case[rhs_summary]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
  >- suspend "rhs_normal" >>
  suspend "rhs_error"
QED

Resume compile_augassign_attr_local_case[rhs_error]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >> irule augassign_attr_rhs_exception >>
      simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_attr_local_case[rhs_normal]:
  gvs[] >>
  `eval_operand cur t = SOME (val_to_w256 fv)` by
    (`mload (w2n (w0 + n2w (struct_field_offset
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))) s0 =
         typed_val_to_w256 ftv fv` by
       (irule stmt_state_rel_field_word >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     `word_value fv` by metis_tac[word_value_type_typed] >>
     gvs[typed_val_to_w256_word_value]) >>
  irule augassign_attr_normal_summary >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise compile_augassign_attr_local_case

(* compile_augassign_attr_local_case for an e with no internal call. *)
Theorem compile_augassign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es
Proof
  rpt strip_tac >> irule compile_augassign_attr_local_case >>
  `expr_body_pre cenv cx env e es` by fs[expr_sim_pre_body] >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[expr_sim_ok_apply] >>
  simp[] >> metis_tac[]
QED
