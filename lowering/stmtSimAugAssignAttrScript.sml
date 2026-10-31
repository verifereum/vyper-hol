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
 * x.f op e is no expression whose lowering this is: dst is computed before
 * e's code and used again after the operator's, so it has to survive both.
 * The pieces therefore run one after the other, each from the state the
 * previous one leaves (augassign_attr_bop_frag): the ADD and the MLOAD,
 * then e's expr_sim and the operator's binop_frag, which keep every
 * variable defined before them, dst among them.
 *
 * TOP-LEVEL:
 *   compile_augassign_attr_local_case — x.f op= e, every outcome, e's
 *                                      simulation a premise
 *   compile_augassign_attr_local_stmt_frag — the same for an e with no
 *                                      internal call
 *   augassign_attr_local_place       — x.f's place, value and type are read
 *                                      where expr_sim_inv holds
 *
 * Helpers: struct_has_type_field, eval_augassign_attr_local,
 *   augassign_attr_local_code_parts, stmt_state_rel_field_word,
 *   attr_load_frag, augassign_attr_bop_frag, write_attr_local_typed,
 *   augassign_attr_local_frag
 *)

Theory stmtSimAugAssignAttr
Ancestors
  list rich_list finite_map pred_set alist
  fragExec freshWrites loweringSlice exprSim exprSimHyps exprSimOps
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimBuffer
  exprSimAttributeFields
  stmtSim stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssign
  stmtSimAugAssign stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperTyping
  vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeSystem
  vyperAST
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

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
  !func cenv cx es s id p sz w0 entry fs vals flds fld ftv fv fty.
    stmt_state_rel func cenv cx es s /\
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
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room func s` by
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

(* The ADD and the MLOAD of x.f op= e: dst holds x's pointer plus off, and
   cur the word at dst. *)
Theorem attr_load_frag:
  !ctx func cenv cx es p off sa dst sn cur s1 s0 w0 R.
    emit_op ADD [Var p; Lit (n2w off)] sa = (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w0 ==>
    frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. stmt_state_rel func cenv cx es s /\
           eval_operand dst s = SOME (w0 + n2w off) /\
           eval_operand cur s = SOME (mload (w2n (w0 + n2w off)) s0) /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x s = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `ci_mono sa sn /\ ci_mono sn s1` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def]) >>
  `?d. dst = Var d /\ not_fresh_at sn d` by
    (qpat_assum `emit_op ADD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `ADD`,
               `[Var p; Lit (n2w off)]`, `sa`, `dst`, `sn`, `s0`,
               `w0 + n2w off`, `R`] mp_tac emit_op_frag >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >> irule step_ADD >>
      simp[eval_operand_def]) >>
  strip_tac >>
  irule frag_exec_seq_pointwise >>
  first_x_assum (irule_at Any) >> fs[ci_mono_def] >>
  rpt strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `MLOAD`, `[dst]`, `sn`,
               `cur`, `s1`, `t`, `mload (w2n (w0 + n2w off)) t`, `R`]
    mp_tac emit_op_frag >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >> irule step_MLOAD >>
      fs[]) >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `mload (w2n (w0 + n2w off)) t = mload (w2n (w0 + n2w off)) s0` by
    simp[mload_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  gvs[eval_operand_def] >> metis_tac[]
QED

(* ===== x.f op e ===== *)

(* The ADD, the MLOAD, e and the operator, one after the other: e's errors
   and the operator's exit, and on a value v of the operator the result
   holds v's word, dst still holds the field's address, and the frame from
   before the ADD holds. *)
Theorem augassign_attr_bop_frag:
  !ctx func cenv cx es ty bop e el p off sa dst sn cur s1 rhs s2 res_op s3
   s0 w0 v1 r1 es1.
    emit_op ADD [Var p; Lit (n2w off)] sa = (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w0 /\
    mload (w2n (w0 + n2w off)) s0 = val_to_w256 v1 /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
          word_value v2 /\ is_word_type (expr_type e) /\
          IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
          expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
          binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
            v1 v2 es1) ==>
    frag_exec ctx sa s3 (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. ?v2 v. r1 = INL v2 /\
                  bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v /\
                  word_value v /\ stmt_state_rel func cenv cx es1 s /\
                  eval_operand res_op s = SOME (val_to_w256 v) /\
                  eval_operand dst s = SOME (w0 + n2w off) /\
                  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                         lookup_var x s = SOME u) /\
                  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                           FLOOKUP s.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
                    INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
                  | INR ex => INR ex))
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sn /\ ci_mono sn s1` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends s2 s3 /\ s2.cs_next_var <= s3.cs_next_var` by
    metis_tac[compile_binop_shape] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `cs_extends s1 s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code s1 s3 func` by metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `(!x. not_fresh_at sa x ==> not_fresh_at s1 x) /\
   (!x. not_fresh_at s1 x ==> not_fresh_at s2 x) /\
   (!x. not_fresh_at s2 x ==> not_fresh_at s3 x)` by
    metis_tac[not_fresh_at_mono] >>
  `(!z. dst = Var z ==> not_fresh_at s1 z) /\ (!l. dst <> Label l) /\
   (!z. cur = Var z ==> not_fresh_at s1 z) /\ (!l. cur <> Label l)` by
    (imp_res_tac emitted_insts_emit_op >> fs[ci_mono_def] >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `p`, `off`, `sa`, `dst`,
               `sn`, `cur`, `s1`, `s0`, `w0`,
               `expr_exit (case r1 of
                             INL v2 => bop_result cx ty bop [ty; expr_type e]
                                         v1 v2 es1
                           | INR ex => INR ex)`]
    mp_tac attr_load_frag >>
  impl_tac >- fs[] >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  fs[] >> rpt strip_tac >>
  reverse (Cases_on `r1`) >> fs[]
  >- ((* e raises *)
      rename1 `_ = (INR ex, es1)` >>
      qpat_x_assum `expr_sim _ _ _ _ _ e _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`s1`, `s2`, `rhs`, `INR ex`, `es1`, `t`]
                    mp_tac) >>
      impl_tac >- fs[] >>
      disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then (qspecl_then [`\s. s = t`, `\s. F`, `expr_exit (INR ex : value + exception)`]
                    mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s2` >> fs[]) >>
  (* e's value, from t to u *)
  rename1 `_ = (INL v2, es1)` >>
  qpat_x_assum `expr_sim _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs`, `INL v2`, `es1`, `t`] mp_tac) >>
  impl_tac >- fs[expr_res_ok_def] >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = t`,
     `expr_exit (bop_result cx ty bop [ty; expr_type e] v1 v2 es1)`]
    mp_tac) >>
  impl_tac >- fs[] >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  fs[] >> rpt strip_tac >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ _ u` >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `?tv2. evaluate_type (get_tenv cx) (expr_type e) = SOME tv2` by
    fs[optionTheory.IS_SOME_EXISTS] >>
  `eval_operand rhs u = SOME (val_to_w256 v2)` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     first_x_assum drule >> gvs[typed_val_to_w256_word_value]) >>
  `eval_operand cur u = SOME (val_to_w256 v1) /\
   eval_operand dst u = SOME (w0 + n2w off)` by
    (conj_tac >>
     (irule eval_operand_frame >> conj_tac >- fs[] >>
      qexistsl_tac [`s1`, `t`] >> fs[])) >>
  (* the operator, from u *)
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_def, binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `cur`, `rhs`, `res_op`, `u`] mp_tac) >>
  impl_tac >- fs[] >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  fs[] >> rpt strip_tac >>
  `eval_operand dst s = SOME (w0 + n2w off)` by
    (irule eval_operand_frame >> conj_tac >- fs[] >>
     qexistsl_tac [`s2`, `u`] >> fs[]) >>
  qexists_tac `v` >> fs[]
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

(* x.f op= e as one fragment: e's errors and the operator's exit, and on
   a value of the operator the MSTORE writes it at x.f, related at the
   scopes write_place leaves. *)
Theorem augassign_attr_local_frag:
  !ctx func cenv cx es ty bop e el id fld p sz flds ftv sa dst sn cur s1 rhs
   s2 res_op s3 sf s0 v1 r1 es1 res es'.
    emit_op ADD [Var p; Lit (n2w (struct_field_offset flds fld))] sa =
      (dst, sn) /\
    emit_op MLOAD [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    emit_void MSTORE [dst; res_op] s3 = ((), sf) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!s. stmt_state_rel func cenv cx es s ==>
         ?w0. lookup_var p s = SOME w0 /\
              mload (w2n (w0 + n2w (struct_field_offset flds fld))) s =
                val_to_w256 v1) /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
          word_value v2 /\ is_word_type (expr_type e) /\
          IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
          expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
          binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
            v1 v2 es1) /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ftv /\
    type_memory_size ftv = 32 /\
    (!v2 v. r1 = INL v2 /\
            bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v ==>
            res = INL () /\
            ?pre env1 entry rest fs vals.
              find_containing_scope id es1.scopes =
                SOME (pre, env1, entry, rest) /\
              entry.type = StructTV fs /\ entry.value = StructV vals /\
              fields_layout flds fs /\ struct_has_type fs vals /\
              ALOOKUP fs fld = SOME ftv /\
              es' = es1 with scopes :=
                pre ++ (env1 |+ (id, entry with
                          <|value := StructV (AFUPDKEY fld (K v) vals);
                            popped := []|>)) :: rest) ==>
    frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\t. res = INL () /\ stmt_state_rel func cenv cx es' t /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x t = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
                    INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
                  | INR ex => INR ex))
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- simp[frag_exec_def] >>
  qpat_x_assum `!s. stmt_state_rel _ _ _ _ s ==> _` drule >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `ci_mono s3 sf` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sa sn /\ ci_mono sn s1` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends s2 s3` by metis_tac[compile_binop_shape] >>
  `cs_extends sa s3 /\ cs_extends s3 sf` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s3 func` by metis_tac[fn_has_code_split] >>
  drule_all augassign_attr_bop_frag >> strip_tac >>
  irule frag_exec_seq_pointwise >>
  qpat_assum `frag_exec _ sa s3 _ _ _` (irule_at Any) >> fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!v2 v. _ ==> res = INL () /\ _`
    (qspecl_then [`v2`, `v`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  `?d. dst = Var d` by
    (qpat_assum `emit_op ADD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `lookup_var p t = SOME w0` by
    (qpat_x_assum `!x u. not_fresh_at sa x /\ _ ==> lookup_var x t = _`
       irule >> simp[]) >>
  `store_lays_out ftv ftv v` by
    (irule store_lays_out_word_value >> fs[] >> metis_tac[]) >>
  `eval_operand res_op t = SOME (typed_val_to_w256 ftv v)` by
    fs[typed_val_to_w256_word_value] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es1`, `t`, `d`, `res_op`, `s3`,
               `sf`, `p`, `sz`, `w0`, `struct_field_offset flds fld`, `id`,
               `pre`, `env1`, `entry`, `rest`, `fs`, `vals`, `flds`, `fld`,
               `ftv`, `v`,
               `expr_exit (case r1 of
                             INL v2 => bop_result cx ty bop [ty; expr_type e]
                                         v1 v2 es1
                           | INR ex => INR ex)`]
    mp_tac assign_attr_local_store >>
  impl_tac >- gvs[eval_operand_def] >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  fs[] >> metis_tac[]
QED

(* x.f op= e for a local x of struct type sid and f a field of sid of type
   ty, ty a word_value_type, for every outcome: e's errors and the
   operator's (overflow, division by zero) exit, and on a value the MSTORE
   writes it at f's offset in x's region.  e may call internal functions:
   its simulation at f's type is a premise. *)
Theorem compile_augassign_attr_local_case:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es res es'.
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') /\
    expr_sim ctx func cenv cx ty e es /\ expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  drule_all augassign_attr_local_code_parts >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  (* x's struct and its field f before e *)
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  rename1 `entry.value = StructV vals` >>
  drule_all struct_has_type_field >> strip_tac >>
  rename1 `ALOOKUP vals fld = SOME fv` >>
  `word_value fv` by metis_tac[word_value_type_typed] >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     fs[well_formed_type_def]) >>
  `type_memory_size ftv = 32` by metis_tac[word_value_type_memory_size] >>
  (* the source *)
  drule_all eval_augassign_attr_local >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es`, `r1`, `es1`] mp_tac
    expr_body_pre_word_result >>
  impl_tac >- fs[] >> strip_tac >>
  `!v2. bop_result cx ty bop [ty; expr_type e] fv v2 es1 =
        case evaluate_binop
               (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
               ftv bop fv v2 of
          INL v => INL v
        | INR err => INR (Error err)` by
    (gen_tac >> irule bop_result_augassign >> simp[]) >>
  (* the code *)
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l)` by
    (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `ty`, `bop`, `e`,
               `if bop = Exp then expr_int_literal e else NONE`, `id`, `fld`,
               `p`, `sz`,
               `get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)`,
               `ftv`, `sa`, `dst`, `sn`, `cur`, `s1`, `rhs`, `s2`, `res_op`,
               `s3`, `sb`, `s0`, `fv`, `r1`, `es1`, `res`, `es'`]
    mp_tac augassign_attr_local_frag >>
  impl_tac
  >- suspend "frag_pre" >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- fs[] >> strip_tac
  >- (disj1_tac >> qexistsl [`t`, `cenv`] >> gvs[] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  Cases_on `r1` >> gvs[]
  >- (rename1 `evaluate_binop u ftv bop fv v2` >>
      Cases_on `evaluate_binop u ftv bop fv v2` >> gvs[] >>
      metis_tac[expr_exit_INR_type]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_attr_local_case[frag_pre]:
  fs[] >> rpt conj_tac
  >~ [`mload`]
  >- (rpt strip_tac >>
      `?w0. lookup_var p s = SOME w0` by
        (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
         metis_tac[]) >>
      qexists_tac `w0` >> simp[] >>
      qspecl_then [`func`, `cenv`, `cx`, `es`, `s`, `id`, `p`, `sz`, `w0`,
                   `entry`, `fs`, `vals`,
                   `get_struct_fields cenv.ce_struct_fields
                      (nsid_to_string sid)`,
                   `fld`, `ftv`, `fv`, `ty`]
        mp_tac stmt_state_rel_field_word >>
      impl_tac >- fs[] >>
      simp[typed_val_to_w256_word_value])
  >~ [`binop_frag`]
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >> strip_tac >>
      simp[optionTheory.IS_SOME_EXISTS] >>
      conj_tac
      >- (Cases_on `evaluate_binop
                      (case type_to_int_bound ty of
                         SOME u => u | NONE => Unsigned 0) ftv bop fv v2` >>
          gvs[expr_res_ok_def, stmt_res_ok_def]) >>
      irule binop_frag_word_typed >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              ftv bop fv v2` >> gvs[] >>
  drule write_attr_local_typed >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[] >> metis_tac[]
QED

Finalise compile_augassign_attr_local_case

(* compile_augassign_attr_local_case for an e with no internal call. *)
Theorem compile_augassign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id fld sid fsz bop e es res es'.
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') /\
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es res es'
Proof
  rpt strip_tac >> irule compile_augassign_attr_local_case >>
  `expr_body_pre cenv cx env e es` by fs[expr_sim_pre_body] >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[expr_sim_ok_apply] >>
  simp[] >> metis_tac[]
QED
