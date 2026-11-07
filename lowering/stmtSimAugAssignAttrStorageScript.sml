(*
 * Statement simulation: an augmented assignment to a word field of a
 * storage or transient struct (#637)
 *
 * self.x.f op= e for a module variable x in storage or transient storage
 * of a struct type and a field f of a word type.  The source looks up
 * x.f's place (a StoragePlace at x's layout slot plus f's slot offset),
 * reads it, evaluates e, runs the operator and writes the slot.  The
 * lowering ADDs f's slot offset to x's slot into dst, loads dst (SLOAD or
 * TLOAD), lowers e at f's type, runs compile_binop and stores the result
 * at dst (SSTORE or TSTORE).  This is no assignment's code (self.x.f =
 * self.x.f op e would ADD twice), so the proof composes the pieces as
 * stmtSimAugAssignAttr does for a field of a local struct.  As there, **
 * and the narrow or negative shifts rest on exprSimBinopFrag's cheats
 * (#572).
 *
 * TOP-LEVEL:
 *   compile_augassign_attr_storage_case — self.x.f op= e, every outcome,
 *                                         given e's simulation
 *
 *   augassign_attr_storage_place        — x.f's place, value and type are
 *                                         read where expr_sim_inv holds
 *
 * Helpers: eval_target_place_attr_toplevel_field,
 *   augassign_storage_field_place, augassign_storage_field_read,
 *   eval_augassign_attr_storage, augassign_attr_storage_source,
 *   augassign_attr_storage_code_parts, augassign_storage_load_frag,
 *   augassign_attr_storage_frag
 *)

Theory stmtSimAugAssignAttrStorage
Ancestors
  list rich_list finite_map pred_set alist
  fragExec freshWrites loweringSlice exprSim exprSimHyps exprSimOps
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimAttributeFields
  exprSimUnwrap
  stmtSim stmtSimDeclMem stmtSimAssign stmtSimAssignStorage stmtSimAugAssign
  stmtSimAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding accountsRelProps
  vyperInterpreter vyperState vyperStorage vyperValue vyperValueOperation
  vyperTyping vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeSystem vyperAST
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* x.f's place for a storage or transient struct x: x's slot plus f's slot
   offset, at f's type. *)
Theorem eval_target_place_attr_toplevel_field:
  !cx src id fld es ts tr typ id_str slot fs off ftv.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) ==>
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (INL (StoragePlace tr (n2w slot + n2w off) ftv), es with storage_trace := es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) /\
    place_type_value cx (StoragePlace tr (n2w slot + n2w off) ftv) es =
      (INL ftv, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, extend_place_def, extend_storage_place_def,
       get_place_def, place_type_value_def]
QED

(* A non-type-error AugAssign has successfully resolved its target. *)
Theorem augassign_storage_field_place[local]:
  !cx ty src id fld bop e es res es' ts tr sid id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?fs off ftv.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM] >>
  Cases_on `eval_target_place cx
    (AttributeTarget (TopLevelNameTarget (src, id)) fld) es` >>
  rename1 `_ = (r0, es0)` >> Cases_on `r0` >> simp[]
  >- (strip_tac >> drule eval_target_place_attr_toplevel >>
      rpt (disch_then drule) >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule eval_target_place_attr_toplevel >>
  rpt (disch_then drule) >> simp[] >> metis_tac[]
QED

(* A declared struct's field read carries the canonical-slot and live-byte
   facts needed by the backend load, independently of RHS evaluation. *)
Theorem augassign_storage_field_read[local]:
  !cx es src id ts tr sid id_str slot fs fld off ftv ty.
    contract_storage_well_formed cx es /\ storage_layout_safe cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    evaluate_type (get_tenv cx) ty = SOME ftv ==>
    ?cur. read_storage_slot cx tr (n2w slot + n2w off) ftv es =
            (INL cur, es) /\
          !ctx func cenv s.
            stmt_state_rel ctx func cenv cx es s ==>
            storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s
Proof
  rpt strip_tac >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all read_storage_slot_field >> strip_tac >>
  `declared_storage_region cx src id [] =
     SOME (tr, n2w slot, StructTV fs)` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  `get_storage_backend cx tr es = (INL (get_storage cx es tr), es)` by
    simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
  drule_all
    vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >>
  strip_tac >>
  drule_all vyperLookupStorageTheory.storage_field_slots_in_range >>
  strip_tac >>
  qexists_tac `fv` >> simp[storage_holds_def, read_result_def, return_def] >>
  rpt strip_tac >>
  irule storage_range_agree_field >> goal_assum (drule_at Any) >>
  irule storage_range_agree_of_live >> conj_tac
  >- (drule_all
        vyperStorageLayoutSafetyTheory.storage_layout_safe_region_nonoverflow >>
      simp[]) >>
  qexistsl_tac [`cx`, `tr`] >> conj_tac
  >~ [`storage_read_live`]
  >- (irule declared_storage_region_read_live >> goal_assum (drule_at Any)) >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def]
QED

(* The saved field is read before the RHS; its address and type are kept
   even if the RHS changes storage. *)
Theorem eval_augassign_attr_storage[local]:
  !cx ty src id fld bop e es res es' ts tr sid id_str slot fs off ftv cur.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    read_storage_slot cx tr (n2w slot + n2w off) ftv es = (INL cur, es) ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od)
        (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v2 =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 ftv bop cur v2 of
            INR err => res = INR (Error err) /\ es' = es1
          | INL v => write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                      (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_target_place_attr_toplevel_field >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       read_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (r2, st0)` >>
  Cases_on `r2` >> simp[]
  >- (rename1 `eval_expr cx e es = (INL raw, st0)` >>
      Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, es1)` >>
      Cases_on `r1` >> simp[] >>
      qmatch_goalsub_abbrev_tac `evaluate_binop u ftv bop cur v2` >>
      Cases_on `evaluate_binop u ftv bop cur v2` >>
      simp[lift_sum_def, return_def, raise_def, write_place_def]) >>
  simp[]
QED

Theorem augassign_attr_storage_source[local]:
  !cx cenv env lctx ty src id fld sid fsz bop e es res es' ts tr id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    ?fs off ftv cur r1 es1.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      struct_field_offset_slots
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      off /\
      evaluate_type (get_tenv cx) ty = SOME ftv /\
      value_has_type ftv cur /\ word_value cur /\
      (!ctx func s.
         stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s) /\
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      expr_res_ok r1 /\
      (!v2. r1 = INL v2 ==> ?tv2.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
        value_has_type tv2 v2 /\ word_value v2) /\
      (case r1 of
         INR ex => res = INR ex /\ erase_storage_trace es' = erase_storage_trace es1
       | INL v2 =>
           case bop_result cx ty bop [ty; expr_type e] cur v2 es1 of
             INR ex => res = INR ex /\ erase_storage_trace es' = erase_storage_trace es1
           | INL v => ?write_es. write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                       (res, write_es) /\
                       erase_storage_trace write_es = erase_storage_trace es') /\
      (!v2 v. r1 = INL v2 /\
        bop_result cx ty bop [ty; expr_type e] cur v2 es1 = INL v ==>
        encode_value ftv v = SOME [(0, val_to_w256 v)]) /\
      (!u st. storage_dead cx tr
        (update_storage (n2w slot + n2w off) u st) = storage_dead cx tr st)
Proof
  rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all augassign_storage_field_place >> strip_tac >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  drule_all struct_field_type >> strip_tac >>
  `ALOOKUP fs fld = SOME ftv` by
    metis_tac[vyperPlaceTypingTheory.struct_field_slot_type] >>
  gvs[] >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx` by
    fs[expr_sim_inv_def] >>
  drule_all augassign_storage_field_read >> strip_tac >>
  `well_formed_type_value ftv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type ftv cur` by
    metis_tac[
      vyperTypeStatePreservationTheory.read_storage_slot_well_typed_value] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `word_value cur` by metis_tac[word_value_type_typed] >>
  drule_all eval_augassign_attr_storage >> strip_tac >>
  drule_all expr_body_pre_word_result >> strip_tac >>
  qexistsl_tac [`cur`, `r1`, `es1`] >> simp[] >>
  rpt conj_tac
  >~ [`encode_value`]
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `value_has_type ftv v` by
        (qpat_x_assum `bop_result _ _ _ _ _ _ _ = _` mp_tac >>
         `bop_result cx ty bop [ty; expr_type e] cur v2 es1 =
          case evaluate_binop
            (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
            ftv bop cur v2 of INL v => INL v | INR err => INR (Error err)` by
           (irule bop_result_augassign >> simp[]) >>
         strip_tac >> gvs[AllCaseEqs()] >>
         irule vyperTypeBuiltinsTheory.well_typed_binop_success_type >>
         goal_assum (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
         goal_assum (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
      `word_value v` by metis_tac[word_value_type_typed] >>
      `is_word_type ty` by metis_tac[word_value_type_word] >>
      drule_all encode_value_word_typed >>
      simp[typed_val_to_w256_word_value])
  >~ [`storage_dead`]
  >- (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
      qexistsl_tac [`fld`, `fs`, `ftv`, `src`, `id`] >>
      simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
      metis_tac[word_value_type_word, word_type_slot_size])
  >~ [`bop_result`]
  >- (Cases_on `r1` >> gvs[] >>
      qmatch_asmsub_abbrev_tac `evaluate_binop u ftv bop cur v2` >>
      `bop_result cx ty bop [ty; expr_type e] cur v2 es1 =
        case evaluate_binop u ftv bop cur v2 of
          INL v => INL v | INR err => INR (Error err)` by
        (simp[Abbr `u`] >> irule bop_result_augassign >> simp[]) >>
      Cases_on `evaluate_binop u ftv bop cur v2` >> gvs[]) >>
  metis_tac[]
QED

Theorem augassign_attr_storage_code_parts[local]:
  !cenv lctx ty0 ty src id fld sid fty fsz bop e sa c sf tr slot.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
          (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
        sa = (dst, sn) /\
      emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     Once compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Lit slot; Lit (n2w off)] sa` >>
  Cases_on `emit_op ADD [Lit slot; Lit (n2w off)] sa` >>
  rename1 `_ = (dst, sn)` >>
  asm_simp_tac (srw_ss())
    [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op load [dst] sn` >>
  Cases_on `emit_op load [dst] sn` >> rename1 `_ = (cur, s1)` >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs, s2)` >>
  Cases_on `compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op, s3)` >>
  qmatch_goalsub_abbrev_tac `emit_void store [dst; res_op] s3` >>
  Cases_on `emit_void store [dst; res_op] s3` >>
  asm_simp_tac (srw_ss())
    [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
     oneTheory.one] >>
  strip_tac >> gvs[oneTheory.one]
QED

Theorem augassign_storage_load_frag[local]:
  !ctx func cenv cx es sa sn s1 dst cur s0 tr slot off ty ftv v R.
    emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst, sn) /\
    emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
    local_ptrs_reserved cenv sa /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\ word_value v /\
    (!s. stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value v) (slot + n2w off) es s) ==>
    frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand dst s = SOME (slot + n2w off) /\
           eval_operand cur s = SOME (val_to_w256 v) /\
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
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `frag_exec ctx sa sn
     (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
     (\s. stmt_state_rel ctx func cenv cx es s /\
       eval_operand dst s = SOME (slot + n2w off) /\
       (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
              lookup_var x s = SOME u) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                FLOOKUP s.vs_allocas aid = SOME b) /\
       s.vs_memory = s0.vs_memory) R` by
    (irule emit_op_frag >> simp[] >>
     qexistsl_tac [`[Lit slot; Lit (n2w off)]`, `ADD`] >>
     simp[is_terminator_def] >>
     rpt strip_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  first_x_assum (mp_then Any irule frag_exec_then) >> fs[ci_mono_def] >>
  rpt strip_tac >>
  `(if tr then tload (slot + n2w off) t else sload (slot + n2w off) t) =
     val_to_w256 v` by
    (`storage_holds cx tr ty (Value v) (slot + n2w off) es t` by
       metis_tac[] >>
     drule_all storage_holds_load >> simp[typed_val_to_w256_word_value]) >>
  `frag_exec ctx sn s1
     (\s. s = t /\ stmt_state_rel ctx func cenv cx es s)
     (\s. stmt_state_rel ctx func cenv cx es s /\
       eval_operand cur s = SOME (val_to_w256 v) /\
       (!x u. not_fresh_at sn x /\ lookup_var x t = SOME u ==>
              lookup_var x s = SOME u) /\
       (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
                FLOOKUP s.vs_allocas aid = SOME b) /\
       s.vs_memory = t.vs_memory) R` by
    (irule emit_op_frag >> simp[] >>
     qexistsl_tac [`[Var d]`, `if tr then TLOAD else SLOAD`] >>
     simp[] >> conj_tac >- (Cases_on `tr` >> simp[is_terminator_def]) >>
     rpt strip_tac >> Cases_on `tr` >> fs[] >>
     simp[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  pop_assum (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  gvs[eval_operand_def] >> metis_tac[]
QED

Theorem augassign_attr_storage_frag[local]:
  !ctx func cenv cx es ty bop e el sa sn dst cur s1 rhs s2 res_op s3 sf s0
   tr slot off ftv v1 r1 es1 res es'.
    emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst, sn) /\
    emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
    compile_binop bop cur rhs ty NONE el s2 = (res_op, s3) /\
    emit_void (if tr then TSTORE else SSTORE) [dst; res_op] s3 = ((), sf) /\
    cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
    (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\ word_value v1 /\
    (!s. stmt_state_rel ctx func cenv cx es s ==>
         storage_holds cx tr ty (Value v1) (slot + n2w off) es s) /\
    expr_sim ctx func cenv cx ty e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\
    expr_res_ok r1 /\
    (!v2. r1 = INL v2 ==>
      word_value v2 /\ is_word_type (expr_type e) /\
      IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
      expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
      binop_frag ctx func cenv cx bop ty ty NONE el [ty; expr_type e]
        v1 v2 es1) /\
    (!v2 v. r1 = INL v2 /\
      bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v ==>
      encode_value ftv v = SOME [(0, val_to_w256 v)] /\
      write_storage_slot cx tr (slot + n2w off) ftv v es1 = (res, es')) /\
    (!u st. storage_dead cx tr (update_storage (slot + n2w off) u st) =
      storage_dead cx tr st) ==>
    frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
          lookup_var x t = SOME u) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP t.vs_allocas aid = SOME b))
      (expr_exit (case r1 of
        INL v2 => bop_result cx ty bop [ty; expr_type e] v1 v2 es1
      | INR ex => INR ex))
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sn /\ ci_mono sn s1 /\ ci_mono s3 sf` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends s2 s3` by metis_tac[compile_binop_shape] >>
  `cs_extends sa s1 /\ cs_extends sa s3 /\ cs_extends s3 sf /\
   sa.cs_next_var <= s1.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s3 func` by metis_tac[fn_has_code_split] >>
  `(!z. dst = Var z ==> not_fresh_at s1 z) /\ (!l. dst <> Label l) /\
   (!z. cur = Var z ==> not_fresh_at s1 z) /\ (!l. cur <> Label l)` by
    (imp_res_tac emitted_insts_emit_op >> gvs[] >>
     fs[not_fresh_at_def, ASCIInumbersTheory.toString_11, ci_mono_def]) >>
  `!R. frag_exec ctx sa s1
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
      eval_operand dst s = SOME (slot + n2w off) /\
      eval_operand cur s = SOME (val_to_w256 v1) /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
        lookup_var x s = SOME u) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP s.vs_allocas aid = SOME b)) R` by
    (gen_tac >> irule augassign_storage_load_frag >> metis_tac[]) >>
  drule_all augassign_load_bop_frag >> strip_tac >>
  irule frag_exec_seq_pointwise >>
  qpat_assum `frag_exec _ sa s3 _ _ _` (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `?d. dst = Var d` by
    (qpat_assum `emit_op ADD _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  gvs[eval_operand_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  irule frag_exec_weaken >>
  irule_at Any store_var_frag >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`res_op`, `d`, `\r. F`] >> simp[]
QED

(* x.f's place, value and type are read for a storage or transient struct
   x where expr_sim_inv holds: the read decodes x's whole value. *)
Theorem augassign_attr_storage_place:
  !cx cenv env es src id fld ts tr sid id_str slot fty fsz.
    expr_sim_inv cenv cx env es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    IS_SOME (evaluate_type (get_tenv cx) (StructT sid)) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?p cur ptv observations.
      eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
        es = (INL p, es with storage_trace := observations) /\
      read_place cx p es = (INL cur, es) /\
      place_type_value cx p es = (INL ptv, es)
Proof
  rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  drule vyperPlaceResultTypingTheory.struct_field_slot_exists >>
  strip_tac >>
  `?v0. read_storage_slot cx tr (n2w slot) (StructTV fs) es = (INL v0, es)` by
    (irule toplevel_storage_read_decodes >> gvs[expr_sim_inv_def] >>
     metis_tac[]) >>
  drule_all read_storage_slot_field >> strip_tac >>
  drule_all eval_target_place_attr_toplevel_field >> strip_tac >>
  simp[read_place_def]
QED

(* self.x.f op= e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of x's struct of a word type ty, for
   every outcome: e's errors and the operator's (overflow, division by
   zero) exit, and on a value of the operator its word is stored at f's
   slot.  e may call internal functions: its simulation at ty is a
   premise. *)
Theorem compile_augassign_attr_storage_case:
  !ctx func cx lctx RetQ cenv ty0 env src id fld sid ty fsz bop e es res es'
   ts tr id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    expr_sim ctx func cenv cx ty e es /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (ty, fsz) /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all augassign_attr_storage_code_parts >> strip_tac >>
  drule_all augassign_attr_storage_source >> strip_tac >> gvs[] >>
  rename1 `value_has_type ftv v1` >>
  qmatch_asmsub_abbrev_tac `storage_holds cx tr ty (Value v1)
    (n2w slot + n2w off) es` >>
  `!s. stmt_state_rel ctx func cenv cx es s ==>
       storage_holds cx tr ty (Value v1) (n2w slot + n2w off) es s` by
    metis_tac[] >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l)` by
    (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     fs[well_formed_type_def]) >>
  `!v2. r1 = INL v2 ==>
    word_value v2 /\ is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    expr_res_ok (bop_result cx ty bop [ty; expr_type e] v1 v2 es1) /\
    binop_frag ctx func cenv cx bop ty ty NONE
      (if bop = Exp then expr_int_literal e else NONE)
      [ty; expr_type e] v1 v2 es1` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v2. r1 = INL v2 ==> ?tv2. _` drule >> strip_tac >>
     simp[optionTheory.IS_SOME_EXISTS] >> conj_tac
     >- (qpat_x_assum `case r1 of _ => _ | _ => _` mp_tac >>
         simp[] >>
         Cases_on `bop_result cx ty bop [ty; expr_type e] v1 v2 es1` >>
         gvs[expr_res_ok_def, stmt_res_ok_def, bop_result_def, AllCaseEqs()]) >>
     gvs[] >> drule eval_expr_read_INL >> strip_tac >>
     `!n. expr_int_literal e = SOME n ==> v2 = IntV n` by
       metis_tac[eval_expr_int_literal_agrees] >>
     `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
       (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
     `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
       (strip_tac >> gvs[nonneg_int_literal_def,
                         GSYM expr_int_literal_value] >>
        Cases_on `expr_int_literal e` >> gvs[]) >>
     irule binop_frag_word_typed >> simp[] >> metis_tac[]) >>
  `!v2 v. r1 = INL v2 /\
    bop_result cx ty bop [ty; expr_type e] v1 v2 es1 = INL v ==>
    encode_value ftv v = SOME [(0, val_to_w256 v)] /\
    write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 = (res, es')` by
    (rpt strip_tac >> gvs[]) >>
  drule_all augassign_attr_storage_frag >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`t`, `cenv`] >> gvs[] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
      simp[is_terminator_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  Cases_on `r1` >> gvs[]
  >- (rename1 `bop_result cx ty bop [ty; expr_type e] v1 v2 es1` >>
      Cases_on `bop_result cx ty bop [ty; expr_type e] v1 v2 es1` >>
      gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  metis_tac[expr_exit_INR_type]
QED
