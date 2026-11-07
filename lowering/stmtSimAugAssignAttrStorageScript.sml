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
 * at dst (SSTORE or TSTORE).  The proof composes the pieces as
 * stmtSimAugAssignAttr does for a field of a local struct: the ADD and the
 * load are straight-line code with no GAS, e's counted outcome comes from
 * its simulation, and the operator and the store follow.  As there, **
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
 *   eval_augassign_storage_place, augassign_storage_place_rhs_exception,
 *   augassign_storage_place_rhs_normal,
 *   augassign_storage_place_rhs_admissible,
 *   augassign_storage_place_binop_admissible,
 *   augassign_storage_place_rhs_exempt, augassign_attr_storage_code_parts,
 *   augassign_attr_storage_load_path, augassign_attr_storage_store_post_path
 *)

Theory stmtSimAugAssignAttrStorage
Ancestors
  exprBopSimDefs
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
  exprSimBinopFrag exprSimOperators exprSimLeaves exprSimAttributeFields
  exprSimUnwrap
   stmtSimDeclMem stmtSimAssign stmtSimAssignStorage stmtSimAugAssign
  stmtSimAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignAttr
  stmtSimAugAssignStorage exprSafeOperand exprWordOperand exprBopSimProps
  exprSimMemoryPath stmtSimDeclGas gasSummaryCompose
  gasContext gasOutcome gasSummary gasExemptCert fragGasPath fragGasMode
  fragGasPathMem fragGasSeq stmtSimDeclPath stmtSimDeclCompose
  exprSimTopLevelProps exprOpenPrimitives vyperExprNoControl
  vyperStorageLayoutSafety vyperStorageBackend
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
      es = (INL (StoragePlace tr (n2w slot + n2w off) ftv), es) /\
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

(* ===== The source, for any target at a fixed storage place ===== *)

(* The target's place, its value and its type are read before e; e's
   evaluation and the operator follow, and the slot is written. *)
Theorem eval_augassign_storage_place:
  !cx tgt tr k ftv es v0.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv), es')) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) ==>
    !gs ty bop e.
      eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
      (do v <- bind (eval_expr cx e) (read_result cx);
          r <- lift_sum (evaluate_binop
            (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
            ftv bop v0 v);
          write_storage_slot cx tr k ftv r od) (es with gas_obs := gs)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `read_storage_slot cx tr k ftv (es with gas_obs := gs) =
     (INL v0, es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       write_place_def, place_type_value_def, return_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_storage_place_rhs_exception:
  !cx tgt tr k ftv es v0 e gs ex ee.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv), es')) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INR ex, ee) ==>
    !ty bop.
      eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
        (INR ex, ee)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  drule_all eval_augassign_storage_place >>
  disch_then (qspecl_then [`gs`, `ty`, `bop`, `e`] SUBST1_TAC) >>
  simp[Once bind_def]
QED

Theorem augassign_storage_place_rhs_normal:
  !cx tgt tr k ftv es v0 e gs v ee.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv), es')) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v, ee) ==>
    !ty bop.
      eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop v0 v)) (write_storage_slot cx tr k ftv) ee
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  drule_all eval_augassign_storage_place >>
  disch_then (qspecl_then [`gs`, `ty`, `bop`, `e`] SUBST1_TAC) >>
  simp[Once bind_def] >> rewrite_tac[ETA_AX]
QED

Theorem augassign_storage_place_rhs_admissible:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv), es')) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  drule_all augassign_storage_place_rhs_exception >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem augassign_storage_place_binop_admissible:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv), es')) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     ftv bop v0 v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop v0 v` >- simp[expr_res_ok_def] >>
  rename1 `_ = INR err` >>
  `eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
     (INR (Error err), ee)` by
    (drule_all augassign_storage_place_rhs_normal >>
     disch_then (qspecl_then [`ty`, `bop`] SUBST1_TAC) >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  `stmt_res_ok lctx (INR (Error err))` by metis_tac[gas_admissible_result] >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

(* An exemption certificate of e lifts to the statement's: the place, its
   value and its type are read with no GAS before e. *)
Theorem augassign_storage_place_rhs_exempt:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv), es')) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  gas_marked_path memory ctx func s0 0 (OK t) /\ ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func) (eval_target_place cx tgt)
     (es,s0) [] (INL (StoragePlace tr k ftv)) es (OK t)` by
    simp[gas_marked_exec_def, gas_explicit_def] >>
  `ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()) =
   do p <- eval_target_place cx tgt;
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec memory (ctx,func) (read_place cx (StoragePlace tr k ftv))
     (es with gas_obs := [],t) [] (INL v0)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         metis_tac[read_storage_slot_gas_obs]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* ===== The code ===== *)

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

(* The ADD of f's slot offset to x's slot and the SLOAD or TLOAD of the
   sum: straight-line code with no GAS.  The loaded word is whatever the
   storage holds at the sum in every state related to es. *)
Theorem augassign_attr_storage_load_path:
  emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst,sm) /\
  emit_op (if tr then TLOAD else SLOAD) [dst] sm = (cur,sn) /\
  fn_has_code sa sn func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  (!s'. stmt_state_rel ctx func cenv cx es s' ==>
        (if tr then tload (slot + n2w off) s'
         else sload (slot + n2w off) s') = w) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand dst t = SOME (slot + n2w off) /\
      eval_operand cur t = SOME w /\
      ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_memory = s.vs_memory /\
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
  `eval_operand (Lit slot) s = SOME slot` by simp[eval_operand_def] >>
  drule_all attr_add_marked_path >> strip_tac >>
  `(if tr then tload (slot + n2w off) q else sload (slot + n2w off) q) = w` by
    (first_x_assum irule >> simp[]) >>
  qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var)) w q)
    with vs_inst_idx := SUC q.vs_inst_idx` >>
  `gas_marked_path F ctx func q 0 (OK t)` by
    (simp[Abbr `t`, gas_marked_path_def, NoAsms] >>
     irule emit_op_zero_path >> simp[] >>
     qexistsl_tac [`[dst]`, `cur`, `if tr then TLOAD else SLOAD`, `sn`] >>
     Cases_on `tr` >> gvs[is_terminator_def] >> gen_tac >>
     simp[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  qexists_tac `t` >> conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[] >>
  qpat_x_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[Abbr `t`, eval_operand_def, update_var_def,
    lookup_var_def, not_fresh_at_def, FLOOKUP_UPDATE] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS]
QED

(* The SSTORE or TSTORE of the operator's word at the saved address writes
   the slot and lands with the full statement post. *)
Theorem augassign_attr_storage_store_post_path:
  !ctx func cx lctx cenv tr dst op st sf s ee k ftv w sa s0.
    emit_void (if tr then TSTORE else SSTORE) [dst; op] st = ((), sf) /\
    fn_has_code st sf func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx ee s /\
    (!u sto. storage_dead cx tr (update_storage k u sto) =
             storage_dead cx tr sto) /\
    encode_value ftv w = SOME [(0, typed_val_to_w256 ftv w)] /\
    eval_operand dst s = SOME k /\
    eval_operand op s = SOME (typed_val_to_w256 ftv w) /\
    (!x wd. not_fresh_at sa x /\ lookup_var x s0 = SOME wd ==>
            lookup_var x s = SOME wd) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    alloca_frame cenv es0 sa s0 cenv ee s ==>
    ?fin last. write_storage_slot cx tr k ftv w ee = (INL (),fin) /\
      gas_marked_path F ctx func s 0 (OK last) /\
      stmt_post ctx func cx lctx cenv cenv sa sf es0 s0 (INL ()) fin last
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `write_storage_slot cx tr k ftv w ee` >>
  `~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  `gas_marked_path F ctx func s 0
     (OK ((if tr then tstore k (typed_val_to_w256 ftv w) s
           else sstore k (typed_val_to_w256 ftv w) s)
       with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[dst;op]`, `if tr then TSTORE else SSTORE`, `[]`,
                   `st`, `sf`] >>
     Cases_on `tr` >> gvs[emit_void_def,emit_inst_def,is_terminator_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     fs[mk_inst_def,exec_write2_def]) >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    (Cases_on `tr` >>
     gvs[emit_void_def,comp_bind_def,fresh_id_def,comp_ignore_bind_def,
         comp_return_def,emit_def]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `r.scopes = ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_storage_slot_scopes] >>
  `alloca_frame cenv es0 sa s0 cenv r
     ((if tr then tstore k (typed_val_to_w256 ftv w) s
       else sstore k (typed_val_to_w256 ftv w) s)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule alloca_frame_same_state >> qexists_tac `s` >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, LET_THM] >>
     qpat_x_assum `alloca_frame _ _ _ _ _ ee s` mp_tac >>
     simp[alloca_frame_def]) >>
  goal_assum (drule_at Any) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  Cases_on `tr` >> gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

(* ===== The statement ===== *)

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
    ?p cur ptv.
      eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
        es = (INL p, es) /\
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
  !ctx func cx lctx RetQ cenv ty0 env src id fld sid ty fsz bop e es
   ts tr id_str slot.
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
      (eval_stmt cx
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx /\
   storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[expr_sim_inv_def, stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all augassign_attr_storage_code_parts >> strip_tac >> gvs[] >>
  `?fs off ftv.
     evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
     struct_field_slot fs fld = SOME (off, ftv)` by
    (Cases_on `eval_stmt cx (AugAssign ty
       (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e) es` >>
     rename1 `_ = (res, es')` >>
     `es with gas_obs := es.gas_obs = es` by
       simp[evaluation_state_component_equality] >>
     `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
     `!m. res <> INR (Error (TypeError m))` by
       (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
     drule_all augassign_storage_field_place >> metis_tac[]) >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  drule_all struct_field_type >> strip_tac >>
  `ALOOKUP fs fld = SOME ftv` by
    metis_tac[vyperPlaceTypingTheory.struct_field_slot_type] >>
  gvs[] >>
  qabbrev_tac `off = struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` >>
  drule_all augassign_storage_field_read >> strip_tac >>
  rename1 `read_storage_slot _ _ _ _ _ = (INL fv, _)` >>
  `well_formed_type_value ftv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type ftv fv` by
    metis_tac[
      vyperTypeStatePreservationTheory.read_storage_slot_well_typed_value] >>
  `word_value fv` by metis_tac[word_value_type_typed] >>
  `!es'. eval_target_place cx
     (AttributeTarget (TopLevelNameTarget (src,id)) fld) es' =
     (INL (StoragePlace tr (n2w slot + n2w off) ftv), es')` by
    (gen_tac >> irule (cj 1 eval_target_place_attr_toplevel_field) >>
     metis_tac[]) >>
  `!s'. stmt_state_rel ctx func cenv cx es s' ==>
     (if tr then tload (n2w slot + n2w off) s'
      else sload (n2w slot + n2w off) s') = val_to_w256 fv` by
    (rpt strip_tac >>
     `storage_holds cx tr ty (Value fv) (n2w slot + n2w off) es s'` by
       metis_tac[] >>
     drule_all storage_holds_load >> simp[typed_val_to_w256_word_value]) >>
  `cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 sb` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def,
              pairTheory.SND, compile_expr_grows, compile_binop_grows] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `safe_operand s1 dst /\ safe_operand s1 cur` by
    metis_tac[emit_op_safe_operand, safe_operand_mono, ci_mono_emit_op,
              ci_mono_def, pairTheory.SND] >>
  drule_all augassign_attr_storage_load_path >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule_all augassign_storage_place_rhs_admissible >> simp[]) >>
  drule_all augassign_load_rhs_counted >> strip_tac
  >- suspend "rhs_summary" >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  drule_all augassign_storage_place_rhs_exempt >> strip_tac >>
  metis_tac[]
QED

Resume compile_augassign_attr_storage_case[rhs_summary]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
  >- suspend "rhs_normal" >>
  Cases_on `res` >- gvs[expr_exit_def] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >>
      qspecl_then [`cx`, `AttributeTarget (TopLevelNameTarget (src,id)) fld`,
        `tr`, `n2w slot + n2w off`, `ftv`, `es`, `fv`, `e`,
        `gas_explicit marks s0.vs_gas_readings ++ tail`, `y`,
        `es_end with gas_obs := tail`]
        mp_tac augassign_storage_place_rhs_exception >>
      impl_tac >- simp[] >> simp[]) >>
  disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_attr_storage_case[rhs_normal]:
  gvs[] >>
  rename1 `expr_post _ _ _ _ _ _ s1 s2 t _ v rhs t'` >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []) =
     (INL v,es_end with gas_obs := [])` by
    metis_tac[gas_marked_exec_observation] >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] fv v
     (es_end with gas_obs := []))` by
    (drule_all augassign_storage_place_binop_admissible >> simp[]) >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    augassign_attr_operator_counted >>
  disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (qspecl_then [`dst`, `n2w slot + n2w off`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  `bop_result cx ty bop [ty;expr_type e] fv v (es_end with gas_obs := []) =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  strip_tac
  >- suspend "store" >>
  gvs[] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v` >- gvs[expr_exit_def, exit_result_def] >>
  gvs[] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error y)`, `es_end`, `r`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> conj_tac
      >- (gen_tac >>
          qspecl_then [`cx`,
            `AttributeTarget (TopLevelNameTarget (src,id)) fld`,
            `tr`, `n2w slot + n2w off`, `ftv`, `es`, `fv`, `e`,
            `gas_explicit marks s0.vs_gas_readings ++ tail`, `v`,
            `es_end with gas_obs := tail`]
            mp_tac augassign_storage_place_rhs_normal >>
          impl_tac >- simp[] >>
          disch_then (qspecl_then [`ty`, `bop`] SUBST1_TAC) >>
          simp[bind_def, lift_sum_def, raise_def]) >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def]
QED

Resume compile_augassign_attr_storage_case[store]:
  gvs[] >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     ftv bop fv v = INL result` by
    (Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ftv bop fv v` >> gvs[]) >>
  qpat_x_assum `INL result = _` kall_tac >>
  `well_formed_type (get_tenv cx) ty` by simp[well_formed_type_def] >>
  drule_all augassign_attr_binop_ready >>
  disch_then (qspecl_then [`func`, `es_end with gas_obs := []`, `ctx`]
    strip_assume_tac) >>
  `value_has_type ftv result` by
    (first_x_assum irule >> irule EQ_TRANS >>
     qexists_tac `case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ftv bop fv v of INL w => INL w | INR err => INR (Error err)` >>
     conj_tac >- (irule bop_result_augassign >> simp[]) >>
     simp[]) >>
  `encode_value ftv result = SOME [(0, typed_val_to_w256 ftv result)]` by
    metis_tac[encode_value_word_typed] >>
  `!u' st. storage_dead cx tr (update_storage (n2w slot + n2w off) u' st) =
           storage_dead cx tr st` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
     qexistsl_tac [`fld`, `fs`, `ftv`, `src`, `id`] >>
     simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
     metis_tac[word_value_type_word, word_type_slot_size]) >>
  `s1.cs_next_var <= s2.cs_next_var` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, ci_mono_def,
              pairTheory.SND] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w` by
    (fs[expr_post_def] >> rpt strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `eval_operand res_op u = SOME (typed_val_to_w256 ftv result)` by
    simp[typed_val_to_w256_word_value] >>
  `MAP FDOM es_end.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv es t` by
    (irule alloca_frame_of_mem_frame >> simp[] >> metis_tac[]) >>
  `alloca_frame cenv es s1 t cenv es_end t'` by
    (drule expr_post_alloca_frame >>
     simp[]) >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `alloca_frame cenv es_end s2 t' cenv es_end u` by
    (irule alloca_frame_of_mem_frame >>
     fs[expr_post_def] >> metis_tac[]) >>
  `sa.cs_next_id <= s1.cs_next_id /\
   s1.cs_next_id <= s2.cs_next_id` by
    (conj_tac
     >- (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
              comp_ignore_bind_def, comp_return_def, emit_def] >> simp[]) >>
     metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, ci_mono_def,
               pairTheory.SND]) >>
  `alloca_frame cenv es s1 t cenv es_end u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`, `es_end`, `t'`, `s2`] >>
     fs[expr_post_def] >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv es_end u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`, `es`, `t`, `s1`] >>
     simp[]) >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `cenv`, `tr`, `dst`, `res_op`,
    `s3`, `sb`, `u`, `es_end with gas_obs := []`, `n2w slot + n2w off`,
    `ftv`, `result`, `sa`, `s0`]
    mp_tac (Q.INST [`es0` |-> `es`] augassign_attr_storage_store_post_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `!g. write_storage_slot cx tr (n2w slot + n2w off) ftv result
         (es_end with gas_obs := g) = (INL (), fin with gas_obs := g)` by
    (gen_tac >>
     qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     once_rewrite_tac[write_storage_slot_gas_obs] >> simp[] >>
     strip_tac >> gvs[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `fin`, `OK last`] >>
  simp[stmtSimDeclComposeTheory.stmt_post_end_gas_obs] >>
  fs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qspecl_then [`cx`, `AttributeTarget (TopLevelNameTarget (src,id)) fld`,
        `tr`, `n2w slot + n2w off`, `ftv`, `es`, `fv`, `e`,
        `gas_explicit marks s0.vs_gas_readings ++ tail`, `v`,
        `es_end with gas_obs := tail`]
        mp_tac augassign_storage_place_rhs_normal >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`ty`, `bop`] SUBST1_TAC) >>
      simp[bind_def, lift_sum_def, return_def]) >>
  `gas_marked_path F ctx func t' 0 (OK last)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]
QED

Finalise compile_augassign_attr_storage_case
