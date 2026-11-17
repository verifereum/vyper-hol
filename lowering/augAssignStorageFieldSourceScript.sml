(* Source evaluation and finite observed-root facts for storage-field AugAssign. *)
Theory augAssignStorageFieldSource
Ancestors
  stmtSimAssignAttrStorage stmtSimAugAssignStorage stmtSimAugAssign
  exprSimAttributeFields exprBopSimProps exprSimDefs exprLoweringProps
  accountsRelProps loweringPosts loweringStateRelDefs stmtSimDefs
  gasSummary gasContext gasExemptCert gasSummaryCompose
  fragGasMode fragGasPathMem gasStorage vyperExprNoControl
  vyperStorageFootprint vyperStorageTrace vyperLookupStorage
  vyperInterpreter vyperState vyperStorageBackend vyperValue
  vyperTypeSystem vyperTyping vyperAST venomState list
Libs
  monadsyntax

(* x.f's place for a storage or transient struct x: x's slot plus f's slot
   offset, at f's type; looking x up records the root it observes. *)
Theorem eval_target_place_attr_toplevel_field:
  !cx src id fld es ts tr typ id_str slot fs off ftv.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) ==>
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (INL (StoragePlace tr (n2w slot + n2w off) ftv),
            es with storage_trace :=
              es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) /\
    place_type_value cx (StoragePlace tr (n2w slot + n2w off) ftv) es =
      (INL ftv, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, extend_place_def, extend_storage_place_def,
       get_place_def, place_type_value_def, ignore_bind_def,
       record_storage_event_def]
QED

(* A non-type-error AugAssign has successfully resolved its target. *)
Theorem augassign_storage_field_place:
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

(* An observed struct root's field reads, and in every state related at a
   horizon observing the root, the backend holds the field's value. *)
Theorem augassign_storage_field_read:
  !(H:(bool # bytes32 # type_value) list # num list) cx es tr slot fs fld off
   ftv ty.
    MEM (tr,n2w slot,StructTV fs) (FST H) /\ regions_consistent (FST H) /\
    storage_well_formed_on cx es (FST H) /\
    well_formed_type_value (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    evaluate_type (get_tenv cx) ty = SOME ftv ==>
    ?cur. read_storage_slot cx tr (n2w slot + n2w off) ftv es =
            (INL cur, es) /\
          !ctx func cenv s.
            stmt_state_rel H ctx func cenv cx es s ==>
            storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s
Proof
  rpt gen_tac >> strip_tac >>
  `?v. read_storage_slot cx tr (n2w slot) (StructTV fs) es = (INL v, es)` by
    (drule_all observed_region_read >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all read_storage_slot_field >> strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32))
     (StructTV fs)` by
    fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  drule_all vyperLookupStorageTheory.storage_field_slots_in_range >>
  strip_tac >>
  `!st. storage_read_live H tr st (n2w slot) (StructTV fs)` by
    metis_tac[observed_storage_region_read_live] >>
  `w2n ((n2w slot):bytes32) + type_slot_size (StructTV fs) <=
   dimword (:256)` by
    (fs[vyperStorageFootprintTheory.regions_consistent_def] >>
     qpat_x_assum `!b slot tv. MEM _ _ ==> _` (drule_then mp_tac) >> simp[]) >>
  qexists_tac `fv` >> simp[storage_holds_def, read_result_def, return_def] >>
  rpt strip_tac >>
  irule storage_range_agree_field >> goal_assum (drule_at Any) >>
  irule (INST_TYPE [alpha |-> ``:256``] storage_range_agree_of_live) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`H`, `tr`] >> simp[] >> Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def]
QED

(* ===== The source, for any target at a fixed storage place ===== *)

(* The target's place, its value and its type are read before e; e's
   evaluation and the operator follow, and the slot is written. *)
Theorem eval_augassign_storage_place:
  !cx tgt tr k ftv evs es v0.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv),
              es' with storage_trace := es'.storage_trace ++ evs)) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) ==>
    !gs ty bop e.
      eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
      (do v <- bind (eval_expr cx e) (read_result cx);
          r <- lift_sum (evaluate_binop
            (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
            ftv bop v0 v);
          write_storage_slot cx tr k ftv r od)
        (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `read_storage_slot cx tr k ftv
     (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>) =
   (INL v0,
    es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>)` by
    (drule read_storage_slot_gas_obs >>
     disch_then (qspec_then `gs` assume_tac) >>
     drule read_storage_slot_storage_trace >>
     disch_then (qspec_then `es.storage_trace ++ evs` mp_tac) >> simp[]) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       write_place_def, place_type_value_def, return_def] >>
  qmatch_goalsub_abbrev_tac `eval_expr cx e es1` >>
  Cases_on `eval_expr cx e es1` >>
  rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_storage_place_rhs_exception:
  !cx tgt tr k ftv evs es v0 e gs ex ee.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv),
              es' with storage_trace := es'.storage_trace ++ evs)) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) /\
    bind (eval_expr cx e) (read_result cx)
      (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>) =
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
  !cx tgt tr k ftv evs es v0 e gs v ee.
    (!es'. eval_target_place cx tgt es' =
             (INL (StoragePlace tr k ftv),
              es' with storage_trace := es'.storage_trace ++ evs)) /\
    read_storage_slot cx tr k ftv es = (INL v0, es) /\
    bind (eval_expr cx e) (read_result cx)
      (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>) =
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
           (INL (StoragePlace tr k ftv),
            es' with storage_trace := es'.storage_trace ++ evs)) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with storage_trace := es.storage_trace ++ evs)
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `bind (eval_expr cx e) (read_result cx)
     (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>) =
   (INR ex, ee)` by fs[] >>
  drule_all augassign_storage_place_rhs_exception >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  qmatch_goalsub_abbrev_tac `eval_expr cx e es1` >>
  Cases_on `eval_expr cx e es1` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem augassign_storage_place_binop_admissible:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv),
            es' with storage_trace := es'.storage_trace ++ evs)) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx)
    (es with <|gas_obs := gs; storage_trace := es.storage_trace ++ evs|>) =
    (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee)
Proof
  strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee) <=>
   expr_res_ok (case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     ftv bop v0 v of INL w => INL w | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
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
           (INL (StoragePlace tr k ftv),
            es' with storage_trace := es'.storage_trace ++ evs)) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  gas_marked_path memory ctx func s0 0 (OK t) /\ ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with <|gas_obs := []; storage_trace := es.storage_trace ++ evs|>,t)
    marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func) (eval_target_place cx tgt)
     (es,s0) [] (INL (StoragePlace tr k ftv))
     (es with storage_trace := es.storage_trace ++ evs) (OK t)` by
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
     (es with <|gas_obs := []; storage_trace := es.storage_trace ++ evs|>,t)
     [] (INL v0)
     (es with <|gas_obs := []; storage_trace := es.storage_trace ++ evs|>)
     (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         drule read_storage_slot_gas_obs >>
         disch_then (qspec_then `tail` assume_tac) >>
         drule read_storage_slot_storage_trace >>
         disch_then (qspec_then `es.storage_trace ++ evs` mp_tac) >> simp[]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* Looking the target up records evs before anything else runs: a trace
   that is bad with evs recorded stays bad through the whole statement. *)
Theorem augassign_storage_place_bad_root:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv),
            es' with storage_trace := es'.storage_trace ++ evs)) /\
  ~storage_trace_domain cx st0 (es.storage_trace ++ evs) ==>
  gas_bad_storage_at cx st0 (eval_stmt cx (AugAssign ty tgt bop e))
    es s0 marks
Proof
  strip_tac >>
  `gas_bad_storage_at cx st0
     (ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()))
     es s0 marks` by
    (`ignore_bind (eval_stmt cx (AugAssign ty tgt bop e)) (return ()) =
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
     irule gasStorageTheory.gas_bad_storage_at_bind_left >> conj_tac
     >- (gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_read_place] >>
         gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_place_type] >>
         gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[augassign_rhs_trace_frame] >> gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_lifts] >>
         gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
         simp[vyperStorageTraceTheory.storage_trace_frame_write_place,
              vyperStorageTraceTheory.storage_trace_frame_return]) >>
     simp[gasStorageTheory.gas_bad_storage_at_def]) >>
  pop_assum mp_tac >> rewrite_tac[gasStorageTheory.gas_bad_storage_at_def] >>
  strip_tac >> gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx stmt est` >>
  Cases_on `eval_stmt cx stmt est` >> rename1 `_ = (res, ee)` >>
  Cases_on `res` >> simp[ignore_bind_def, bind_def, return_def]
QED

(* A bad trace at the end of e, run with the target's events recorded,
   stays bad through the operator and the slot write. *)
Theorem augassign_storage_place_rhs_bad_storage:
  (!es'. eval_target_place cx tgt es' =
           (INL (StoragePlace tr k ftv),
            es' with storage_trace := es'.storage_trace ++ evs)) /\
  read_storage_slot cx tr k ftv es = (INL v0, es) /\
  gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
    (es with storage_trace := es.storage_trace ++ evs) s0 marks ==>
  gas_bad_storage_at cx st0 (eval_stmt cx (AugAssign ty tgt bop e))
    es s0 marks
Proof
  strip_tac >>
  `gas_bad_storage_at cx st0
     (do v <- bind (eval_expr cx e) (read_result cx);
         r <- lift_sum (evaluate_binop
           (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
           ftv bop v0 v);
         write_storage_slot cx tr k ftv r od)
     (es with storage_trace := es.storage_trace ++ evs) s0 marks` by
    (irule gasStorageTheory.gas_bad_storage_at_bind_left >> conj_tac
     >- (gen_tac >> BETA_TAC >>
         irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_write_storage_slot]) >>
     first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >> rewrite_tac[gasStorageTheory.gas_bad_storage_at_def] >>
  strip_tac >> gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
  drule_all eval_augassign_storage_place >>
  disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings ++ tail`,
                           `ty`, `bop`, `e`] SUBST1_TAC) >>
  simp[]
QED

