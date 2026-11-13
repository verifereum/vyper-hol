(*
 * Statement simulation: Assign to a word field of a storage struct (#637)
 *
 * self.x.f = e for a module variable x of struct type in storage or
 * transient storage, f a field of a word type, and e of f's type.  The
 * source evaluates e, takes the place self.x.f (x's slot plus f's slot
 * offset, struct_field_slot), reads e's value and writes its encoding at
 * f's type there.  The lowering evaluates e, adds f's slot offset
 * (struct_field_offset_slots) to x's slot, unwraps the value and stores it
 * with one SSTORE or TSTORE.  The two offsets agree by fields_layout.
 *
 * TOP-LEVEL:
 *   eval_assign_attr_toplevel          — the source run: e's forced
 *                                        value, then write_storage_slot at
 *                                        the field's slot
 *   compile_assign_attr_storage_case  — self.x.f = e, every outcome, e's
 *                                        simulation a premise
 *   compile_assign_attr_storage_stmt_frag — the same for an e with no
 *                                        internal call
 *
 * Helpers: struct_field_slot_alookup, extend_storage_place_attr,
 *   eval_target_place_attr_toplevel, assign_attr_storage_source,
 *   assign_attr_storage_code_parts, store_var_frag, assign_attr_storage_word_suffix
 *)

Theory stmtSimAssignAttrStorage
Ancestors
  exprSimFieldLayout exprSimAggregateChildren exprSimVVFrame immutableWordExecution
  fragGasSeq fragGasPath fragGasMode gasSummary exprSimUnwrap exprSimUnwrapProps
  exprSimSource exprSimMemorySource exprSimMemoryRead exprSimProps gasContext
  stmtSimProps stmtSimDeclPath vyperStorageBackend arithmetic exprOpenPrimitives
  exprSimTopLevelProps stmtSimForced exprSimDefs
  exprSimHypsDefs
  stmtSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec exprSimHyps exprSimLeaves exprSimAttributeFields stmtSimDecl stmtSimDeclMem stmtSimAssign stmtSimAssignMem storageStoreFrame
  stmtSimAssignStorage stmtSimAssignAttr
  vyperStorageTrace vyperStorageFootprint vyperStoragePlaceRegion
  vyperStorageRegionWrite gasStorage
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding accountsRelProps
  vyperInterpreter vyperState vyperStorage vyperValue vyperTyping
  vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

Theorem struct_field_slot_alookup[local]:
  !fs id off ftv.
    struct_field_slot fs id = SOME (off, ftv) ==> ALOOKUP fs id = SOME ftv
Proof
  Induct >> simp[struct_field_slot_def] >> PairCases >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[] >> rename1 `struct_field_slot fs id = SOME q` >>
  PairCases_on `q` >> gvs[] >> metis_tac[]
QED

(* A field of a storage struct: the slot plus the field's slot offset, at
   the field's type; any other case is a type error. *)
Theorem extend_storage_place_attr:
  !cx tr slot tv fld es r es'.
    extend_storage_place cx tr slot tv (AttrSubscript fld) es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv. tv = StructTV fs /\ struct_field_slot fs fld = SOME (off, ftv) /\
                 r = INL (StoragePlace tr (slot + n2w off) ftv)
Proof
  rpt gen_tac >> Cases_on `tv` >>
  simp[extend_storage_place_def, raise_def, bind_def, lift_option_type_def,
       return_def]
  >~ [`struct_field_slot l fld`]
  >- (Cases_on `struct_field_slot l fld` >> simp[raise_def, return_def] >>
      rename1 `SOME q` >> PairCases_on `q` >> simp[return_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_target_place_attr_toplevel:
  !cx src id fld ts tr typ id_str slot es r es'.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    ?fs off ftv.
      evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      r = INL (StoragePlace tr (n2w slot + n2w off) ftv) /\
      es' = es with storage_trace :=
              es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, ignore_bind_def, record_storage_event_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def, extend_place_def, bind_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `extend_storage_place cx tr _ tv _ es0` >>
  Cases_on `extend_storage_place cx tr (n2w slot) tv (AttrSubscript fld) es0` >>
  rename1 `_ = (r1, es1)` >>
  drule extend_storage_place_attr >> strip_tac >>
  Cases_on `r1` >> simp[return_def, get_place_def] >> strip_tac >>
  gvs[Abbr `es0`]
QED

(* self.x.f = e, unless it fails with a type error: e's forced value r,
   and on an error that error, on a value v the write of v at f's slot. *)
Theorem eval_assign_attr_toplevel:
  !cx src id fld e es res es' ts tr typ id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?fs off ftv.
             evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
             struct_field_slot fs fld = SOME (off, ftv) /\
             write_storage_slot cx tr (n2w slot + n2w off) ftv v
               (es1 with storage_trace :=
                  es1.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) =
               (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `eval_expr cx e es = (INL pv, es1)` >>
  Cases_on `read_result cx pv es1` >>
  rename1 `read_result cx pv es1 = (r3, es3)` >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `r3` >> simp[] >>
  Cases_on `eval_target_place cx
              (AttributeTarget (TopLevelNameTarget (src, id)) fld) es1` >>
  rename1 `_ = (r2, es2)` >>
  drule eval_target_place_attr_toplevel >> rpt (disch_then drule) >>
  strip_tac >>
  Cases_on `r2` >> simp[]
  >- (gvs[] >> simp[write_place_def] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Theorem eval_assign_attr_toplevel_action:
  eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld)) e) =
  bind (eval_expr cx e)
    (\pv. do
      v <- read_result cx pv;
      p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src, id)) fld);
      write_place cx p v
    od)
Proof
  simp[Once evaluate_def]
QED

Theorem eval_target_place_attr_toplevel_action[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) ==>
  !es. eval_target_place cx
         (AttributeTarget (TopLevelNameTarget (src, id)) fld) es =
       (INL (StoragePlace tr (n2w slot + n2w off) ftv),
        es with storage_trace :=
          es.storage_trace ++ [StorageRoot tr slot (StructTV fs)])
Proof
  strip_tac >> gen_tac >> simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, lift_option_type_def,
       bind_def, return_def, extend_place_def, extend_storage_place_def,
       get_place_def, ignore_bind_def, record_storage_event_def]
QED

Theorem assign_attr_storage_tail[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) /\
  read_result cx raw ee = (INL v, ee) /\
  write_storage_slot cx tr (n2w slot + n2w off) ftv v
    (ee with storage_trace :=
       ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) = (res, ee') ==>
  !tail.
    (do
      v <- read_result cx raw;
      p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src, id)) fld);
      write_place cx p v
    od) (ee with gas_obs := tail) = (res, ee' with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  drule_all eval_target_place_attr_toplevel_action >> strip_tac >>
  drule read_result_gas_obs >> strip_tac >>
  mp_tac (Q.SPECL [`cx`, `tr`, `n2w slot + n2w off`, `ftv`, `v`,
    `ee with storage_trace :=
       ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]`, `tail`]
    write_storage_slot_gas_obs) >>
  simp[bind_def, write_place_def]
QED

(* What self.x.f = e does on each outcome of e, with the typing that makes
   the write a one-slot store: f's slot is x's slot plus the offset the
   lowering's struct table gives, and e's value encodes there as its typed
   word. *)
Theorem assign_attr_storage_source:
  !cx cenv env lctx src id fld sid fty fsz e es res es' ts tr id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?fs off ftv.
             evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
             struct_field_slot fs fld = SOME (off, ftv) /\
             off = struct_field_offset_slots
               (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
               fld /\
             evaluate_type (get_tenv cx) fty = SOME ftv /\
             value_has_type ftv v /\
             encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
             write_storage_slot cx tr (n2w slot + n2w off) ftv v
               (es1 with storage_trace :=
                  es1.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) =
               (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_toplevel >> strip_tac >>
  qexistsl_tac [`r`, `es1`] >> simp[] >>
  conj_tac >- (irule expr_body_pre_res_ok >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off, ftv)` >>
  qexistsl_tac [`fs`, `off`, `ftv`] >> simp[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  imp_res_tac struct_field_slot_alookup >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def] >>
  rpt conj_tac >> metis_tac[encode_value_word_typed]
QED

Theorem assign_attr_storage_source_counted[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty, fsz) /\
  is_word_type fty /\ expr_type e = fty /\
  expr_body_pre cenv cx env e es /\
  gas_admissible
    (eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw, ee) /\
  read_result cx raw ee = (INL v, ee) ==>
  ?fs off ftv res ee'.
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    off = struct_field_offset_slots
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    value_has_type ftv v /\
    encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
    write_storage_slot cx tr (n2w slot + n2w off) ftv v
      (ee with storage_trace :=
         ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) = (res, ee') /\
    (!tail.
      (do
        v <- read_result cx raw;
        p <- eval_target_place cx
          (AttributeTarget (TopLevelNameTarget (src,id)) fld);
        write_place cx p v
      od) (ee with gas_obs := tail) = (res, ee' with gas_obs := tail))
Proof
  strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)
    (es with gas_obs := gs)` >>
  rename1 `_ = (res, ee')` >>
  `stmt_res_ok lctx res` by (drule_all gas_admissible_result >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all assign_attr_storage_source >> simp[bind_def] >> strip_tac >>
  drule_all assign_attr_storage_tail >> strip_tac >>
  qexistsl_tac [`fs`, `off`, `ftv`, `res`, `ee'`] >> simp[]
QED

(* ===== The code ===== *)

(* The code of self.x.f = e for a storage or transient struct x and f of
   a word type: e's code, the ADD of f's slot offset to x's slot, e's
   unwrap, then one SSTORE or TSTORE at the field's slot. *)
Theorem assign_attr_storage_code_parts:
  !cenv lctx ty src id fld e sa c sf tr slot sid fty fsz.
    stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ is_word_type (expr_type e) ==>
    c = cenv /\
    ?vv sm dst sn op su.
      compile_expr cenv (expr_type e) e sa = (vv, sm) /\
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sm = (dst, sn) /\
      unwrap_value cenv vv sn = (op, su) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; op] su = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP cenv.ce_module_vars _` >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [compile_stmt_def, exprLoweringTheory.expr_can_mutate_def,
     stmtLoweringTheory.target_to_expr_def, compile_assign_value_def, comp_bind_def,
     comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sm)` >> simp[] >>
  asm_simp_tac (srw_ss())
    [Once compile_get_target_ptr_def, comp_bind_def, comp_return_def,
     LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Lit slot; Lit (n2w off)] sm` >>
  Cases_on `emit_op ADD [Lit slot; Lit (n2w off)] sm` >>
  rename1 `emit_op _ _ _ = (dst, sn)` >> simp[] >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value _ _ _ = (op, su)` >> simp[]
  >- (Cases_on `emit_void TSTORE [dst; op] su` >>
      rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
      simp[comp_bind_def, comp_return_def]) >>
  Cases_on `emit_void SSTORE [dst; op] su` >>
  rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
  simp[comp_bind_def, comp_return_def]
QED

(* An SSTORE or TSTORE at a variable holding a slot, run. *)
Theorem store_var_frag:
  !H ctx func cenv cx es' s1 tr d a op w st st' R.
    emit_void (if tr then TSTORE else SSTORE) [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME w /\
    stmt_state_rel H ctx func cenv cx es'
      (if tr then tstore a w s1 else sstore a w s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel H ctx func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `eval_operand (Var d) s1 = SOME a` by simp[eval_operand_def] >>
  drule_all storage_emit_frame_frag >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[]
QED

(* After e's code: the ADD of f's offset to x's slot, e's unwrap and one
   SSTORE or TSTORE, for any e whose read succeeds; the store's horizons
   are those that declare x's root, which the write's trace records. *)
Theorem assign_attr_storage_word_suffix[local]:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Lit (n2w slot); Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] su = ((),sf) /\
  local_ptrs_reserved cenv sa /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\
  is_word_type (expr_type e) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee raw vv s) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ee.gas_obs = [] /\
  (!v. read_result cx raw ee = (INL v,ee) ==>
     ?fs ftv res ee'.
       struct_field_slot fs fld = SOME (off,ftv) /\
       evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
       value_has_type ftv v /\
       encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
       write_storage_slot cx tr (n2w slot + n2w off) ftv v
         (ee with storage_trace :=
            ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) =
         (res,ee') /\
       !tail. k raw (ee with gas_obs := tail) =
              (res,ee' with gas_obs := tail)) ==>
  ?res ee' r.
    (!tail. k raw (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)) /\
    gas_marked_path F ctx func s 0 r /\
    ?t'. r = OK t' /\
      !H. valid_horizon cx st0 H ee'.storage_trace ==>
          stmt_post H ctx func cx lctx cenv cenv sa sf es s0 res
            (ee' with gas_obs := []) t'
Proof
  strip_tac >>
  `eval_operand (Lit (n2w slot)) s = SOME (n2w slot)` by
    simp[eval_operand_def] >>
  drule_all expr_add_unwrap_marked_read >> strip_tac >>
  rename1 `gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s) []
             (INL v) ee (OK u)` >>
  `read_result cx raw ee = (INL v,ee)` by
    (`ee with gas_obs := [] = ee` by
       simp[evaluation_state_component_equality] >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >>
     simp[gas_explicit_def]) >>
  qpat_x_assum `!v. read_result cx raw ee = _ ==> _` drule >> strip_tac >>
  `type_slot_size ftv = 1` by metis_tac[word_type_slot_size] >>
  `well_formed_type_value ftv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `stmt_state_rel H0 ctx func cenv cx ee u` by metis_tac[] >>
  `~u.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `res = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq]) >>
  pop_assum SUBST_ALL_TAC >>
  `ee'.gas_obs = [] /\ ee'.scopes = ee.scopes /\
   ee'.storage_trace =
     ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  `eval_operand op u = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `gas_marked_path F ctx func u 0
    (OK ((if tr then tstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u
          else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u)
      with vs_inst_idx := SUC u.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[dst;op]`, `if tr then TSTORE else SSTORE`, `[]`,
                   `su`, `sf`] >>
     Cases_on `tr` >> gvs[emit_void_def,emit_inst_def,is_terminator_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     fs[mk_inst_def,exec_write2_def]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `sf.cs_current_bb = su.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH su.cs_current_insts)` by
    (Cases_on `tr` >>
     gvs[emit_void_def,comp_bind_def,fresh_id_def,comp_ignore_bind_def,
         comp_return_def,emit_def]) >>
  `alloca_frame cenv es sa s0 cenv ee u` by metis_tac[] >>
  `alloca_frame cenv es sa s0 cenv ee'
     ((if tr then tstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u
       else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u)
      with vs_inst_idx := SUC u.vs_inst_idx)` by
    (irule alloca_frame_same_state >> qexists_tac `u` >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, LET_THM] >>
     qpat_x_assum `alloca_frame _ _ _ _ _ ee u` mp_tac >>
     simp[alloca_frame_def]) >>
  qexistsl_tac [`INL ()`, `ee'`,
    `OK ((if tr then tstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u
          else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u)
      with vs_inst_idx := SUC u.vs_inst_idx)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      metis_tac[gas_marked_path_then,ADD_CLAUSES]) >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace /\
   MEM (tr, n2w slot, StructTV fs) (FST H) /\ regions_consistent (FST H)` by
    fs[vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       listTheory.EVERY_APPEND,
       vyperStorageFootprintTheory.storage_trace_regions_def] >>
  `stmt_state_rel H ctx func cenv cx ee u /\
   storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
  `!u' st. storage_dead H tr (update_storage (n2w slot + n2w off) u' st) =
           storage_dead H tr st` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
     metis_tac[]) >>
  qspecl_then [`H`, `func`, `cenv`, `cx`,
    `ee with storage_trace :=
       ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]`,
    `u`, `tr`, `n2w slot + n2w off`, `ftv`, `v`,
    `typed_val_to_w256 ftv v`, `INL ()`, `ee'`, `ctx`]
    mp_tac stmt_state_rel_write_storage_word >>
  impl_tac >- simp[] >> strip_tac >>
  `storage_well_formed_on cx ee' (FST H)` by
    (qabbrev_tac `ee1 = ee with storage_trace :=
       ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]` >>
     `storage_well_formed_on cx ee1 (FST H)` by
       fs[Abbr `ee1`, vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     qpat_x_assum `storage_well_formed_on cx ee _` kall_tac >>
     `storage_subregion (StructTV fs) [AttrSubscript fld] off ftv` by
       simp[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
     `w2n (n2w slot : bytes32) + type_slot_size (StructTV fs) <= dimword(:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
     strip_tac >>
     `w2n (n2w slot + n2w off : bytes32) = w2n (n2w slot : bytes32) + off` by
       (`w2n (n2w slot : bytes32) + off < dimword (:256)` by decide_tac >>
        Cases_on `(n2w slot : bytes32)` >>
        fs[wordsTheory.word_add_n2w]) >>
     `slots_in_range (get_storage cx ee1 tr) (w2n (n2w slot : bytes32))
        (StructTV fs)` by
       metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     `0 < type_slot_size ftv` by simp[] >>
     `slots_in_range (get_storage cx ee' tr) (w2n (n2w slot : bytes32))
        (StructTV fs)` by
       (drule_all
          vyperStorageRegionWriteTheory.storage_subregion_typed_write_preserves_root >>
        simp[]) >>
     irule vyperStorageFootprintTheory.contained_write_preserves_storage_well_formed_on >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`ee1`, `n2w slot + n2w off`, `ftv`, `v`] >> simp[] >>
     decide_tac) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  Cases_on `tr` >>
  gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

(* self.x.f = e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of a word type that e has, for every
   outcome: e's errors exit, and on a value its word is stored at the
   field's slot.  e may call internal functions: its simulation is a
   premise. *)
Theorem compile_assign_attr_storage_case:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def,stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >>
  gvs[] >> rename1 `emit_void _ _ su = ((),sf)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sf` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,
              ci_mono_emit_void,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  irule forced_vv_then_stmt_outcome >>
  qexistsl_tac [
    `\H raw ee t. vv_post H ctx func cenv cx e es sa sm s0 ee raw vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts`, `e`,
    `\raw. do v <- read_result cx raw;
       p <- eval_target_place cx
         (AttributeTarget (TopLevelNameTarget (src,id)) fld);
       write_place cx p v od`] >>
  rpt conj_tac
  >~ [`eval_stmt _ _ = _`] >- simp[eval_assign_attr_toplevel_action]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >>
      gen_tac >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_write_place])
  >~ [`gas_outcome _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`st0`,`sa`,`sm`,`vv`,`s0`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[expr_body_pre_vv_gas_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `valid_horizon cx st0 H1 ee.storage_trace` >>
  `storage_trace_frame (eval_expr cx e)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gs).storage_trace`
       suffices_by simp[] >>
     metis_tac[vyperStorageFootprintTheory.valid_horizon_frame]) >>
  `stmt_state_rel H1 ctx func cenv cx es s0` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t` by metis_tac[] >>
  `t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by metis_tac[] >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `eval_expr cx e (es with gas_obs := _) = _`
       (mp_tac o MATCH_MP
          vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
     ?fs ftv res ee'.
       struct_field_slot fs fld = SOME (struct_field_offset_slots
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld,
         ftv) /\
       evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
       value_has_type ftv v /\
       encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
       write_storage_slot cx tr (n2w slot + n2w (struct_field_offset_slots
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))
         ftv v
         (ee with storage_trace :=
            ee.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) =
         (res,ee') /\
       !tail. (do v <- read_result cx tv;
         p <- eval_target_place cx
           (AttributeTarget (TopLevelNameTarget (src,id)) fld);
         write_place cx p v od)
         (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`fty` |-> `expr_type e`]
       assign_attr_storage_source_counted)) >>
     strip_tac >> qexistsl_tac [`fs`, `ftv`, `res`, `ee'`] >> gvs[]) >>
  drule_all (SRULE [] (Q.INST [`k` |-> `\raw. do
    v <- read_result cx raw;
    p <- eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld);
    write_place cx p v od`]
    assign_attr_storage_word_suffix)) >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  metis_tac[]
QED

(* compile_assign_attr_storage_case for an e with no internal call. *)
Theorem compile_assign_attr_storage_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  rpt strip_tac >> irule compile_assign_attr_storage_case >>
  `expr_body_pre cenv cx env e es` by fs[expr_sim_pre_body] >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[expr_vv_ok_def] >>
  simp[] >> metis_tac[]
QED
