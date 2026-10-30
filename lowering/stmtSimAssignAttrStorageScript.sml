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
 *   compile_assign_attr_storage_stmt_frag — self.x.f = e, every outcome
 *
 * Helpers: struct_field_slot_alookup, extend_storage_place_attr,
 *   eval_target_place_attr_toplevel, assign_attr_storage_source,
 *   assign_attr_storage_code_parts, store_var_frag, assign_attr_storage_frag
 *)

Theory stmtSimAssignAttrStorage
Ancestors
  list rich_list finite_map pred_set alist
  fragExec exprSim exprSimHyps exprSimLeaves exprSimAttributeFields
  stmtSim stmtSimDecl stmtSimDeclMem stmtSimAssign stmtSimAssignMem
  stmtSimAssignStorage stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
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
    es' = es /\
    ?fs off ftv.
      evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      r = INL (StoragePlace tr (n2w slot + n2w off) ftv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def, extend_place_def, bind_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  rename1 `extend_storage_place cx tr _ tv` >>
  Cases_on `extend_storage_place cx tr (n2w slot) tv (AttrSubscript fld) es` >>
  rename1 `_ = (r1, es1)` >>
  drule extend_storage_place_attr >> strip_tac >>
  Cases_on `r1` >> simp[return_def, get_place_def] >> strip_tac >> gvs[]
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
             write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
               (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `eval_expr cx e es = (INL pv, es1)` >>
  Cases_on `eval_target_place cx
              (AttributeTarget (TopLevelNameTarget (src, id)) fld) es1` >>
  rename1 `_ = (r2, es2)` >>
  drule eval_target_place_attr_toplevel >> rpt (disch_then drule) >>
  strip_tac >>
  Cases_on `r2` >> simp[]
  >- (gvs[] >> Cases_on `read_result cx pv es1` >>
      rename1 `read_result cx pv es1 = (r3, es3)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `r3` >> simp[write_place_def] >> metis_tac[]) >>
  strip_tac >> gvs[]
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
    stmt_res_ok lctx res /\ expr_sim_pre cenv cx env e es /\
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
           ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv /\
                 encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
                 write_storage_slot cx tr
                   (n2w slot + n2w (struct_field_offset_slots
                      (get_struct_fields cenv.ce_struct_fields
                         (nsid_to_string sid)) fld))
                   ftv v es1 = (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_toplevel >> strip_tac >>
  qexistsl_tac [`r`, `es1`] >> simp[] >>
  conj_tac >- (irule expr_sim_pre_res_ok >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off, ftv)` >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  imp_res_tac struct_field_slot_alookup >> gvs[] >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def] >>
  irule encode_value_word_typed >> metis_tac[]
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
    FLOOKUP cenv.ce_vars (module_var_key (src, id)) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (module_var_key (src, id)) = NONE /\
    cenv.ce_var_type (module_var_key (src, id)) = SOME (StructT sid) /\
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
  rename1 `FLOOKUP cenv.ce_vars _` >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [compile_stmt_def, compile_assign_value_def, comp_bind_def,
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
Theorem store_var_frag[local]:
  !ctx func cenv cx es' s1 tr d a op w st st' R.
    emit_void (if tr then TSTORE else SSTORE) [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME w /\
    stmt_state_rel func cenv cx es'
      (if tr then tstore a w s1 else sstore a w s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `frag_exec ctx st st' (\t. t = s1)
     (\t. stmt_state_rel func cenv cx es' t /\
          (!x. lookup_var x t = lookup_var x s1) /\
          (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b)) (\r. F)` by
    (imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts st st')` by
       (Cases_on `tr` >> gvs[venomInstTheory.mk_inst_def, is_terminator_def]) >>
     irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     rpt strip_tac >> gvs[] >>
     `step_inst_base (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
                        [Var d; op] []) s1 =
        OK (if tr then tstore a w s1 else sstore a w s1)` by
       (Cases_on `tr` >>
        simp[step_inst_base_def, exec_write2_def, mk_inst_def,
             eval_operand_def]) >>
     Cases_on `tr` >> gvs[] >>
     simp[run_inst_seq_def, stmt_state_rel_inst_idx] >>
     gvs[lookup_var_def, sstore_def, tstore_def, LET_THM]) >>
  pop_assum (mp_then Any irule frag_exec_weaken) >> simp[]
QED

(* self.x.f = e as one fragment: e's errors exit, and on a value it reaches
   its end related at the state the slot write leaves. *)
Theorem assign_attr_storage_frag:
  !ctx func cenv cx e es res es' r es1 sa vv sm dst sn op su sf tr slot off
   s0.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD [Lit (n2w slot); Lit (n2w off)] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    emit_void (if tr then TSTORE else SSTORE) [dst; op] su = ((), sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
    expr_res_ok r /\
    (!v. r = INL v ==>
         ?ftv. evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
               encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
               write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
                 (res, es')) ==>
    frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\t. res = INL () /\ stmt_state_rel func cenv cx es' t /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x t = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b))
      (expr_exit r)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sf` by
    metis_tac[compile_expr_ci_mono, ci_mono_emit_op, ci_mono_unwrap_value,
              ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa su /\ cs_extends su sf` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  `eval_operand (Lit (n2w slot)) s0 = SOME (n2w slot) /\
   (!x. Lit (n2w slot) = Var x ==> not_fresh_at sa x) /\
   !l. Lit (n2w slot) <> Label l` by
    simp[eval_operand_def] >>
  drule_all expr_add_unwrap_frag >> strip_tac >>
  irule frag_exec_seq_pointwise >>
  qpat_assum `frag_exec _ sa su _ _ _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[eval_operand_def] >>
  `eval_operand op t = SOME (typed_val_to_w256 ftv v)` by
    gvs[expr_val_rel_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  drule_at (Pos hd) store_var_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `t`,
                           `n2w slot + n2w off`, `typed_val_to_w256 ftv v`,
                           `expr_exit (INL v)`] mp_tac) >>
  simp[] >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[]
QED

(* self.x.f = e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of a word type that e has, for every
   outcome: e's errors exit, and on a value its word is stored at the
   field's slot. *)
Theorem compile_assign_attr_storage_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es res es' ts
   tr id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (module_var_key (src, id)) = NONE /\
    cenv.ce_var_type (module_var_key (src, id)) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars (module_var_key (src, id)) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[expr_vv_ok_def] >>
  drule_all assign_attr_storage_source >> strip_tac >>
  qpat_x_assum `expr_type e = fty` (SUBST_ALL_TAC o SYM) >>
  drule_all assign_attr_storage_frag >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`t`, `cenv`] >> gvs[] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
      simp[is_terminator_def]) >>
  Cases_on `r` >> gvs[] >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED
