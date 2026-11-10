(*
 * Statement simulation: Assign to a word field of a local struct (#637)
 *
 * x.f = e for a local x of struct type held in memory at its pointer, f a
 * field of a word type, and e of f's type.  The source evaluates e, takes
 * the place x.f (the field must be in x's value), reads e's value and
 * writes it into x's value at f (write_place on MemoryPlace x [f]).  The
 * lowering evaluates e, adds f's byte offset to x's pointer, unwraps the
 * value and stores it there with one MSTORE.  The ADD sits between e's
 * code and the unwrap, so e is taken through expr_vv_sim and
 * exprSimAggregateChildren's rebased unwrap, as a struct literal's
 * children are.
 *
 * TOP-LEVEL:
 *   eval_assign_attr_local           — the source run: e's forced value,
 *                                      then write_place on x.f
 *   stmt_state_rel_write_field       — an MSTORE at a word field's offset
 *                                      relates the scopes write_place leaves
 *   expr_add_unwrap_marked_read      — counted ADD and unwrap after e
 *   assign_attr_local_store_marked_path — counted field MSTORE
 *   attribute_type_struct_field      — a field the typing gives a struct is
 *                                      in the lowering's struct table
 *   compile_assign_attr_local_case   — x.f = e, every outcome, e's
 *                                      simulation a premise
 *   compile_assign_attr_local_stmt_frag — the same for an e with no
 *                                      internal call
 *
 * Helpers: eval_target_place_attr_local,
 *   write_place_attr_local, fields_in_memory_mstore_field,
 *   fields_val_wf_update, assign_attr_local_code_parts,
 *   assign_attr_local_source, assign_attr_local_rhs_outcome
 *)

Theory stmtSimAssignAttr
Ancestors
  exprSimFieldLayout exprSimProps
  exprSimSource exprSimMemorySource exprSimVVFrame
  stmtSimDeclPath stmtSimDeclCompose fragGasSeq fragGasMode gasSummary
  gasSummaryCompose fragGasPath gasContext gasExemptCert gasOutcome
  stmtSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec localPtrsProps  exprSimHyps exprSimUnwrap exprSimBuffer
  exprSimAggregateChildren exprSimAttributeFields freshWrites
   stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssignStore
  stmtSimAssign
  stmtSimAssignMem stmtSimAugAssign
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  exprOperandVar compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  vyperTyping vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeExprResult
  venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

Theorem alookup_fields_args[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty, fsz)
Proof
  Induct >> rpt gen_tac >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> Cases_on `h'` >> rw[] >> gvs[] >> metis_tac[]
QED

(* A field the typing gives a struct is in the lowering's struct table,
   at the type the typing gives it. *)
Theorem attribute_type_struct_field:
  !cenv cx env es sid fld fty.
    expr_sim_inv cenv cx env es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
    ?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                     (nsid_to_string sid)) fld = SOME (fty, fsz)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.attribute_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[get_struct_fields_def] >> metis_tac[alookup_fields_args]
QED

(* The place x.f for a local x in scope whose value has field f, and only
   then: any other case is a type error. *)
Theorem eval_target_place_attr_local:
  !cx id fld es r es'.
    eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
      (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\ r = INL (MemoryPlace id [AttrSubscript fld]) /\
    ?entry vals old.
      lookup_scopes id es.scopes = SOME entry /\
      entry.value = StructV vals /\ ALOOKUP vals fld = SOME old
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def] >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[raise_def, return_def, get_place_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def, raise_def,
       read_memory_path_def, evaluate_subscripts_def, subscripts_type_def,
       lift_sum_def, extend_memory_place_def, get_place_def] >>
  Cases_on `evaluate_subscripts entry.type entry.value [AttrSubscript fld]` >>
  simp[raise_def, ignore_bind_def, bind_def, return_def, get_place_def] >>
  strip_tac >> gvs[] >>
  Cases_on `entry.value` >> gvs[evaluate_subscripts_def, AllCaseEqs()]
QED

(* Writing v at x.f, where x's value has field f: unless it fails with a
   type error (x not assignable), x's value gets v at f. *)
Theorem write_place_attr_local:
  !cx id fld v es res es' entry vals old.
    write_place cx (MemoryPlace id [AttrSubscript fld]) v es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?pre env rest.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      res = INL () /\
      es' = es with scopes :=
              pre ++ (env |+ (id, entry with
                        <|value := StructV (AFUPDKEY fld (K v) vals);
                          popped := []|>)) :: rest
Proof
  rpt gen_tac >>
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id es.scopes` >>
  simp[raise_def, return_def] >>
  rename1 `find_containing_scope _ _ = SOME q` >> PairCases_on `q` >>
  strip_tac >>
  `q2 = entry` by (imp_res_tac find_containing_scope_lookup >> gvs[]) >>
  gvs[] >> Cases_on `entry.assignable` >>
  gvs[assert_def, raise_def, return_def, replace_memory_entry_def,
      evaluate_subscripts_def, assign_subscripts_def, LET_THM, lift_sum_def,
      set_scopes_def, bind_def, ignore_bind_def]
QED

(* x.f = e, unless it fails with a type error: e's forced value r, and
   on an error that error, on a value v the write of v at x.f, where x's
   value has field f. *)
Theorem eval_assign_attr_local:
  !cx id fld e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?entry vals old.
             lookup_scopes id es1.scopes = SOME entry /\
             entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
             write_place cx (MemoryPlace id [AttrSubscript fld]) v es1 =
               (res, es'))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `eval_expr cx e es = (INL pv, es1)` >>
  Cases_on `eval_target_place cx (AttributeTarget (NameTarget id) fld) es1` >>
  rename1 `_ = (r2, es2)` >>
  drule eval_target_place_attr_local >> strip_tac >>
  Cases_on `r2` >> simp[]
  >- (gvs[] >> Cases_on `read_result cx pv es1` >>
      rename1 `read_result cx pv es1 = (r3, es3)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `r3` >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem assign_attr_local_admissible_run:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  !gs. eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      (es with gas_obs := gs) =
    vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld]))
      (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >>
  rename1 `_ = (res, ee)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >>
  strip_tac >> Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY]
QED

Theorem assign_attr_local_admissible_rhs:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control]
     >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`, `gs`] >>
     drule assign_attr_local_admissible_run >>
     disch_then (qspec_then `gs` SUBST1_TAC) >>
     simp[Once vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assign_attr_local_admissible_raw:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  metis_tac[assign_attr_local_admissible_rhs]
QED

Theorem assign_attr_local_continuation_success:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v, ee) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v ee =
      (INL (), ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >> rename1 `_ = (res, ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY] >>
  `!m. res <> INR (Error (TypeError m))` by gvs[stmt_res_ok_def] >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem assign_attr_local_continuation_all_tails:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `!tail. ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)` by
    (gen_tac >> drule assign_attr_local_continuation_success >>
     disch_then (qspecl_then [`v`, `prefix ++ tail`, `ee with gas_obs := tail`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  pop_assum (fn th => assume_tac th >> mp_tac (Q.SPEC `[]` th)) >>
  strip_tac >> qexistsl [`pre`, `env`, `entry`, `rest`, `vals`, `old`] >>
  gvs[] >> gen_tac >>
  first_x_assum (qspec_then `tail` strip_assume_tac) >> gvs[]
QED

Theorem assign_attr_local_exempt:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_expr cx e) (return ()))
    (es, s0) marks (err, ee) (leaf, fin) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (return ()))
    (es, s0) marks (err, ee) (leaf, fin)
Proof
  strip_tac >>
  `ignore_bind
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (return ()) =
   vyperState$bind (eval_expr cx e)
     (\pv. ignore_bind
       (vyperState$bind (eval_target_place cx (AttributeTarget (NameTarget id) fld))
         (\p. vyperState$bind (read_result cx pv) (write_place cx p)))
       (return ()))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_result >> simp[]
QED

(* ===== The struct in memory after a field store ===== *)

Theorem fields_in_memory_mstore_field:
  !vals fs flds off s fld v wd ftv.
    fields_layout flds fs /\ struct_has_type fs vals /\
    fields_val_wf vals fs /\ fields_in_memory vals fs off s.vs_memory /\
    ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\
    val_in_memory ftv v (off + struct_field_offset flds fld)
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory ==>
    fields_in_memory (AFUPDKEY fld (K v) vals) fs off
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory
Proof
  Induct
  >- (Cases_on `fs` >> simp[value_has_type_def]) >>
  PairCases >> rpt gen_tac >>
  Cases_on `fs` >- simp[value_has_type_def] >>
  rename1 `hf::fs'` >> PairCases_on `hf` >>
  Cases_on `flds` >- simp[fields_layout_def] >>
  rename1 `hl::flds'` >> PairCases_on `hl` >>
  simp[fields_layout_def, value_has_type_def, AFUPDKEY_def,
       struct_field_offset_def] >>
  strip_tac >> gvs[] >>
  Cases_on `h0 = fld` >> gvs[val_in_memory_def, val_wf_def]
  >- (`mstore off wd s = mstore off wd (s with vs_memory := s.vs_memory)` by
        simp[mstore_def] >>
      pop_assum SUBST1_TAC >>
      irule (cj 2 mstore_preserves_val_in_memory) >> simp[]) >>
  conj_tac
  >- (irule mstore_keeps_val_in_memory >> simp[]) >>
  REWRITE_TAC [arithmeticTheory.ADD_ASSOC] >>
  first_x_assum irule >> REWRITE_TAC [GSYM arithmeticTheory.ADD_ASSOC] >>
  gvs[fields_layout_def]
QED

Theorem fields_val_wf_update:
  !vals fs fld v ftv.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP fs fld = SOME ftv /\ val_wf ftv v ==>
    fields_val_wf (AFUPDKEY fld (K v) vals) fs
Proof
  Induct
  >- (Cases_on `fs` >> simp[value_has_type_def]) >>
  PairCases >> rpt gen_tac >>
  Cases_on `fs` >- simp[value_has_type_def] >>
  rename1 `hf::fs'` >> PairCases_on `hf` >>
  simp[value_has_type_def, AFUPDKEY_def] >> strip_tac >> gvs[] >>
  Cases_on `h0 = fld` >> gvs[val_wf_def] >>
  first_x_assum irule >> metis_tac[]
QED

(* An MSTORE of the word that lays v out at field fld's offset in a
   local's region relates the scopes in which the local's value has v at
   fld. *)
Theorem stmt_state_rel_write_field:
  !func cenv cx es s id p sz w pre env entry rest fs vals flds fld ftv etv v ctx.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out etv ftv v ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with
                   <|value := StructV (AFUPDKEY fld (K v) vals);
                     popped := []|>)) :: rest)
      (mstore (w2n w + struct_field_offset flds fld)
         (typed_val_to_w256 etv v) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = w2n w + struct_field_offset flds fld` >>
  qabbrev_tac `t = mstore a (typed_val_to_w256 etv v) s` >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `val_wf entry.type entry.value /\
   val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `fields_val_wf vals fs /\ fields_in_memory vals fs (w2n w) s.vs_memory` by
    gvs[val_wf_def, val_in_memory_struct] >>
  `val_wf ftv v /\ type_memory_size ftv = 32 /\
   val_in_memory ftv v a t.vs_memory` by
    gvs[store_lays_out_def, Abbr `t`] >>
  `struct_field_offset flds fld + 32 <= type_memory_size_fields fs` by
    metis_tac[struct_field_offset_le] >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    simp[Abbr `t`, mstore_def, LET_THM, venom_state_component_equality] >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    simp[Abbr `t`, mstore_def, LET_THM, lookup_var_def] >>
  `!b n. b + n <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
         mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     irule mstore_mem_bytes_at_disjoint >>
     gvs[Abbr `a`, type_memory_size_def]) >>
  `val_wf entry.type (StructV (AFUPDKEY fld (K v) vals))` by
    (gvs[val_wf_def] >> irule fields_val_wf_update >> metis_tac[]) >>
  `val_in_memory entry.type (StructV (AFUPDKEY fld (K v) vals)) (w2n w)
     t.vs_memory` by
    (gvs[val_in_memory_struct, Abbr `t`, Abbr `a`] >>
     irule fields_in_memory_mstore_field >> simp[] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (simp[Abbr `t`, Abbr `a`] >> irule local_mstore_immutables_at >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`id`, `sz`] >> gvs[type_memory_size_def]) >>
  drule_all stmt_state_rel_write_local >> simp[Abbr `t`, Abbr `a`]
QED

(* ===== The code ===== *)

(* The code of x.f = e for a local x of struct type and f of a word type:
   e's code, the ADD of f's byte offset to x's pointer, e's unwrap, then
   one MSTORE at the field. *)
Theorem assign_attr_local_code_parts:
  !cenv lctx ty id fld e sa c sf p sz sid fty fsz.
    stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ is_word_type (expr_type e) ==>
    c = cenv /\
    ?vv sm dst sn op su.
      compile_expr cenv (expr_type e) e sa = (vv, sm) /\
      emit_op ADD
        [Var p; Lit (n2w (struct_field_offset
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sm = (dst, sn) /\
      unwrap_value cenv vv sn = (op, su) /\
      emit_void MSTORE [dst; op] su = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP cenv.ce_vars id` >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [compile_stmt_def, compile_get_target_ptr_def, compile_assign_value_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sm)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Var p; Lit (n2w off)] sm` >>
  Cases_on `emit_op ADD [Var p; Lit (n2w off)] sm` >>
  rename1 `emit_op _ _ _ = (dst, sn)` >> simp[] >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value _ _ _ = (op, su)` >> simp[] >>
  Cases_on `emit_void MSTORE [dst; op] su` >>
  rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >> simp[]
QED

(* ===== e, an ADD, and e's unwrap ===== *)

(* After the ADD and the unwrap: e's value at op, the ADD's sum in dst,
   and the frame from before e. *)
Theorem buffer_emit_add_vv_marked_path:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  eval_operand bop s = SOME bw /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    vv_post ctx func cenv cx e es sa sn s0 ee tv vv q /\
    eval_operand dst q = SOME (bw + n2w off) /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >> drule_all buffer_emit_add_vv_post >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base
    (mk_inst sm.cs_next_id ADD [bop; Lit (n2w off)]
      [STRING #"%" (toString sm.cs_next_var)]) s = OK q` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `emit_inst ADD [bop; Lit (n2w off)]
      [STRING #"%" (toString sm.cs_next_var)] sm =
      ((),sn with cs_next_var := sm.cs_next_var)` by
    gvs[emit_op_def, fresh_var_def, emit_inst_def, emit_def, fresh_id_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def,
        compile_state_component_equality] >>
  `fn_has_code sm (sn with cs_next_var := sm.cs_next_var) func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) emit_inst_zero_marked_path >>
  disch_then (qspecl_then [`q`, `s`, `func`, `ctx`] mp_tac) >>
  impl_tac >- simp[is_terminator_def] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[] >>
  `q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(q with vs_vars := _) = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb)`) >> simp[]) >>
  gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, comp_return_def, compile_state_component_equality]
QED

Theorem add_unwrap_post[local]:
  !func cenv cx e es sa sm sn su s0 es1 tv vv r v op dst bw off s.
    emit_op ADD [bop; Lit (n2w off)] sm = (dst, sn) /\
    ci_mono sa sm /\
    post_value_type cenv e = expr_type e /\
    vv_post ctx func cenv cx e es sa sn s0 es1 tv vv r /\
    eval_operand dst r = SOME (bw + n2w off) /\
    expr_post ctx func cenv cx e es1 (sa with cs_next_var := sn.cs_next_var)
      su r es1 v op s ==>
    stmt_state_rel ctx func cenv cx es1 s /\
    expr_val_rel cx (expr_type e) v op s /\
    eval_operand dst s = SOME (bw + n2w off) /\
    (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
           lookup_var x s = SOME u) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `not_fresh_at sn (STRING #"%" (toString sm.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  `!x. not_fresh_at sa x ==>
       not_fresh_at (sa with cs_next_var := sm.cs_next_var + 1) x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  fs[expr_post_def, vv_post_def] >>
  `eval_operand dst s = SOME (bw + n2w off)` by
    (gvs[eval_operand_def] >>
     qpat_x_assum `!x w. not_fresh_at (sa with cs_next_var := _) x /\ _ ==> _`
       irule >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
         lookup_var x s = SOME u` by
    (rpt strip_tac >>
     qpat_x_assum `!x w. not_fresh_at (sa with cs_next_var := _) x /\ _ ==> _`
       irule >>
     metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem expr_add_unwrap_marked_read:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  fn_inst_ids_distinct func /\ is_word_type (expr_type e) /\
  local_ptrs_reserved cenv sa /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  eval_operand bop s = SOME bw /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
      [] (INL v) ee (OK u) /\
    stmt_state_rel ctx func cenv cx ee u /\
    expr_val_rel cx (expr_type e) v op u /\
    eval_operand dst u = SOME (bw + n2w off) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  drule_all buffer_emit_add_vv_marked_path >> strip_tac >>
  `vv_post ctx func cenv cx e ee (sa with cs_next_var := sn.cs_next_var)
     sn q ee tv vv q` by metis_tac[vv_post_rebase] >>
  `local_ptrs_reserved cenv sn` by
    metis_tac[compiler_ci_mono_reserved, ci_mono_def, cs_extends_trans] >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sn.cs_next_var)` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sn` >> simp[]) >>
  `sa.cs_next_id <= sn.cs_next_id` by fs[ci_mono_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var,
              freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_word] >>
  drule_all add_unwrap_post >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  `0 + 0 = 0` by simp[] >>
  metis_tac[gas_marked_path_then]
QED


(* ===== x.f = e ===== *)

(* What x.f = e does on each outcome of e, with the typing that makes the
   write a field store: x's value is a struct laid out as the lowering's
   struct table says, its field f is of f's declared word type, and e's
   value is of that type. *)
Theorem assign_attr_local_source:
  !cx cenv env lctx id fld sid fty fsz e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           res = INL () /\
           ?pre env1 entry rest fs vals ftv.
             find_containing_scope id es1.scopes =
               SOME (pre, env1, entry, rest) /\
             entry.type = StructTV fs /\ entry.value = StructV vals /\
             fields_layout (get_struct_fields cenv.ce_struct_fields
                              (nsid_to_string sid)) fs /\
             struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
             evaluate_type (get_tenv cx) fty = SOME ftv /\
             store_lays_out ftv ftv v /\
             es' = es1 with scopes :=
               pre ++ (env1 |+ (id, entry with
                         <|value := StructV (AFUPDKEY fld (K v) vals);
                           popped := []|>)) :: rest)
Proof
  rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_local >> strip_tac >>
  qexistsl_tac [`r`, `es1`] >> simp[] >>
  conj_tac >- (irule expr_body_pre_res_ok >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  drule_all struct_fields_layout >> strip_tac >>
  rename1 `entry.type = StructTV fs` >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[value_has_type_def, expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def] >>
  irule store_lays_out_typed >> simp[] >>
  qexistsl_tac [`expr_type e`, `get_tenv cx`] >> simp[]
QED

(* The MSTORE of x.f = e, from the state e's unwrap leaves: the field's
   address is x's base plus f's offset, which does not wrap since x's
   region lies below the allocation frontier. *)
Theorem assign_attr_local_store_marked_path:
  !ctx func cenv cx es1 t d op su sf p sz w0 off id pre env1 entry rest fs
   vals flds fld ftv v.
    emit_void MSTORE [Var d; op] su = ((), sf) /\
    lookup_var d t = SOME (w0 + n2w off) /\ lookup_var p t = SOME w0 /\
    eval_operand op t = SOME (typed_val_to_w256 ftv v) /\
    stmt_state_rel ctx func cenv cx es1 t /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
    off = struct_field_offset flds fld /\
    fn_has_code su sf func /\ ~t.vs_halted /\
    t.vs_current_bb = su.cs_current_bb /\
    t.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?t'. gas_marked_path F ctx func t 0 (OK t') /\
      stmt_state_rel ctx func cenv cx
        (es1 with scopes :=
          pre ++ (env1 |+ (id, entry with
            <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t' /\
      (!x. lookup_var x t' = lookup_var x t) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP t'.vs_allocas aid = SOME b) /\
      ~t'.vs_halted /\ t'.vs_current_bb = sf.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sf.cs_current_insts
Proof
  rpt strip_tac >>
  `lookup_scopes id es1.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es1.scopes t /\ alloca_room ctx func t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n w0 + sz <= t.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `type_memory_size ftv = 32` by fs[store_lays_out_def] >>
  `off + 32 <= type_memory_size_fields fs` by
    metis_tac[struct_field_offset_le] >>
  `w2n (w0 + n2w off) = w2n w0 + off` by
    (irule buffer_offset_no_wrap >>
     qexists_tac `type_memory_size_fields fs` >>
     gvs[type_memory_size_def]) >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  qexists_tac `mstore (w2n (w0 + n2w off)) (typed_val_to_w256 ftv v) t
    with vs_inst_idx := SUC t.vs_inst_idx` >> simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule stmt_state_rel_write_field >> metis_tac[]) >>
  gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, comp_return_def, compile_state_component_equality,
      mstore_def, lookup_var_def] >>
  qpat_x_assum `_ ++ [_] = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Theorem assign_attr_local_marked_exec[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0) marks res ee r
Proof
  strip_tac >> drule assign_attr_local_admissible_run >>
  strip_tac >> gvs[gas_marked_exec_def]
QED

Theorem assign_attr_local_initial_pointer[local]:
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa ==>
  not_fresh_at sa p /\ ?bw. lookup_var p s0 = SOME bw
Proof
  strip_tac >> conj_tac
  >- metis_tac[local_ptrs_reserved_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]
QED

Theorem assign_attr_local_normal_source[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env1 entry rest fs vals ftv.
    find_containing_scope id ee.scopes = SOME (pre,env1,entry,rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\ store_lays_out ftv ftv v /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), ee with <|scopes := pre ++
        (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
          popped := []|>)) :: rest; gas_obs := tail|>)
Proof
  strip_tac >> drule_all assign_attr_local_continuation_all_tails >> strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs ++ [])` >> rename1 `_ = (res,ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs ++ [])` by simp[] >>
  drule_all assign_attr_local_source >> strip_tac >>
  qpat_x_assum `!tail. vyperState$bind _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `r = INL v /\ es1 = (ee with gas_obs := [])` by
    (qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
     qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, pairTheory.UNCURRY]) >>
  gvs[] >> metis_tac[]
QED

Theorem assign_attr_local_store_post[local]:
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  emit_void MSTORE [dst;op] su = ((),sf) /\
  eval_operand dst t = SOME (w0 + n2w off) /\ lookup_var p t = SOME w0 /\
  expr_val_rel cx fty v op t /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
  is_word_type fty /\ stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t /\
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
  strip_tac >>
  `eval_operand op t = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var)) t = SOME (w0 + n2w off)` by
    gvs[eval_operand_def] >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >>
     metis_tac[]) >>
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

Theorem assign_attr_local_normal_continuation[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
    sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  emit_void MSTORE [dst;op] su = ((),sf) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sf /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_marked_exec F (ctx,func) (eval_expr cx e)
    (es,s0) marks (INL tv) ee (OK s) /\
  vv_post ctx func cenv cx e es sa sm s0 (ee with gas_obs := []) tv vv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s0 ==>
  ?ff u. gas_marked_exec F (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0) marks (INL ()) ff (OK u) /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff u
Proof
  strip_tac >> drule_all assign_attr_local_initial_pointer >> strip_tac >>
  `eval_operand (Var p) s = SOME bw` by
    (fs[vv_post_def, eval_operand_def] >> metis_tac[]) >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all expr_add_unwrap_marked_read >> strip_tac >>
  `lookup_var p u = SOME bw` by metis_tac[] >>
  `gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK u)` by
    (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
      |> REWRITE_RULE [APPEND_NIL]) >>
     qexistsl_tac [`ee`, `s`, `tv`] >> simp[] >> fs[gas_marked_exec_def]) >>
  `!tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  drule_all assign_attr_local_normal_source >> strip_tac >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `?ff t'. gas_marked_exec F (ctx,func)
      (write_place cx (MemoryPlace id [AttrSubscript fld]) v)
      (ee with gas_obs := [],u) [] (INL ()) ff (OK t') /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff t'` by
    (irule assign_attr_local_store_post >>
     rpt (goal_assum (drule_at Any)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ff`, `t'`] >> simp[] >>
  irule assign_attr_local_marked_exec >>
  (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
    |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`ee`, `u`, `v`] >> simp[]
QED

Theorem assign_attr_local_rhs_outcome:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
    sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  emit_void MSTORE [dst;op] su = ((),sf) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sf /\ stmt_state_rel ctx func cenv cx es s0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sm s0 ee tv vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0) (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `?ff u. gas_marked_exec F (ctx,func)
            (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
            (es,s0) marks (INL ()) ff (OK u) /\
            stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff u` by
            (irule assign_attr_local_normal_continuation >> simp[] >>
             goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
             goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
             rpt (goal_assum (drule_at Any)) >> simp[]) >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[stmt_post_end_gas_obs]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_attr_local_marked_exec >>
          (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
          ntac 2 (irule gas_marked_exec_bind_exception) >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_attr_local_exempt >> simp[]
QED

(* x.f = e for a local x of struct type sid, f a field of sid of a word
   type, and e of f's type, for every outcome: e's errors exit, and on a
   value its typed word is stored at f's offset in x's region.  e may call
   internal functions: its simulation is a premise. *)
Theorem compile_assign_attr_local_case:
  !ctx func cx lctx RetQ cenv ty env id fld sid fty fsz e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\
   cs_extends su sb` by
    (metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
       ci_mono_unwrap_value, ci_mono_emit_void, pairTheory.SND, ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule assign_attr_local_admissible_raw >> simp[]) >>
  irule assign_attr_local_rhs_outcome >> simp[] >>
  goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then irule >> simp[]
QED

(* compile_assign_attr_local_case for an e with no internal call. *)
Theorem compile_assign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env id fld sid fty fsz e es.
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es
Proof
  rpt strip_tac >> irule compile_assign_attr_local_case >>
  `expr_body_pre cenv cx env e es` by fs[expr_sim_pre_body] >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[expr_vv_ok_def] >>
  simp[] >> metis_tac[]
QED
