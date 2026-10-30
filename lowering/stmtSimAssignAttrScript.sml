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
 *   expr_add_unwrap_frag             — e's code, an ADD of an offset to a
 *                                      base, and e's unwrap, run
 *   compile_assign_attr_local_stmt_frag — x.f = e, every outcome
 *
 * Helpers: struct_field_type, eval_target_place_attr_local,
 *   write_place_attr_local, fields_in_memory_mstore_field,
 *   fields_val_wf_update, assign_attr_local_code_parts,
 *   assign_attr_local_source, mstore_var_frag, assign_attr_local_frag
 *)

Theory stmtSimAssignAttr
Ancestors
  list rich_list finite_map pred_set alist
  fragExec localPtrsProps exprSim exprSimHyps exprSimUnwrap exprSimBuffer
  exprSimAggregateChildren exprSimAttributeFields freshWrites
  stmtSim stmtSimDecl stmtSimDeclMem stmtSimDeclStore stmtSimAssignStore
  stmtSimAssign
  stmtSimAssignMem stmtSimAugAssign
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  exprOperandVar compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  vyperTyping vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeExprResult
  venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

(* A field the lowering's struct table lists has, in the struct's type
   value, the type value its declared type evaluates to. *)
Theorem alookup_zip_field[local]:
  !fields tvs f fld fty fsz.
    OPT_MMAP f (MAP (FST o SND) fields) = SOME tvs /\
    ALOOKUP fields fld = SOME (fty, fsz) ==>
    ?ftv. ALOOKUP (ZIP (MAP FST fields, tvs)) fld = SOME ftv /\
          f fty = SOME ftv
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `if h0 = fld then _ else _` >> Cases_on `h0 = fld` >> gvs[]
QED

Theorem struct_field_type:
  !cenv cx env es sid fs fld fty fsz.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?ftv. ALOOKUP fs fld = SOME ftv /\
          evaluate_type (get_tenv cx) fty = SOME ftv
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[get_struct_fields_def, vyperValueTheory.evaluate_types_OPT_MMAP] >>
  qpat_x_assum `MAP FST fields = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `MAP (FST o SND) fields = _` (SUBST_ALL_TAC o SYM) >>
  drule_all alookup_zip_field >> strip_tac >> simp[] >>
  metis_tac[cj 1 evaluate_type_mono]
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
  !func cenv cx es s id p sz w pre env entry rest fs vals flds fld ftv etv v.
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out etv ftv v ==>
    stmt_state_rel func cenv cx
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

(* vv_post holds of a result only where it reads (exprSimUnwrap's
   vv_post_failed_read, local there). *)
Theorem vv_post_failed_read[local]:
  !func cenv cx e es sa sm s0 es' raw vv s exc.
    read_result cx raw es' = (INR exc, es') ==>
    ~vv_post func cenv cx e es sa sm s0 es' raw vv s
Proof
  rpt strip_tac >> Cases_on `vv` >>
  gvs[vv_post_def, vv_holds_def, storage_holds_def, immutable_holds_def] >>
  rename1 `eval_operand place_ptr.ptr_operand s = SOME word` >>
  Cases_on `place_ptr.ptr_location` >> gvs[]
QED

(* After the ADD and the unwrap: e's value at op, the ADD's sum in dst,
   and the frame from before e. *)
Theorem add_unwrap_post[local]:
  !func cenv cx e es sa sm sn su s0 es1 tv vv r v op dst bw off s.
    emit_op ADD [bop; Lit (n2w off)] sm = (dst, sn) /\
    ci_mono sa sm /\
    vv_post func cenv cx e es sa sn s0 es1 tv vv r /\
    eval_operand dst r = SOME (bw + n2w off) /\
    expr_post func cenv cx e es1 (sa with cs_next_var := sn.cs_next_var)
      su r es1 v op s ==>
    stmt_state_rel func cenv cx es1 s /\
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

(* e's code, an ADD of off to the base operand bop, then e's unwrap: on
   a value, op holds e's value and the ADD's output the base plus off, in
   a state related at the state after e; e's errors exit. *)
Theorem expr_add_unwrap_frag:
  !ctx func cenv cx e es res es1 sa vv sm bop off dst sn op su s0 bw.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD [bop; Lit (n2w off)] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    fn_has_code sa su func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es1) /\
    expr_res_ok res /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\ (!l. bop <> Label l) /\
    eval_operand bop s0 = SOME bw ==>
    frag_exec ctx sa su (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. ?v. res = INL v /\ stmt_state_rel func cenv cx es1 s /\
               expr_val_rel cx (expr_type e) v op s /\
               eval_operand dst s = SOME (bw + n2w off) /\
               (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                      lookup_var x s = SOME u) /\
               (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                        FLOOKUP s.vs_allocas aid = SOME b))
      (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono sa sn` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved cenv sn` by metis_tac[compiler_ci_mono_reserved] >>
  qpat_x_assum `(do _ <- _; _ od) _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (raw, est)` >>
  Cases_on `raw` >> simp[]
  >- suspend "value" >>
  suspend "error"
QED

Resume expr_add_unwrap_frag[error]:
  strip_tac >> gvs[] >> rename1 `eval_expr cx e es = (INR ex, es1)` >>
  `expr_vv_res_ok (INR ex)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INR ex`, `es1`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >>
  fs[ci_mono_def] >>
  conj_tac >- (irule cs_extends_trans >> qexists_tac `sn` >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_exit _ _` mp_tac >> rpt (pop_assum kall_tac) >>
  metis_tac[expr_exit_INR_type]
QED

Resume expr_add_unwrap_frag[value]:
  rename1 `eval_expr cx e es = (INL tv, _)` >> strip_tac >>
  `es1 = est` by metis_tac[read_result_state] >>
  pop_assum SUBST_ALL_TAC >>
  rename1 `eval_expr cx e es = (INL tv, es1)` >>
  `expr_vv_res_ok (INL tv)` by
    (Cases_on `tv` >> gvs[expr_vv_res_ok_def, read_result_def, raise_def,
                         expr_res_ok_def]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INL tv`, `es1`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `res`
  >- suspend "read" >>
  rename1 `read_result _ _ _ = (INR ex, _)` >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >>
  fs[ci_mono_def] >>
  conj_tac >- (irule cs_extends_trans >> qexists_tac `sn` >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any irule frag_exec_weaken) >>
  simp[] >> metis_tac[vv_post_failed_read]
QED

Resume expr_add_unwrap_frag[read]:
  rename1 `read_result _ _ _ = (INL v, _)` >>
  `frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
     (\s. ?tv'. INL tv = INL tv' /\
                vv_post func cenv cx e es sa sm s0 es1 tv' vv s)
     (expr_exit (INL v))` by
    (qpat_x_assum `frag_exec _ _ _ _ _ _`
       (mp_then Any irule frag_exec_weaken) >> simp[]) >>
  irule (Q.INST [`w` |-> `bw:bytes32`, `buf` |-> `bop:operand`]
           aggregate_child_add_then) >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  qpat_assum `frag_exec _ sa sm _ _ _` (irule_at Any) >>
  qexists_tac `bw` >> fs[ci_mono_def] >> rpt conj_tac
  >~ [`frag_exec _ _ _ _ _ _`]
  >- (rpt strip_tac >> gvs[] >>
      `frag_exec ctx sn su (\s. s = r)
         (\s. expr_post func cenv cx e es1
                (sa with cs_next_var := sn.cs_next_var) su r es1 v op s)
         (expr_exit (INL v))` by
        (irule unwrap_value_rebased_sim >> simp[] >>
         qexistsl_tac [`es`, `s0`, `tv`, `vv`] >> simp[]) >>
      qpat_x_assum `frag_exec _ sn su _ _ _`
        (mp_then Any irule frag_exec_weaken) >>
      simp[] >> rpt gen_tac >> strip_tac >>
      `ci_mono sa sm` by fs[ci_mono_def] >>
      drule_all add_unwrap_post >> simp[]) >>
  rpt strip_tac >> Cases_on `bop` >> gvs[eval_operand_def, vv_post_def] >>
  qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` irule >> simp[]
QED

Finalise expr_add_unwrap_frag

(* ===== x.f = e ===== *)

(* What x.f = e does on each outcome of e, with the typing that makes the
   write a field store: x's value is a struct laid out as the lowering's
   struct table says, its field f is of f's declared word type, and e's
   value is of that type. *)
Theorem assign_attr_local_source:
  !cx cenv env lctx id fld sid fty fsz e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    stmt_res_ok lctx res /\ expr_sim_pre cenv cx env e es /\
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
  conj_tac >- (irule expr_sim_pre_res_ok >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >>
  drule_all expr_sim_pre_eval >> strip_tac >>
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

(* An MSTORE at a variable holding an address, run. *)
Theorem mstore_var_frag[local]:
  !ctx func cenv cx es' s1 d op wd a st st' R.
    emit_void MSTORE [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME wd /\
    stmt_state_rel func cenv cx es' (mstore (w2n a) wd s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  irule (SRULE [] (Q.INST [`keep` |-> `\x. T`]
    (SPEC_ALL annassign_mstore_framed_frag))) >>
  simp[] >> metis_tac[]
QED

(* The MSTORE of x.f = e, from the state e's unwrap leaves: the field's
   address is x's base plus f's offset, which does not wrap since x's
   region lies below the allocation frontier. *)
Theorem assign_attr_local_store:
  !ctx func cenv cx es1 t d op su sf p sz w0 off id pre env1 entry rest fs
   vals flds fld ftv v R.
    emit_void MSTORE [Var d; op] su = ((), sf) /\
    lookup_var d t = SOME (w0 + n2w off) /\ lookup_var p t = SOME w0 /\
    eval_operand op t = SOME (typed_val_to_w256 ftv v) /\
    stmt_state_rel func cenv cx es1 t /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
    off = struct_field_offset flds fld ==>
    frag_exec ctx su sf (\s. s = t)
      (\t'. stmt_state_rel func cenv cx
              (es1 with scopes :=
                 pre ++ (env1 |+ (id, entry with
                           <|value := StructV (AFUPDKEY fld (K v) vals);
                             popped := []|>)) :: rest) t' /\
            (!x. lookup_var x t' = lookup_var x t) /\
            (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
                     FLOOKUP t'.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `lookup_scopes id es1.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es1.scopes t /\ alloca_room func t` by
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
  irule mstore_var_frag >>
  qpat_assum `lookup_var d _ = _` (irule_at Any) >>
  qpat_assum `eval_operand op _ = _` (irule_at Any) >>
  simp[] >> gvs[] >>
  irule stmt_state_rel_write_field >> metis_tac[]
QED

(* x.f = e as one fragment: e's errors exit, and on a value it reaches
   its end related at the scopes write_place leaves. *)
Theorem assign_attr_local_frag:
  !ctx func cenv cx id fld sid e es res es' r es1 sa vv sm dst sn op su
   sf p sz entry0 s0.
    compile_expr cenv (expr_type e) e sa = (vv, sm) /\
    emit_op ADD
      [Var p; Lit (n2w (struct_field_offset
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
         fld))] sm = (dst, sn) /\
    unwrap_value cenv vv sn = (op, su) /\
    emit_void MSTORE [dst; op] su = ((), sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_scopes id es.scopes = SOME entry0 /\
    is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
    expr_res_ok r /\
    (!v. r = INL v ==>
         res = INL () /\
         ?pre env1 entry rest fs vals ftv.
           find_containing_scope id es1.scopes =
             SOME (pre, env1, entry, rest) /\
           entry.type = StructTV fs /\ entry.value = StructV vals /\
           fields_layout (get_struct_fields cenv.ce_struct_fields
                            (nsid_to_string sid)) fs /\
           struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
           evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
           store_lays_out ftv ftv v /\
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
      (expr_exit r)
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- simp[frag_exec_def] >>
  `?w0. lookup_var p s0 = SOME w0` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sf` by
    metis_tac[compile_expr_ci_mono, ci_mono_emit_op, ci_mono_unwrap_value,
              ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa su /\ cs_extends su sf` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  `eval_operand (Var p) s0 = SOME w0 /\
   (!x. Var p = Var x ==> not_fresh_at sa x) /\ !l. Var p <> Label l` by
    simp[eval_operand_def] >>
  drule_all expr_add_unwrap_frag >> strip_tac >>
  irule frag_exec_seq_pointwise >>
  qpat_assum `frag_exec _ sa su _ _ _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[eval_operand_def] >>
  `eval_operand op t = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w0` by
    (qpat_x_assum `!x u. not_fresh_at sa x /\ _ ==> lookup_var x t = _`
       irule >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es1`, `t`,
               `STRING #"%" (toString sm.cs_next_var)`, `op`, `su`, `sf`,
               `p`, `sz`, `w0`,
               `struct_field_offset (get_struct_fields cenv.ce_struct_fields
                  (nsid_to_string sid)) fld`,
               `id`, `pre`, `env1`, `entry`, `rest`, `fs`, `vals`,
               `get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)`,
               `fld`, `ftv`, `v`, `expr_exit (INL v)`]
    mp_tac assign_attr_local_store >>
  impl_tac >- simp[] >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> metis_tac[]
QED

(* x.f = e for a local x of struct type sid, f a field of sid of a word
   type, and e of f's type, for every outcome: e's errors exit, and on a
   value its typed word is stored at f's offset in x's region. *)
Theorem compile_assign_attr_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env id fld sid fty fsz e es res es'.
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[expr_vv_ok_def] >>
  drule_all assign_attr_local_source >> strip_tac >>
  qpat_x_assum `expr_type e = fty` (SUBST_ALL_TAC o SYM) >>
  drule_all assign_attr_local_frag >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`t`, `cenv`] >> gvs[] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  Cases_on `r` >> gvs[] >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED
