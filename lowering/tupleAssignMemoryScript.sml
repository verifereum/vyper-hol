(*
 * Tuple unpacking into locals with memory-backed elements: the code's
 * stages and the run of a successful assignment (#637).
 *
 * TOP-LEVEL:
 *   assign_tuple_locals_memory_code_parts — the code split at its stages
 *   assign_tuple_locals_memory_success_run — a successful assignment's run
 *)
Theory tupleAssignMemory
Ancestors
  tupleTypedLoad tupleStageProps stmtSimAssignTuple tupleLocalStoreProps
  tupleLocalStoreRun stmtSimReturn stmtSimDeclMem valueCopyBytes
  stmtSim exprSim exprOperandVar exprLoweringProps stmtLowering compileEnv
  exprLowering emitHelperProps fragExec loweringSlice freshWrites
  list rich_list finite_map valueEncoding vyperTyping vyperValue
  vyperInterpreter vyperState venomState venomInst
Libs
  monadsyntax

(* The code of x1, ..., xn = e with memory-backed elements, split at its
   stages, with the growth facts of each. *)
Theorem assign_tuple_locals_memory_code_parts:
  !cenv lctx ty ids e tys sa sf c func.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
      ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
        cenv.ce_var_type (EL i ids) = SOME vt /\
        (is_word_type vt = is_word_type (EL i tys)) /\
        (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sc op su staged sl elems ss.
      compile_expr cenv (TupleT tys) e sa = (vv, sc) /\
      unwrap_value cenv vv sc = (op, su) /\
      (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
          EXISTS (\t. ~is_word_type t) tys /\
          0 < SUM (MAP (type_memory_bytes cenv) tys) then
         do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
            ptr <- comp_return buf.buf_operand;
            emit_void MCOPY [ptr; op;
              Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
            comp_return ptr od
       else comp_return op) su = (staged, sl) /\
      compile_tuple_load_all cenv staged tys 0 sl = (elems, ss) /\
      compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
        elems ss = ((), sf) /\
      cs_extends sa sc /\ cs_extends sc su /\ cs_extends su sl /\
      cs_extends sl ss /\ cs_extends ss sf /\
      fn_has_code sa sc func /\ fn_has_code sc su func /\
      fn_has_code su sl func /\ fn_has_code sl ss func /\
      fn_has_code ss sf func /\
      sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
      sl.cs_next_var <= ss.cs_next_var /\ ss.cs_next_var <= sf.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_locals_code_decompose >> strip_tac >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  drule exprSimUnwrapTheory.unwrap_value_extends >> strip_tac >>
  drule tuple_stage_grows >> strip_tac >>
  drule compile_tuple_load_all_grows >> strip_tac >>
  drule_all tupleLocalStorePropsTheory.tuple_store_locals_grows >> strip_tac >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op, su)` by
    simp[lower_value_def, comp_bind_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends sl sf` by metis_tac[cs_extends_trans] >>
  `cs_extends su sf` by metis_tac[cs_extends_trans] >>
  `cs_extends sc sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc func /\ fn_has_code sc sf func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sc su func /\ fn_has_code su sf func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code su sl func /\ fn_has_code sl sf func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sl ss func /\ fn_has_code ss sf func` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

Theorem assign_tuple_locals_memory_success_run:
  !ctx func cx lctx cenv ty ids e es es' tys tvs sa sf s0.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (INL (), es') /\
    ids <> [] /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==>
      cenv.ce_target CapMcopy /\ type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH ids ==> ?p sz vt.
      FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type (EL i ids) = SOME vt /\
      if is_word_type (EL i tys) then is_word_type vt else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
          type_memory_bytes cenv vt = type_memory_size vtv /\
          0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i entry.
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH ids /\
      lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
      if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa = (cenv,sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule eval_assign_tuple >> strip_tac >> Cases_on `r` >> gvs[] >>
  rename1 `assign_tuple_targets _ _ v es1 = (INL (),es')` >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "source"
QED

Resume assign_tuple_locals_memory_success_run[source]:
  drule assign_tuple_target_list_length >> strip_tac >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  `LENGTH ids = LENGTH vs /\ LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length, LENGTH_MAP] >>
  `!i. i < LENGTH ids /\ i < LENGTH tys ==> ?p sz vt.
     FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
     cenv.ce_var_type (EL i ids) = SOME vt /\
     (is_word_type vt = is_word_type (EL i tys)) /\
     (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> qexistsl_tac [`p`, `sz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> gvs[] >>
     metis_tac[is_bytestring_word_type]) >>
  `(EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy)` by
    metis_tac[] >>
  drule_all assign_tuple_locals_memory_code_parts >> strip_tac >>
  suspend "code"
QED

Resume assign_tuple_locals_memory_success_run[code]:
  qpat_x_assum `eval_stmt _ _ _ = _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `LENGTH (MAP _ _) = _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH ids /\ i < LENGTH tys ==> _` kall_tac >>
  qpat_x_assum `cenv = cenv` kall_tac >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends su sf` by metis_tac[cs_extends_trans] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (qspecl_then [`sa`, `su`, `sf`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `expr_res_ok (INL (ArrayV (TupleV vs)))` by simp[expr_res_ok_def] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule_all >> disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ _ sv` >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `expr_type e = TupleT tys`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  suspend "value"
QED

Resume assign_tuple_locals_memory_success_run[value]:
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`fn_has_code sa sf func`, `fn_has_code sa sc func`,
     `fn_has_code sc su func`, `fn_has_code sa su func`,
     `compile_expr _ _ _ _ = _`, `unwrap_value _ _ _ = _`,
     `lower_value _ _ _ _ _ = _`, `expr_res_ok _`,
     `!aid off sz. _`,
     `stmt_state_rel func cenv cx es s0`, `~s0.vs_halted`,
     `s0.vs_current_bb = _`, `s0.vs_inst_idx = _`,
     `cs_extends sa sc`, `cs_extends sc su`, `cs_extends sa su`,
     `cs_extends su sf`] >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (irule tuple_element_sizes >> reverse conj_tac
     >- (qexists `get_tenv cx` >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl [`get_tenv cx`, `tys`] >>
     simp[SF CONJ_ss] >>
     rpt gen_tac >> strip_tac >>
     Cases_on `is_word_type (EL i tys)` >- simp[] >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> metis_tac[]) >>
  suspend "stage"
QED

Resume assign_tuple_locals_memory_success_run[stage]:
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  drule_all optional_tuple_stage_run >>
  disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  suspend "load"
QED

Resume assign_tuple_locals_memory_success_run[load]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`(if flag then _ else _) su = _`, `Abbrev (flag = _)`,
     `flag ==> _`, `expr_val_rel _ _ _ _ _`, `expr_val_at _ _ _ _ _ _ _ _ _`,
     `expr_type e = _`, `eval_operand op sv = _`,
     `!x. op = Var x ==> _`, `fn_has_code su sl func`,
     `~sv.vs_halted`, `sv.vs_current_bb = _`, `sv.vs_inst_idx = _`,
     `stmt_state_rel func cenv cx es1 sv`] >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  drule_all compile_tuple_load_all_typed_frag >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "store"
QED

Resume assign_tuple_locals_memory_success_run[store]:
  `LENGTH ids = LENGTH tys /\ LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH ids ==> ?v. eval_operand (EL i elems) t = SOME v /\
     if is_word_type (EL i tys) then
       v = typed_val_to_w256 (EL i tvs) (EL i vs)
     else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH ids ==> ?p dsz vt.
     FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) dsz) /\
     cenv.ce_var_type (EL i ids) = SOME vt /\
     (is_word_type vt = is_word_type (EL i tys)) /\
     (~is_word_type (EL i tys) ==>
       (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
       type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
       ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
         type_memory_bytes cenv vt = type_memory_size vtv /\
         0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> ?p sz vt. _` (qspec_then `i` mp_tac) >>
     simp[] >> disch_then (qx_choosel_then [`p`, `dsz`, `vt`]
       (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qexistsl [`p`, `dsz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> asm_rewrite_tac[] >>
     metis_tac[is_bytestring_word_type]) >>
  suspend "store_ready"
QED

Resume assign_tuple_locals_memory_success_run[store_ready]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`!i. i < LENGTH ids ==> ?p sz vt. _ /\ _ /\ if _ then _ else _`,
     `value_has_type _ _`, `evaluate_type _ (TupleT tys) = _`,
     `(EXISTS _ tys ==> _ /\ _)`, `(EXISTS _ tys ==> _)`,
     `bind (eval_expr _ _) _ _ = _`, `compile_tuple_load_all _ _ _ _ _ = _`,
     `local_ptrs_reserved cenv sa`, `local_ptrs_reserved cenv su`,
     `eval_operand staged st = _`,
     `tuple_in_memory vs tvs (w2n w) st.vs_memory`,
     `0 < type_memory_size_list tvs`, `tys <> []`,
     `type_memory_bytes cenv (TupleT tys) = _`] >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH tys ==>
     evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
     (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (rpt gen_tac >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
       (qpat_assum `LIST_REL (\t tv. evaluate_type _ t = SOME tv) _ _`
          (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        disch_then (qspec_then `i` mp_tac o CONJUNCT2) >> simp[]) >>
     simp[] >> strip_tac >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  Q.SUBGOAL_THEN
    `((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
      (?name. local_region cenv es1.scopes t name b sz))` assume_tac
  >- metis_tac[] >>
  `~t.vs_halted` by metis_tac[] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`ids`, `T`] tupleLocalStoreRunTheory.tuple_store_mixed_locals_run)) >>
  disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t. stmt_state_rel _ _ _ es' _ /\ _`
    (qx_choose_then `sfv` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  suspend "compose"
QED

Resume assign_tuple_locals_memory_success_run[compose]:
  conj_tac >- simp[] >>
  qexists `sfv` >> simp[] >>
  conj_tac >- suspend "vars" >>
  ntac 3 (qpat_x_assum
    `!fuel. _ ==> ?fuel'. run_from fuel' ctx func _ = _` mp_tac) >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx func _ = r` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  metis_tac[]
QED
Resume assign_tuple_locals_memory_success_run[vars]:
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists `sl` >> simp[]) >>
  simp[]
QED

Finalise assign_tuple_locals_memory_success_run
