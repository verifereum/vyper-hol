(*
 * Statement simulation: tuple unpacking into locals with memory-backed
 * elements (#637)
 *
 * x1, ..., xn = e for locals xi already in scope and e a tuple whose
 * elements may be words or memory-backed values.  The lowering evaluates e
 * to a pointer to the tuple, stages it in a fresh buffer when e is a
 * memory view held in memory with a memory-backed element
 * (compile_tuple_unpack), loads every word element and the
 * address of every other (compile_tuple_load_all), then stores each into
 * its local (compile_tuple_store_all): an MSTORE for a word, a copy
 * (compile_store_memory) for a memory-backed element.
 *
 * TOP-LEVEL:
 *   compile_assign_tuple_locals_memory_stmt_frag — the statement, every
 *                                                   outcome
 *)

Theory stmtSimAssignTupleMem
Ancestors
  stmtSimForced fragGasMode gasContext exprSimDefs tupleStageProps
  stmtSimProps
  stmtSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimDeclMem
  stmtSimAssignStore stmtSimAssign stmtSimAssignMem stmtSimAssignTuple
  stmtSimReturn exprOperandVar freshWrites tupleAssignMemory valueCopyBytes
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperLookup vyperTyping
  vyperExprNoControl venomInst venomState
Libs
  monadsyntax

(* x1, ..., xn = e for locals x1, ..., xn (n > 0) and e a tuple whose
   elements may be memory-backed.  A word element goes into a word local
   as for compile_assign_tuple_locals_stmt_frag.  A memory-backed element
   is copied (compile_store_memory) from its place in the tuple into its
   local's buffer; the local has the element's type, or both are
   bytestrings (a Bytes[10] element into a Bytes[64] local).  The lowering
   may stage a memory view's tuple in a fresh buffer first (MCOPY); the
   theorem assumes CapMcopy whenever an element is memory-backed, and the
   tuple's size bound when e is also a memory view, the only source it
   stages.  It loads every element before storing any; a tuple that is
   not staged lies where expr_val_at puts it, in e's own buffer or inside
   one local's region, so a store into x_i misses the elements after i. *)
Theorem compile_assign_tuple_locals_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty ids e es tys tvs.
    ids <> [] /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
     type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH ids ==>
       ?p sz vt.
         FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         if is_word_type (EL i tys) then is_word_type vt
         else
           (vt = EL i tys \/
            is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
           type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
           ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
                 type_memory_bytes cenv vt = type_memory_size vtv /\
                 0 < type_memory_size vtv /\
                 type_memory_size vtv + 64 < dimword (:256)) /\
    (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
               (es with gas_obs := gs) = (INL v, es1) ==>
               value_has_type (TupleTV tvs) v) /\
    (!gs vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL (ArrayV (TupleV vs)), es1) /\
       i < LENGTH ids /\
       lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) entry.type (EL i vs)
       else
         ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
              evaluate_type (get_tenv cx) vt = SOME entry.type /\
              value_has_type entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
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
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists `sb` >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  irule forced_then_stmt_outcome >>
  qexistsl [
    `\v ee t. expr_post ctx func cenv cx e es sa su s0 ee v op t /\
              t.vs_current_bb = su.cs_current_bb /\
              t.vs_inst_idx = LENGTH su.cs_current_insts`,
    `e`, `assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))`] >>
  reverse conj_tac
  >- (conj_tac >- simp[eval_assign_tuple_action] >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `su`, `op`, `s0`] mp_tac) >>
      (impl_tac >- (fs[] >> metis_tac[forced_then_admissible, eval_assign_tuple_action])) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  suspend "success"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag[success]:
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  Cases_on `assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v ee` >>
  rename1 `_ = (res, ee')` >>
  `eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
     (es with gas_obs := gs) = (res, ee')` by
    (pure_rewrite_tac[eval_assign_tuple_action] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >> simp[]) >>
  `stmt_res_ok lctx res` by
    (qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `res`, `ee'`] mp_tac) >> simp[]) >>
  `res = INL ()` by
    (drule assign_tuple_locals_ok >> disch_then irule >> gvs[stmt_res_ok_def]) >>
  gvs[] >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  suspend "suffix"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag[suffix]:
  `!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) ee.scopes = SOME entry ==>
     if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
     else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
       evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs)` by
    metis_tac[] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  `post_value_type cenv e = TupleT tys` by
    metis_tac[post_value_type_lowered] >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op t /\
   expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op t` by gvs[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) assign_tuple_locals_memory_suffix_path) >> strip_tac >>
  suspend "post" 
QED

Resume compile_assign_tuple_locals_memory_stmt_frag[post]:
  qexistsl [`INL ()`, `ee'`, `OK t'`] >>
  conj_tac >- (drule assign_tuple_locals_gas >> simp[]) >>
  asm_rewrite_tac [] >> disj1_tac >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  `stmt_state_rel ctx func cenv cx (ee' with gas_obs := []) t'` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee' t'` mp_tac >>
     rpt (pop_assum kall_tac) >>
     mp_tac (Q.INST [`es` |-> `ee'`, `s` |-> `t'`,
                     `gs` |-> `[]`, `readings` |-> `t'.vs_gas_readings`,
                     `k` |-> `t'.vs_inst_idx`] msg_gas_state_frame) >>
     simp[] >> metis_tac[]) >>
  asm_rewrite_tac [] >>
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  metis_tac[]
QED
Finalise compile_assign_tuple_locals_memory_stmt_frag
