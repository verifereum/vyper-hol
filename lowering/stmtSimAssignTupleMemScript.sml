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
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclMem
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
   theorem assumes CapMcopy, and the tuple's size bound, whenever an
   element is memory-backed, staged or not.  It loads every element before storing any; a tuple that is
   not staged lies where expr_val_at puts it, in e's own buffer or inside
   one local's region, so a store into x_i misses the elements after i. *)
Theorem compile_assign_tuple_locals_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty ids e es res es' tys tvs.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (res, es') /\
    ids <> [] /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==>
     cenv.ce_target CapMcopy /\ type_memory_size (TupleTV tvs) < dimword (:256)) /\
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
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
               (INL v, es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL (ArrayV (TupleV vs)), es1) /\
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
      es res es'
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
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
  Cases_on `res`
  >- (rename1 `eval_stmt _ _ _ = (INL u, _)` >> Cases_on `u` >>
      drule_all assign_tuple_locals_memory_success_run >> strip_tac >>
      disj1_tac >> qexistsl [`t`, `cenv`] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]) >>
  rename1 `eval_stmt _ _ _ = (INR y, _)` >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INR y, es') /\
   expr_res_ok (INR y : value + exception)` by
    (drule eval_assign_tuple_locals_error >> disch_then drule >> simp[]) >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (qspecl_then [`sa`, `su`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  drule_all stmtSimDeclTheory.expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED
