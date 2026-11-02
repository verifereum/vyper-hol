(*
 * Statement simulation: a declaration initialised with the empty value
 * (#637)
 *
 * x: T = e for a type T with a length word (a bytestring or a dynamic
 * array) and e the empty value (empty(T), b"", an empty list): the
 * lowering runs e's code, drops its value_vv, and stores a zero length
 * word at the local's buffer, which lays out T's default value.
 *
 * TOP-LEVEL:
 *   compile_annassign_empty_stmt_frag — the declaration, for every outcome
 *                                       of its right-hand side
 *)

Theory stmtSimDeclEmpty
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclStore
  stmtSimDecl stmtSimDeclMem valueCopyBytes
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperTyping
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* A type with a length word has a default value laid out by a zero word,
   in at least one word. *)
Theorem has_length_word_default[local]:
  !tenv t tv off s.
    has_length_word t /\ evaluate_type tenv t = SOME tv ==>
    val_in_memory tv (default_value tv) off (mstore off 0w s).vs_memory /\
    val_wf tv (default_value tv) /\ 32 <= type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytestring_type t \/ ?et n. t = ArrayT et (Dynamic n)` by
    (Cases_on `t` >> gvs[has_length_word_def] >>
     rename1 `ArrayT _ bd` >> Cases_on `bd` >> gvs[has_length_word_def])
  >- (drule_all bytestring_type_value >> strip_tac >>
      gvs[default_value_def, val_in_memory_def, val_wf_def,
          type_memory_size_def, mstore_mem_word_at_same, mem_bytes_at_def]) >>
  gvs[evaluate_type_def, AllCaseEqs(), default_value_def, val_in_memory_def,
      val_wf_def, type_memory_size_def, mstore_mem_word_at_same]
QED

Theorem annassign_empty_store_run[local]:
  !ctx func cenv cx es s id p sz w inst t tyv sc rest a st st' tenv.
    emit_void MSTORE [Var p; Lit 0w] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    has_length_word t /\ evaluate_type tenv t = SOME tyv /\
    type_memory_size tyv <= sz ==>
    ?u. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv;
                           value := default_value tyv; popped := []|>)) :: rest) u /\
        ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb /\
        u.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x u = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP u.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >>
  drule_all has_length_word_default >>
  disch_then (qspecl_then [`w2n w`, `s`] strip_assume_tac) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s`, `id`, `p`, `sz`, `w`,
               `inst`, `default_value tyv`, `tyv`, `sc`, `rest`, `a`,
               `Lit 0w`, `st`, `st'`, `0w`] mp_tac annassign_word_store_run >>
  impl_tac >- simp[eval_operand_lit] >>
  disch_then ACCEPT_TAC
QED

Theorem annassign_empty_store_post_run[local]:
  !ctx func cenv cx e es es1 s0 s sa sb sf tv vv id p sz w inst t tyv sc rest a tenv.
    vv_post ctx func cenv cx e es sa sb s0 es1 tv vv s /\
    emit_void MSTORE [Var p; Lit 0w] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    has_length_word t /\ evaluate_type tenv t = SOME tyv /\
    type_memory_size tyv <= sz ==>
    ?u. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv;
                           value := default_value tyv; popped := []|>)) :: rest) u /\
        ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
        u.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
               lookup_var x u = SOME v) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP u.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz)` by metis_tac[] >>
  drule_all annassign_empty_store_run >>
  disch_then (qspecl_then [`a`] mp_tac) >> strip_tac >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED

Theorem annassign_empty_success_run[local]:
  !ctx func cenv cx id vtyp e es es' tyv sa sb sf vv p sz s0 w inst.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              tv = Value (default_value tyv)) /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    compile_expr cenv (expr_type e) e sa = (vv, sb) /\
    emit_void MSTORE [Var p; Lit 0w] sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    type_memory_size tyv <= sz ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!tv es1. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  gvs[read_result_def, return_def] >>
  `not_local_ptr cenv es1.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `INL (Value (default_value tyv))`,
                           `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_vv_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  `lookup_scopes id es1.scopes = NONE` by gvs[] >>
  drule_all annassign_empty_store_post_run >>
  disch_then (qspecl_then [`T`] mp_tac) >> strip_tac >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED

Theorem expr_vv_sim_error_run[local]:
  !ctx func cenv cx ty e es ex es' sa sb vv s0.
    expr_vv_sim ctx func cenv cx ty e es /\
    eval_expr cx e es = (INR ex, es') /\
    expr_res_ok (INR ex : value + exception) /\
    compile_expr cenv ty e sa = (vv, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             expr_exit (INR ex : unit + exception) r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `INR ex`, `es'`, `s0`] mp_tac) >>
  impl_tac >- gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  metis_tac[expr_exit_INR_type]
QED

Theorem compile_annassign_empty_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word vtyp /\ is_empty_value_expr e ==>
    ?sA vv sB.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sB) /\
      emit_void MSTORE [Var p; Lit 0w] sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >> gvs[]
QED

Theorem annassign_empty_code_parts[local]:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ has_length_word vtyp /\ is_empty_value_expr e /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b vv. compile_expr c (expr_type e) e a = (vv, b) ==> cs_extends a b) ==>
    ?st sA sB vv p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sB) /\
      emit_void MSTORE [Var p; Lit 0w] sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all compile_annassign_empty_parts >>
  disch_then (qx_choosel_then [`sA`, `vv`, `sB`] strip_assume_tac) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `cs_extends sA sB` by metis_tac[] >>
  `cs_extends sB sf` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  qexistsl [`st`, `sA`, `sB`, `vv`, `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[]
QED

(* x: T = e for a type T with a length word, where e is the empty value
   and its values are T's default value.  The lowering keeps e's code
   (e's judgment is expr_vv_sim, as e's value_vv is never unwrapped) and
   stores a zero length word at the local's buffer of type_memory_bytes of
   T, the size val_in_memory lays a value of T out in. *)
(* Why it holds.  As compile_annassign_memory_stmt_frag: the relation at
   the declared environment c, the local's ALLOCA, then e's fragment,
   which exits on an error or ends in vv_post; then the MSTORE of 0 at the
   local's buffer, whose region misses every other live local's, lays out
   T's default value (has_length_word_default). *)
Theorem compile_annassign_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' tyv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    has_length_word vtyp /\ is_empty_value_expr e /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_size tyv < dimword (:256) /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              tv = Value (default_value tyv)) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_vv_sim ctx func c cx (expr_type e) e es /\
       !sa sb vv. compile_expr c (expr_type e) e sa = (vv, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
     !a b vv. compile_expr c (expr_type e) e a = (vv,b) ==> cs_extends a b` by
    metis_tac[] >>
  drule_all annassign_empty_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sB`, `vv`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id vtyp sa = (c,st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  `stmt_state_rel ctx func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  `type_memory_bytes cenv vtyp < dimword (:256)` by simp[] >>
  drule_all annassign_alloca_framed_run >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  Cases_on `res`
  >- suspend "success" >>
  rename1 `eval_stmt _ _ _ = (INR ex, _)` >>
  `(do raw <- eval_expr cx e; read_result cx raw od) es = (INR ex,es') /\
   expr_res_ok (INR ex : value + exception)` by
    (drule eval_annassign_word_error >> simp[] >>
     disch_then (qspec_then `lctx` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_expr cx e es = (INR ex,es')` by
    (Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1,es1)` >>
     Cases_on `r1` >> gvs[bind_def, read_result_def, return_def]) >>
  drule_all expr_vv_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED

Resume compile_annassign_empty_stmt_frag[success]:
  rename1 `eval_stmt _ _ _ = (INL u, _)` >> Cases_on `u` >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w,type_memory_bytes cenv vtyp)` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  `type_memory_size tyv <= type_memory_bytes cenv vtyp` by simp[] >>
  drule_all annassign_empty_success_run >> strip_tac >>
  `!tv es1. eval_expr cx e es = (INL tv,es1) ==> ?v. tv = Value v` by metis_tac[] >>
  drule_all annassign_word_top_ext >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
    (`sA.cs_next_var = st.cs_next_var` by
       (drule emit_inst_extends >> simp[]) >>
     drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
  disj1_tac >> qexistsl [`t`, `c`] >> simp[stmt_lands_def] >>
  conj_tac
  >- (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func salloc = r /\ _ ==> _`
    drule >> simp[]
QED

Finalise compile_annassign_empty_stmt_frag
