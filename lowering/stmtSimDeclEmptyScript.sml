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
 *
 * HELPERS:
 *   annassign_raw_rhs_outcome — a declaration's counted outcome from its
 *                               raw (value_vv) right-hand side's outcome
 *)

Theory stmtSimDeclEmpty
Ancestors
  stmtSimProps stmtSimDefs exprSimDefs loweringPosts list rich_list
  finite_map pred_set fragExec localPtrsProps loweringSlice stmtSimDeclStore
  stmtSimDecl stmtSimDeclMem valueCopyBytes stmtSimDeclCompose
  stmtSimDeclSource stmtSimDeclPath gasOutcome gasContext gasSummary
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps vyperInterpreter vyperState
  vyperValue vyperTyping venomExecSemantics venomInst venomState
  stmtSimDeclGas gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  exprSimMemorySource
Libs
  monadsyntax

Theorem eval_empty_gas_obs[local]:
  !e cx es gs. is_empty_value_expr e ==>
    eval_expr cx e (es with gas_obs := gs) =
      (FST (eval_expr cx e es), (SND (eval_expr cx e es)) with gas_obs := gs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `e` >> gvs[is_empty_value_expr_def]
  >~ [`Literal ann lit`]
  >- (Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
      rename1 `BytesL bs` >> Cases_on `bs` >> gvs[is_empty_value_expr_def] >>
      simp[Ntimes evaluate_def 12, vyperValueOperationTheory.evaluate_literal_def,
           bind_def, return_def])
  >~ [`TypeBuiltin ann tb target args`]
  >- (Cases_on `tb` >> gvs[is_empty_value_expr_def] >>
      Cases_on `args` >>
      simp[Ntimes evaluate_def 12, vyperContextTheory.type_builtin_args_length_ok_def,
           type_check_def, assert_def, ignore_bind_def, bind_def, raise_def,
           return_def, vyperContextTheory.evaluate_type_builtin_def, lift_sum_def,
           AllCaseEqs()] >>
      Cases_on `evaluate_type (get_tenv cx) target` >>
      simp[lift_sum_def, bind_def, return_def, raise_def]) >>
  rename1 `Builtin ann builtin args` >> Cases_on `builtin` >>
  gvs[is_empty_value_expr_def] >>
  rename1 `MakeArray et bd` >> Cases_on `et` >> gvs[is_empty_value_expr_def] >>
  Cases_on `args` >> gvs[is_empty_value_expr_def] >>
  simp[Ntimes evaluate_def 12, vyperContextTheory.builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
       get_accounts_def, vyperContextTheory.evaluate_builtin_def] >>
  Cases_on `compatible_bound bd 0` >>
  Cases_on `evaluate_type (get_tenv cx) x` >>
  simp[bind_def, return_def, raise_def, lift_sum_def]
QED

Theorem eval_empty_default_gas_obs[local]:
  is_empty_value_expr e /\
  (!tv ee. eval_expr cx e es = (INL tv,ee) ==>
           tv = Value (default_value tyv)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
  tv = Value (default_value tyv)
Proof
  strip_tac >> drule eval_empty_gas_obs >>
  disch_then (qspecl_then [`cx`, `es`, `gs`] mp_tac) >>
  Cases_on `eval_expr cx e es` >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem annassign_empty_store_post_path[local]:
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
        (!x. lookup_var x u = lookup_var x s) /\
        u.vs_memory = (mstore (w2n w) 0w s).vs_memory /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP u.vs_allocas aid = SOME entry) /\
        gas_marked_path F ctx func s 0 (OK u)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz)` by metis_tac[] >>
  `val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s).vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    (irule memory_length_word_layout >> simp[mstore_mem_word_at_same] >>
     metis_tac[]) >>
  `32 <= sz` by decide_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all annassign_word_store_path >>
  disch_then (qspec_then `a` mp_tac) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists `u` >> simp[] >> metis_tac[]
QED

Theorem annassign_raw_rhs_outcome:
  !ctx func cx lctx RetQ id typ tyv e es salloc old c sa sf s0 Q.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
       ?v. tv = Value v) /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx e) (es,salloc) Q (\res ee r. expr_exit res r) /\
    (!res ee t. Q res ee t ==> ?tv. res = INL tv) /\
    (!marks v ee t.
      gas_marked_exec F (ctx,func) (eval_expr cx e) (es,salloc)
        marks (INL (Value v)) ee (OK t) /\
      Q (INL (Value v)) (ee with gas_obs := []) t ==>
      ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        stmt_post ctx func cx lctx old c sa sf es s0 (INL ())
          (ff with gas_obs := []) u) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (stmt_post ctx func cx lctx old c sa sf es s0)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gas_outcome_def] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  once_rewrite_tac[bind_assoc] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `?tv. res = INL tv` by metis_tac[] >> gvs[] >>
          `?v. tv = Value v` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >> strip_tac >>
             first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
          gvs[] >>
          qpat_x_assum `!marks v ee t. _` (drule_then mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end`, `t`, `Value v`] >>
          simp[read_result_def, bind_return]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem annassign_empty_normal_continuation[local]:
  !ctx func old c cx lctx id typ tyv e es sa0 st sa sb sf salloc
    marks v ee s vv p sz w inst.
    declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
    (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ has_length_word typ /\
    (!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv,es1) ==>
       tv = Value (default_value tyv)) /\
    local_ptrs_reserved c sa /\ stmt_state_rel ctx func c cx es salloc /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    emit_void MSTORE [Var p; Lit 0w] sb = ((), sf) /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    type_memory_size tyv <= sz /\
    gas_marked_exec F (ctx,func) (eval_expr cx e)
      (es,salloc) marks (INL (Value v)) ee (OK s) /\
    vv_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) (Value v) vv s /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      stmt_post ctx func cx lctx old c sa0 sf es salloc (INL ()) ff u
Proof
  rpt gen_tac >> strip_tac >>
  `!tail. eval_expr cx e
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL (Value v), ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `v = default_value tyv` by
    (first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs tv es1. _` drule >> simp[]) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by
    simp[bind_def, read_result_def, return_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `not_local_ptr c (ee with gas_obs := []).scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `cenv_top_ext old c
    ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)` by
    (irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl [`id`, `sa0`, `st`, `typ`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  ` (ee with gas_obs := []).scopes = sc :: rest /\
    lookup_scopes id (ee with gas_obs := []).scopes = NONE` by (simp[] >> metis_tac[]) >>
  drule_all annassign_empty_store_post_path >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
     simp[]) >>
  `alloca_frame c es sa salloc c (ee with gas_obs := []) s` by
    (irule vv_post_alloca_frame >> metis_tac[]) >>
  `allocas_non_overlapping s /\ lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
   (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
            FLOOKUP s.vs_allocas aid = SOME b)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >> metis_tac[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `32 <= sz` by
    (qspecl_then [`get_tenv cx`, `typ`, `tyv`, `0`, `(mstore 0 0w s).vs_memory`]
       mp_tac memory_length_word_layout >>
     simp[mstore_mem_word_at_same]) >>
  `!aid off z'. FLOOKUP s.vs_allocas aid = SOME (off, z') /\ aid < sa0.cs_next_id ==>
     mem_bytes_at off z' u.vs_memory = mem_bytes_at off z' s.vs_memory` by
    (mp_tac (Q.SPECL [`s`, `inst.inst_id`, `w`, `sz`] mstore_alloca_others) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     rpt strip_tac >>
     `aid <> inst.inst_id` by decide_tac >>
     qpat_x_assum `!wd aid off z'. _` (qspecl_then [`0w`, `aid`, `off`, `z'`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `u.vs_memory = _` (fn th => REWRITE_TAC [th]) >>
     disch_then ACCEPT_TAC) >>
  `((ee with gas_obs := []) with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest).scopes =
   (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` by
    simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by simp[] >>
  `alloca_frame old es sa0 salloc c ((ee with gas_obs := []) with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) u` by
    (mp_tac (Q.INST [`ee` |-> `(ee with gas_obs := []) with scopes :=
         (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`,
       `es1` |-> `ee with gas_obs := []`,
       `s0` |-> `salloc`, `aid0` |-> `inst.inst_id`, `z` |-> `sz`,
       `entry` |-> `<|assignable := T; type := tyv; value := v; popped := []|>`,
       `sa1` |-> `sa`, `t` |-> `u`] alloca_frame_declare_local_store) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  qexistsl [`(ee with gas_obs := []) with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`, `u`] >>
  conj_tac
  >- gvs[gas_marked_exec_def] >>
  gvs[stmt_post_def, stmt_lands_def] >> rpt strip_tac >>
  first_x_assum irule >> fs[not_fresh_at_def]
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
   T's default value (memory_length_word_layout). *)
Theorem compile_annassign_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es tyv.
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
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
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
  drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[annassign_admissible_rhs, forced_expr_admissible_raw] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,salloc)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func c cx e es sA sB salloc ee tv vv t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
     simp[expr_vv_sim_def] >> disch_then irule >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sB.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w, type_memory_bytes cenv vtyp)` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  `!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv,es1) ==>
    tv = Value (default_value tyv)` by
    metis_tac[eval_empty_default_gas_obs] >>
  `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
    (`sA.cs_next_var = st.cs_next_var` by
       (drule emit_inst_extends >> simp[]) >>
     drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
  `sa.cs_next_id <= ai.inst_id /\ sa.cs_next_id <= sA.cs_next_id /\
   sa.cs_next_var <= sA.cs_next_var` by
    (drule_all declare_local_ptr >> strip_tac >>
     qpat_x_assum `emit_inst ALLOCA _ _ _ = _` assume_tac >>
     drule emit_inst_extends >>
     simp[Abbr `ai`, venomInstTheory.mk_inst_def]) >>
  irule annassign_outcome_entry_prefix >>
  simp[] >> qexists_tac `salloc` >> simp[] >>
  irule annassign_raw_rhs_outcome >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size tyv <= type_memory_bytes cenv vtyp` by simp[] >>
  drule_all annassign_empty_normal_continuation >> strip_tac >>
  qexistsl [`ff`, `u`] >> simp[] >>
  qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_post_def, stmt_state_rel_def, state_rel_gas_obs,
       immutable_alloca_sep_def] >> strip_tac >> simp[] >>
  `alloca_frame cenv es sa salloc c (ff with gas_obs := []) u` by
    (qpat_x_assum `alloca_frame cenv es sa salloc c ff u` mp_tac >>
     simp[alloca_frame_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
