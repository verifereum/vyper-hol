(* Actual zero-observation instruction paths for local declarations. *)
Theory stmtSimDeclPath
Ancestors
  stmtSimDeclStore stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  fragGasMode fragGasSeq fragGasPath fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list finite_map pred_set
Libs monadsyntax intLib

Theorem exec_alloca_frames:
  !inst s n s1 p.
    inst.inst_outputs = [p] /\ exec_alloca inst s n = OK s1 ==>
    (!x. x <> p ==> lookup_var x s1 = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP s1.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (rw[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      gvs[FLOOKUP_UPDATE] >> Cases_on `inst.inst_id = aid` >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  rw[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem exec_alloca_memory:
  !inst s n t. exec_alloca inst s n = OK t ==> t.vs_memory = s.vs_memory
Proof
  rpt gen_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def, AllCaseEqs()]
QED

Theorem exec_alloca_operand_frame:
  !inst s n t p.
    exec_alloca inst s n = OK t /\ inst.inst_outputs = [p] ==>
    !op. op <> Var p ==> eval_operand op t = eval_operand op s
Proof
  rpt gen_tac >> simp[exec_alloca_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `op` >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem emit_inst_zero_marked_path:
  emit_inst opc args outs sa = ((), sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args outs) s = OK u ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc args outs]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule emitted_insts_emit_inst >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc args outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
  `gas_path_edge ctx func s 0
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst sa.cs_next_id opc args outs`]
       tuple_straight_line_edge) >>
     simp[venomInstTheory.mk_inst_def]) >>
  drule gas_path_edge_normal >> simp[] >> strip_tac >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_path_rules) >> simp[]
QED

Theorem annassign_alloca_operand_framed_path:
  !ctx func cenv cx es st st1 p sz s0.
    emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), st1) /\
    stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    fn_has_code st st1 func /\ ~s0.vs_halted /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?s1 w. (!op. op <> Var p ==> eval_operand op s1 = eval_operand op s0) /\
      s1.vs_memory = s0.vs_memory /\ lookup_var p s1 = SOME w /\
      FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w, sz) /\
      (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s1.vs_allocas aid = SOME entry) /\
      stmt_state_rel ctx func cenv cx es s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st1.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
      gas_marked_path F ctx func s0 0 (OK s1)
Proof
  rpt strip_tac >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (Cases_on `FLOOKUP s0.vs_allocas st.cs_next_id`
     >- simp[exec_alloca_def] >>
     rename1 `FLOOKUP s0.vs_allocas st.cs_next_id = SOME entry` >>
     PairCases_on `entry` >> simp[exec_alloca_def]) >>
  drule exec_alloca_operand_frame >> simp[] >> disch_tac >>
  drule_all exec_alloca_memory >> strip_tac >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  drule_all exec_alloca_frames >> strip_tac >>
  `gas_marked_path F ctx func s0 0
    (OK (s1 with vs_inst_idx := SUC s0.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >>
     simp[] >>
     qexistsl_tac [`[Lit (n2w sz)]`, `ALLOCA`, `[p]`, `st`, `st1`] >>
     gvs[step_inst_base_def, venomInstTheory.mk_inst_def,
         eval_operand_def, is_terminator_def, Abbr `A`]) >>
  `st1.cs_current_bb = st.cs_current_bb /\
   LENGTH st1.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule gas_marked_path_exec >> strip_tac >>
  drule gas_path_normal >> strip_tac >>
  qexistsl_tac [`s1 with vs_inst_idx := SUC s0.vs_inst_idx`, `w`] >>
  gvs[lookup_var_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
      stmt_state_rel_inst_idx] >>
  qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem emit_mstore_marked_path:
  emit_void MSTORE [Var p; op] st = ((), st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd ==>
  gas_marked_path F ctx func s 0
    (OK (mstore (w2n w) wd s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule emit_inst_zero_marked_path >>
  simp[] >>
  qexistsl_tac [`[Var p; op]`, `MSTORE`, `[]`, `st`, `st'`] >>
  gvs[emit_void_def, emit_inst_def, is_terminator_def] >>
  irule step_MSTORE >> simp[eval_operand_def]
QED

Theorem annassign_word_store_path:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a op st st' wd.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME wd /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ type_memory_size tyv <= sz /\
    val_in_memory tyv v (w2n w) (mstore (w2n w) wd s).vs_memory /\
    val_wf tyv v ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_memory = (mstore (w2n w) wd s).vs_memory /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx es'` >>
  `stmt_state_rel ctx func cenv cx es' (mstore (w2n w) wd s)` by
    (simp[Abbr `es'`] >> irule stmt_state_rel_declare_store >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists_tac `mstore (w2n w) wd s with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, mstore_def, LET_THM]
QED

Theorem annassign_word_store_post_path:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v etv tyv sc rest a.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    store_lays_out etv tyv v /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_memory = (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz)` by metis_tac[] >>
  `val_in_memory tyv v (w2n w)
     (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory /\
   val_wf tyv v /\ type_memory_size tyv = 32` by fs[store_lays_out_def] >>
  `type_memory_size tyv <= sz` by simp[] >>
  drule_all annassign_word_store_path >>
  disch_then (qspecl_then [`a`] mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
