(* Compiled statement environments, reservations and frame facts. *)
Theory stmtSimProps
Ancestors
  fragGasPath fragGasPathMem gasCount stmtSimDefs memSafeRun instMemFrontier opcodeClass
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec fragExecMem localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState venomMemDefs integer_word
Libs
  monadsyntax intLib

Theorem immutable_prefix_bound_scopes[simp]:
  immutable_prefix_bound cenv addr src (es with scopes := scs) cap <=>
  immutable_prefix_bound cenv addr src es cap
Proof
  simp[immutable_prefix_bound_def]
QED

Theorem immutable_prefix_bound_local_entry:
  !cenv bc addr src es cap.
    immutable_prefix_bound cenv addr src es cap /\
    bc.ce_module_vars = cenv.ce_module_vars ==>
    immutable_prefix_bound bc addr src es cap
Proof
  rw[immutable_prefix_bound_def] >> metis_tac[]
QED

Theorem exec_alloca_prefix_base:
  !func cenv cx es inst s n s' p w cap ctx.
    stmt_state_rel ctx func cenv cx es s /\ alloca_prefix cap s /\
    inst.inst_outputs = [p] /\ exec_alloca inst s n = OK s' /\
    lookup_var p s' = SOME w ==> cap <= w2n w
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, LET_THM] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]
  >- (strip_tac >>
      gvs[alloca_prefix_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME region` >>
  PairCases_on `region` >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `region0 < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     res_tac >> DECIDE_TAC) >>
  fs[alloca_prefix_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  metis_tac[]
QED

Theorem ret_pc_ok_frame:
  !cenv cenv' sa sb s s'.
    ret_pc_ok cenv sa s /\ cenv'.ce_return_pc = cenv.ce_return_pc /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x s' = SOME w) ==>
    ret_pc_ok cenv' sb s'
Proof
  rw[ret_pc_ok_def] >> qpat_x_assum `!x sz. _` drule >> strip_tac
  >- (fs[not_fresh_at_def] >> rpt strip_tac >>
      qpat_x_assum `!n. sa.cs_next_var <= n ==> _` (qspec_then `n` mp_tac) >>
      simp[]) >>
  rename1 `lookup_var x s = SOME w` >> qexists_tac `w` >>
  qpat_x_assum `!x w. _ ==> _` irule >> simp[]
QED

Theorem ret_pc_ok_jump_to:
  !cenv sa l s. ret_pc_ok cenv sa (jump_to l s) <=> ret_pc_ok cenv sa s
Proof
  simp[ret_pc_ok_def, lookup_var_def, jump_to_def]
QED

Theorem cenv_top_ext_return_pc:
  !cenv c sc. cenv_top_ext cenv c sc ==> c.ce_return_pc = cenv.ce_return_pc
Proof
  rw[cenv_top_ext_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem cenv_top_ext_refl:
  !cenv scopes. cenv_top_ext cenv cenv scopes
Proof
  rw[cenv_top_ext_def, compileEnvTheory.compile_env_component_equality]
QED

Theorem emit_jump_zero_path_mem:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_mem ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     `mem_safe_step 0 ctx (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
       (simp[mem_safe_step_non_invoke, mk_inst_def] >>
        irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem emit_jump_zero_path:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all emit_jump_zero_path_mem >>
  metis_tac[gas_path_mem_exec]
QED

Theorem run_from_jump_end:
  !ctx func sa sb ss inst lbl.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    fn_has_code sa sb func /\
    ss.vs_current_bb = sa.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst ss = OK (jump_to lbl ss) /\ ~ss.vs_halted ==>
    !fuel r. run_from fuel ctx func (jump_to lbl ss) = r /\
             (!e. r <> Error e) ==>
             ?fuel'. run_from fuel' ctx func ss = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule run_from_jump_result >> gvs[] >> metis_tac[]
QED

Theorem stmts_env_cons:
  !cenv lctx ty s ss sa.
    ~block_is_terminated sa ==>
    stmts_env cenv lctx ty (s::ss) sa =
    (do c <- stmt_env cenv lctx ty s; stmts_env c lctx ty ss od) sa
Proof
  rw[stmts_env_def, stmt_env_def, comp_bind_def, comp_get_def,
     comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem cenv_top_ext_trans:
  !c1 c2 c3 sc1 sc2.
    cenv_top_ext c1 c2 sc1 /\ cenv_top_ext c2 c3 sc2 /\
    (sc1 = [] <=> sc2 = []) /\ MAP FDOM (TL sc1) = MAP FDOM (TL sc2) ==>
    cenv_top_ext c1 c3 sc2
Proof
  rw[cenv_top_ext_def]
  >- fs[compileEnvTheory.compile_env_component_equality]
  >- (Cases_on `FLOOKUP c2.ce_vars n = FLOOKUP c1.ce_vars n` >> gvs[] >>
      metis_tac[])
  >- (Cases_on `FLOOKUP c3.ce_vars n = FLOOKUP c2.ce_vars n` >> gvs[] >>
      metis_tac[]) >>
  Cases_on `FLOOKUP c3.ce_vars n = FLOOKUP c2.ce_vars n`
  >- (`FLOOKUP c2.ce_vars n <> FLOOKUP c1.ce_vars n` by metis_tac[] >>
      qpat_x_assum `!n. FLOOKUP c2.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> Cases_on `sc2` >> gvs[] >>
      irule lookup_scopes_none_map_fdom >> metis_tac[]) >>
  metis_tac[]
QED

Theorem stmt_state_rel_pop_top_ext:
  !func cenv cenv' cx es ss sc rest ctx.
    stmt_state_rel ctx func cenv' cx es ss /\ cenv_top_ext cenv cenv' es.scopes /\
    es.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    stmt_state_rel ctx func cenv cx (es with scopes := rest) ss
Proof
  rpt strip_tac >>
  drule_all stmt_state_rel_pop_scope >> strip_tac >>
  irule stmt_state_rel_cenv_cong >>
  qexists_tac `cenv'` >> fs[cenv_top_ext_def] >>
  `cenv'.ce_module_vars = cenv.ce_module_vars` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> CCONTR_TAC >>
      qpat_x_assum `!n. FLOOKUP cenv'.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> rpt strip_tac >> gvs[])
  >- simp[]
  >- simp[] >>
  fs[compileEnvTheory.compile_env_component_equality]
QED

Theorem declare_stmt_local_reserved:
  !cenv stmt st cenv' st'.
    declare_stmt_local cenv stmt st = (cenv', st') /\
    local_ptrs_reserved cenv st ==>
    local_ptrs_reserved cenv' st' /\ st.cs_next_var <= st'.cs_next_var /\
    cs_extends st st'
Proof
  rpt gen_tac >> Cases_on `stmt` >>
  simp[declare_stmt_local_def, comp_return_def] >>
  TRY (rw[] >> simp[cs_extends_refl] >> NO_TAC) >>
  rw[declare_local_def, comp_bind_def, fresh_var_def, comp_return_def] >>
  gvs[cs_extends_refl] >>
  TRY (irule cs_extends_same_block >> simp[] >> NO_TAC) >>
  TRY (fs[local_ptrs_reserved_def] >> NO_TAC) >>
  fs[local_ptrs_reserved_def, FLOOKUP_UPDATE] >> rw[] >> gvs[AllCaseEqs()] >>
  fs[not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
  FIRST (map (fn (a, b) =>
    first_x_assum drule >> disch_then (qspecl_then [a, b] mp_tac) >>
    simp[] >> TRY (qexists_tac `st.cs_next_var` >> simp[]) >> NO_TAC)
    [(`n1`, `sz1`), (`n2`, `sz2`)])
QED

Theorem stmt_env_reserved:
  !cenv lctx ty stmt sa c sb.
    stmt_env cenv lctx ty stmt sa = (c, sb) /\
    (!c'. cs_mono (compile_stmt c' lctx ty stmt)) /\
    local_ptrs_reserved cenv sa ==>
    local_ptrs_reserved c sb /\ cs_extends sa sb /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_all declare_stmt_local_reserved >> strip_tac >>
  fs[cs_mono_def] >> first_x_assum drule >> strip_tac >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> metis_tac[])
  >- metis_tac[cs_extends_trans] >>
  decide_tac
QED

Theorem declare_local_ptr:
  !cenv id fty st bc st1.
    declare_local cenv id fty st = (bc, st1) /\ cenv.ce_alloca_locals ==>
    st1 = st with cs_next_var := st.cs_next_var + 1 /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var (STRING #"%" (toString st.cs_next_var)))
                   (type_memory_bytes cenv fty)) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv
Proof
  rw[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
     LET_THM] >>
  gvs[FLOOKUP_UPDATE, compileEnvTheory.compile_env_component_equality]
QED

Theorem declare_local_reserved:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ local_ptrs_reserved cenv st ==>
    local_ptrs_reserved c st1
Proof
  rpt strip_tac >>
  qspecl_then [`cenv`, `AnnAssign id ty (Literal ty (IntL 0))`, `st`, `c`,
               `st1`] mp_tac declare_stmt_local_reserved >>
  simp[declare_stmt_local_def]
QED

Theorem compile_stmts_env:
  !ss cenv lctx ty st.
    compile_stmts cenv lctx ty ss st = ((), SND (stmts_env cenv lctx ty ss st))
Proof
  Induct
  >- simp[compile_stmt_def, stmts_env_def, comp_return_def] >>
  rpt gen_tac >> simp[Once compile_stmt_def, stmts_env_def] >>
  simp[comp_bind_def, comp_get_def, comp_ignore_bind_def] >> rw[] >>
  simp[comp_return_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem expr_exit_INR_type:
  !ex rr. expr_exit (INR ex : 'a + exception) rr =
          expr_exit (INR ex : 'b + exception) rr
Proof
  rpt gen_tac >> Cases_on `rr` >> Cases_on `ex` >> simp[expr_exit_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def])
QED


Theorem emit_abort_zero_path:
  emit_inst opc ops [] sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t ==>
  gas_path ctx func s 0 (Abort a t)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0 (Abort a t)` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          exit_result_def] >> metis_tac[]) >>
  metis_tac[gas_path_rules, exit_result_def]
QED

Theorem emit_abort_zero_path_mem:
  emit_inst opc ops [] sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\
  inst_mem_below_frontier (mk_inst sa.cs_next_id opc ops []) s /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t ==>
  gas_path_mem ctx func s 0 (Abort a t)
Proof
  strip_tac >>
  `inst_dload_in_section (mk_inst sa.cs_next_id opc ops []) s` by
    (drule step_inst_base_abort_opcodes >> simp[mk_inst_def] >>
     strip_tac >> gvs[inst_dload_in_section_def, mk_inst_def]) >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx func s 0 (Abort a t)` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     `mem_safe_step 0 ctx (mk_inst sa.cs_next_id opc ops []) s` by
       simp[mem_safe_step_non_invoke, mk_inst_def] >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          exit_result_def] >> metis_tac[]) >>
  metis_tac[gas_path_mem_rules, exit_result_def]
QED

Theorem emit_abort_exit:
  !ctx func opc ops st st' s0 RetQ es' res.
    emit_inst opc ops [] st = ((), st') /\ fn_has_code st st' func /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
    opc <> INVOKE /\
    (?a s'. step_inst_base (mk_inst st.cs_next_id opc ops []) s0 =
              Abort a s' /\ expr_exit res (Abort a s')) ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             stmt_exit RetQ es' res r
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  `frag_exec ctx st st' (\s. s = s0) (\s. F) (stmt_exit RetQ es' res)` by
    (irule frag_exec_step_abort >> fs[] >> qexists_tac `0` >>
     fs[step_inst_non_invoke, venomInstTheory.mk_inst_def, stmt_exit_def]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >> simp[frag_exec_def]
QED

Theorem assert_jnz_zero_path:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME (if b then 1w else 0w) ==>
  gas_path ctx func s 0 (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] assume_tac) >>
  `gas_path_edge ctx func s 0 (OK (jump_to (if b then lt else lf) s))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jnz_behavior, is_terminator_def] >>
     Cases_on `b` >> gvs[] >> metis_tac[]) >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem assert_jnz_zero_path_mem:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME (if b then 1w else 0w) ==>
  gas_path_mem ctx func s 0 (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] assume_tac) >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to (if b then lt else lf) s))` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     `mem_safe_step 0 ctx (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
       (simp[mem_safe_step_non_invoke, mk_inst_def] >>
        irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jnz_behavior, is_terminator_def] >>
     Cases_on `b` >> gvs[] >> metis_tac[]) >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem run_from_jump_end_mem:
  !ctx func sa sb ss inst lbl.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    fn_has_code sa sb func /\
    ss.vs_current_bb = sa.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst ss = OK (jump_to lbl ss) /\ ~ss.vs_halted /\
    inst_mem_below_frontier inst ss ==>
    !fuel r. run_from fuel ctx func (jump_to lbl ss) = r /\
      (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ss = r /\
        (mem_safe_run fuel ctx func (jump_to lbl ss) ==>
         mem_safe_run fuel' ctx func ss)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule mem_safe_run_jump_result >> simp[] >>
  qexists_tac `0` >>
  gvs[step_inst_non_invoke, mem_safe_step_non_invoke,
      inst_dload_in_section_def, is_terminator_def]
QED

Theorem emit_abort_exit_mem:
  !ctx func opc ops st st' s0 RetQ es' res.
    emit_inst opc ops [] st = ((), st') /\ fn_has_code st st' func /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
    opc <> INVOKE /\ inst_mem_below_frontier (mk_inst st.cs_next_id opc ops []) s0 /\
    (?a s'. step_inst_base (mk_inst st.cs_next_id opc ops []) s0 =
              Abort a s' /\ expr_exit res (Abort a s')) ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             stmt_exit RetQ es' res r /\ mem_safe_run fuel ctx func s0
Proof
  rpt strip_tac >>
  `inst_dload_in_section (mk_inst st.cs_next_id opc ops []) s0` by
    (drule step_inst_base_abort_opcodes >> simp[mk_inst_def] >>
     strip_tac >> gvs[inst_dload_in_section_def, mk_inst_def]) >>
  drule emit_inst_extends >> strip_tac >>
  `frag_exec_mem ctx st st' (\s. s = s0) (\s. F) (stmt_exit RetQ es' res)` by
    (irule frag_exec_mem_step_abort >> fs[] >> qexists_tac `0` >>
     fs[step_inst_non_invoke, mk_inst_def, stmt_exit_def,
        mem_safe_step_non_invoke]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >> simp[frag_exec_mem_def]
QED
