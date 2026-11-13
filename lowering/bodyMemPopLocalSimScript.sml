(* Located-value memory simulation for a local dynamic-array pop. *)
Theory bodyMemPopLocalSim
Ancestors
  bodyMemPopLocalPath bodyMemPopLocalFacts exprSimMemDefs exprSimPop
  exprSimDefs exprSimProps exprSimSource exprLowering exprLoweringProps
  compileEnv loweringStateRelDefs context vyperAST vyperValue vyperState vyperInterpreter
  vyperLookup venomState gasOutcome gasSummary fragGasMode fragGasPathMem
  loweringPosts list words arithmetic valueEncoding valueEncodingDefs exprSimVVFrame
  exprSimHypsDefs exprSimMemoryStack venomMemDefs fragExec

Theorem pop_local_source_empty[local]:
  lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
  entry.value = ArrayV (DynArrayV []) ==>
  eval_expr cx (Pop ann (NameTarget id)) es =
    (INR (Error (RuntimeError "pop empty memory array")), es)
Proof
  rpt strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  `IS_SOME (lookup_scopes id es.scopes)` by simp[] >>
  simp[Once evaluate_def, bind_def] >>
  drule_then (qspec_then `cx` SUBST1_TAC) eval_target_place_name >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, return_def,
       raise_def, lift_sum_def, read_memory_path_def, evaluate_subscripts_def,
       check_def]
QED

Theorem pop_local_source_nonempty[local]:
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
  entry.value = ArrayV (DynArrayV vs) /\ vs <> [] ==>
  eval_expr cx (Pop ann (NameTarget id)) es =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))])),
     es with scopes := pre ++ env |+ (id, pop_name_entry entry vs) :: rest)
Proof
  rpt strip_tac >>
  Cases_on `eval_expr cx (Pop ann (NameTarget id)) es` >>
  drule_all eval_pop_name >> strip_tac >> gvs[]
QED

Theorem pop_store_bound_cursor[local,simp]:
  vv_store_bound cx t lt es tv vv (s with vs_inst_idx := k) =
  vv_store_bound cx t lt es tv vv s
Proof
  simp[vv_store_bound_def, eval_operand_def, lookup_var_def]
QED

Theorem compile_pop_name_sim_mem:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Pop ann (NameTarget id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  drule_all pop_name_facts >> strip_tac >>
  `popped_keys_indexed es.scopes` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all compile_expr_pop_name >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Var p) 32 (type_memory_size etv)
              cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory sa` >>
  qmatch_asmsub_rename_tac `compile_dynarray_pop _ _ _ _ _ _ _ = (rop, sc)` >>
  gvs[] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `w2n w + 32 <= s0.vs_alloca_next` by decide_tac >>
  `mload (w2n w) s0 = n2w (LENGTH vs)` by
    gvs[mload_def, mem_word_at_def] >>
  Cases_on `vs = []`
  >- (gvs[] >> drule dynarray_pop_local_empty_path_mem >>
      disch_then (qspecl_then [`s0`, `w`, `ctx`, `func`] mp_tac) >>
      (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "pop empty memory array"))`,
                    `es`, `Abort a t`] >>
      simp[gas_marked_exec_def, exit_result_def, expr_exit_def] >>
      gen_tac >> irule pop_local_source_empty >> simp[]) >>
  `mload (w2n w) s0 <> 0w` by
    (`LENGTH vs <> 0 /\ LENGTH vs < dimword (:256)` by
      (Cases_on `vs` >> gvs[]) >> simp[n2w_11]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  drule_all dynarray_pop_local_path_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  drule dynarray_pop_mem_shape >> strip_tac >> gvs[] >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  rename1 `find_containing_scope id es.scopes = SOME (pre, envs, entry, rest)` >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
             lookup_var q u = lookup_var q s0` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!q. cenv.ce_imm_alloca = SOME (Var q) ==> lookup_var q u = lookup_var q s0`
    by metis_tac[local_ptrs_reserved_imm_base] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id
                  [ValueSubscript (IntV &(LENGTH vs - 1))]))`,
               `es with scopes := pre ++ envs |+ (id, pop_name_entry entry vs) :: rest`,
               `OK (u with vs_inst_idx := LENGTH sc.cs_current_insts)`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, exit_result_def] >>
  conj_tac >-
    (gen_tac >> irule pop_local_source_nonempty >> simp[]) >>
  conj_asm1_tac
  >- (irule (SRULE [vv_post_initial_gas, vv_post_inst_idx]
        (Q.INST [`es` |-> `es with gas_obs := []`] (SPEC_ALL pop_vv_post))) >>
      simp[] >> fs[eval_operand_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  reverse conj_tac
  >- (qpat_x_assum `u = _` SUBST1_TAC >> simp[]) >>
  simp[] >> drule pop_local_vv_post_mem >>
  disch_then irule >> simp[] >>
  conj_tac >- (qpat_x_assum `u = _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`LENGTH vs`, `n`, `sz`, `w`] >>
  Cases_on `vs` >> gvs[]

QED
