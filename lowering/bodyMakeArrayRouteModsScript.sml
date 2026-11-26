(* Linked homogeneous MakeArray: allocation, length header, and element run. *)
Theory bodyMakeArrayRouteMods
Ancestors
  bodyMakeArraySourceMods bodyMakeArrayCodeCutsMods bodyMakeArrayAllocCutMods
  bodyMakeArrayHeaderCutMods bodyMakeArrayHeaderFrameMods bodyMakeArrayLoopResultMods
  bodyMakeArrayMaterializedMods bodyMakeElementsContractMods bodyFullIfExpReach
  gasOutcomeFullZeroPrefixMods gasStorage vyperStorageFootprint vyperStorageTrace
  exprSimAggregateEncoding exprLoweringProps exprBodyPreProps valueEncodingProps
  gasOutcomeFullMods gasOutcomeFull gasContext vyperInterpreter vyperState
  bodyFullPostsMods bodyFullPredsMods rich_list vyperMisc integer
  bodyMakeBufferInitMods bodyMakeArrayCompletedMods exprSimDefs stmtSimProps
  haltExitProj gasOutcomeFullPostMods

val _ = Parse.hide "base";

val init_contract = concl (GEN_ALL make_buffer_init_mods);
val completion_contract =
  concl (GEN_ALL (INST_TYPE [alpha |-> ``:256``] make_array_completed_mods));

Theorem array_replicated_layout[local]:
  EVERY (\e. arg_type_fits (expr_type e) et) args /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes ce et = type_memory_size tv ==>
  LIST_REL (\ty e. arg_type_fits (expr_type e) ty) (REPLICATE (LENGTH args) et) args /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) et) =
    SOME (REPLICATE (LENGTH args) tv) /\
  LIST_REL (\ty rt. type_memory_bytes ce ty = type_memory_size rt)
    (REPLICATE (LENGTH args) et) (REPLICATE (LENGTH args) tv)
Proof
  Induct_on `args` >> simp[REPLICATE]
QED

Theorem array_count_fits[local]:
  0 < type_slot_size tv /\ off + k * type_memory_size tv <= cap /\
  cap < dimword (:256) ==> k < dimword (:256) /\ off <= cap
Proof
  strip_tac >> drule (cj 1 type_memory_size_pos) >> strip_tac >>
  `k <= k * type_memory_size tv` by
    (ONCE_REWRITE_TAC [GSYM (cj 2 arithmeticTheory.MULT_CLAUSES)] >>
     simp[arithmeticTheory.LE_MULT_LCANCEL]) >>
  decide_tac
QED

(* The map leaves the source trace, observations and exceptions untouched.
   A successful post may use the exact source result at this same horizon. *)
Theorem array_outcome_map[local]:
  compatible_bound n (LENGTH args) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) ce cx st0
    (eval_exprs cx args) (es,s,G,tn) Q /\
  (!H r ee g tt u. Q H r ee g tt u ==> ISL r) /\
  (!H vs ee g tt u gs.
     eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)
       (es with gas_obs := gs) = (INL (Value (ArrayV (make_array_value tv n vs))),ee) /\
     valid_horizon cx st0 H ee.storage_trace /\ Q H (INL vs) ee g tt u ==>
     P H (INL (Value (ArrayV (make_array_value tv n vs)))) ee g tt u) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args))
    (es,s,G,tn) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  drule_all make_array_source_action_mods >> disch_then (mk_asm "source") >>
  `ignore_bind (eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)) (return ()) =
   ignore_bind (eval_exprs cx args) (return ())` by
    (asm "source" (fn th => simp[FUN_EQ_THM,ignore_bind_def,bind_def,th]) >>
     gen_tac >> Cases_on `eval_exprs cx args x` >> Cases_on `q` >> simp[]) >>
  qhdtm_x_assum `make_elements_run_mods`
    (strip_assume_tac o PURE_REWRITE_RULE [make_elements_run_mods_def,gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- asm "source" (fn th => fs[gas_bad_storage_at_def,th]) >>
      qexistsl [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[])
  >- suspend "result"
  >> disj2_tac >> disj2_tac >> qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> qexists_tac `H` >> simp[]
QED

Resume array_outcome_map[result]:
  disj2_tac >> disj1_tac >> Cases_on `res`
  >- (qexistsl [`INL (Value (ArrayV (make_array_value tv n x)))`,`ee`,`r`,`G'`,`tn'`] >>
      asm "source" (fn th => simp[th]) >> qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]
      >- (first_x_assum irule >> simp[] >> qexists_tac `gas_explicit marks s.vs_gas_readings` >>
          asm "source" (fn th => simp[th]) >>
          qpat_assum `!tail. eval_exprs _ _ (_ with gas_obs := _ ++ tail) = _`
            (qspec_then `[]` (fn th => simp[REWRITE_RULE [APPEND_NIL] th]))) >>
      gvs[expr_exit_def]) >>
  qexistsl [`INR y`,`ee`,`r`,`G'`,`tn'`] >> asm "source" (fn th => simp[th]) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]
  >- (qpat_assum `!H r ee g tt u. Q H r ee g tt u ==> ISL r` drule >> simp[]) >>
  disj2_tac >> conj_tac
  >- (qpat_x_assum `create_size_exit_ok ctx (INR y) r` mp_tac >>
      simp_tac bool_ss [createSizeExitTheory.create_size_exit_ok_def, sumTheory.INR_11]) >>
  qpat_x_assum `(\h rr e g r. _) H (INR y) _ _ _` mp_tac >> BETA_TAC >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:eval_result``] expr_exit_INR_type,
                    INST_TYPE [beta |-> ``:eval_result``] halt_exit_INR_type] >>
  simp[]
QED

Finalise array_outcome_map

Theorem array_route_vv_mods[local]:
  make_elements_contract_mods /\ ^init_contract /\ ^completion_contract /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  strip_tac >> drule_then (qx_choose_then `tv` strip_assume_tac) make_array_source_layout_mods >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac make_array_source_entry_mods >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[] >> qx_gen_tac `tail` >>
      Cases_on `eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)
        (es with gas_obs := tail)` >> simp[] >>
      irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_preserves_bad_domain) >>
      rpt (goal_assum (drule_at Any) ORELSE conj_tac) >>
      simp[evaluate_storage_trace_frame]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] make_array_code_cuts_mods) >>
  disch_then (qx_choosel_then [`ba`,`sm`,`ssm`,`sh`,`ssh`] strip_assume_tac) >>
  qabbrev_tac `cap = type_memory_bytes ce (ArrayT et n)` >>
  qabbrev_tac `h = case n of Dynamic _ => T | _ => F` >>
  qabbrev_tac `off = if h then 32 else 0` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  `make_elements_admissible_mods cx args es` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  suspend "alloc"
QED

Resume array_route_vv_mods[alloc]:
  drule_all (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] make_array_alloc_cut_from_init_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`q`,`base`,`si`,`Gi`,`tni`] strip_assume_tac)) >>
  drule_all_then strip_assume_tac array_count_fits >>
  `h ==> 32 <= cap /\ LENGTH args < dimword (:256)` by (strip_tac >> fs[Abbr `off`]) >>
  qpat_x_assum `ba.buf_operand = Var q` SUBST_ALL_TAC >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [q]` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_id = sa.cs_next_id` by simp[Abbr `ai`,venomInstTheory.mk_inst_def] >>
  `h ==> !H.
      let raw = mstore base (n2w (LENGTH args)) si in
      let i = mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w (LENGTH args))] [] in
      let t = raw with vs_inst_idx := LENGTH sh.cs_current_insts in
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func ce cx es si /\
      immutable_frame_mods func ce cx es si /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx es Gi tni si ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx es (step_prov PG Gi i raw) (step_taint i si raw tni) t` by
    (simp_tac bool_ss [LET_THM] >> strip_tac >> gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qhdtm_x_assum `make_elements_cut_mods`
       (strip_assume_tac o REWRITE_RULE [make_elements_cut_mods_def]) >>
     irule (SIMP_RULE bool_ss [] make_array_header_frame_mods) >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- simp[] >>
     qexistsl [`ai`,`cap`] >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- (qpat_assum `h ==> _` drule >> simp[]) >>
     simp[]) >>
  suspend "header"
QED

Resume array_route_vv_mods[header]:
  qpat_x_assum `h ==> !H. _` (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  drule (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
    (SIMP_RULE bool_ss [LET_THM] make_array_header_cut_from_frame_mods)) >>
  disch_then (fn th => qpat_assum `(if h then _ else _) sm = ((),sh)`
    (mp_tac o MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL th)))) >>
  disch_then (mp_tac o Q.INST [`ai` |-> `ai`, `PG` |-> `PG`] o SPEC_ALL) >>
  (impl_tac >- (simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`sj`,`Gj`,`tnj`] strip_assume_tac) >>
  qabbrev_tac `ps = if h then [(BaseTV (UintT 256),IntV (&LENGTH args),base,32)] else []` >>
  `ci_mono sa sh` by drule_all_then ACCEPT_TAC ci_mono_trans >>
  `sa.cs_next_id < sh.cs_next_id` by fs[make_elements_cut_mods_def] >>
  `make_elements_entry_mods mods exps src tops ce cx env
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0 (sa,es,s0,G0,tn0)
      (sa.cs_next_id,base,cap,q) args ps off sh (es,sj,Gj,tnj)` by
    (simp_tac bool_ss [make_elements_entry_mods_def,make_elements_static_mods_def,
        arithmeticTheory.LESS_EQ_REFL] >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- fs[ci_mono_def]
     >- fs[ci_mono_def]
     >- (qx_gen_tac `H` >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ _`
           (qspec_then `H` mp_tac) >> simp[]) >>
     fs[Abbr `off`]) >>
  suspend "elements"
QED

Resume array_route_vv_mods[elements]:
  drule_all_then strip_assume_tac array_replicated_layout >>
  `off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= cap` by
    (rewrite_tac[type_memory_size_list_replicate] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `Q = make_elements_post_mods mods ce cx env DF lo d ctx func st0
    (sa,es,s0,G0,tn0) (sa.cs_next_id,base,cap,q) args (REPLICATE (LENGTH args) tv)
    ps off sh sb es sj : (bool # 256 word # type_value) list # num list ->
      (value list + exception) -> evaluation_state -> (string |-> num # num) -> taint -> venom_state -> bool` >>
  `make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) ce cx st0
      (eval_exprs cx args) (es,sj,Gj,tnj) Q` by
    (qunabbrev_tac `Q` >>
     qhdtm_assum `make_elements_contract_mods`
       (irule o REWRITE_RULE [make_elements_contract_mods_def]) >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
     qexistsl [`exps`,`ssh`,`shadow_func`,`shadow_sb`,`src`,`tops`,`REPLICATE (LENGTH args) et`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl [`Gi`,`si`,`tni`] >>
  conj_tac >- (gen_tac >> first_assum irule) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl [`Gj`,`sj`,`tnj`] >>
  conj_tac >- (gen_tac >> first_assum irule) >>
  irule array_outcome_map >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  qexistsl [`Q`,`tv`] >>
  reverse (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))
  >- (simp_tac bool_ss [Abbr `Q`,make_elements_post_mods_def] >>
      rpt strip_tac >> ASM_REWRITE_TAC [sumTheory.ISL]) >>
  suspend "post"
QED

Resume array_route_vv_mods[post]:
  BETA_TAC >> map_every qx_gen_tac [`H`,`vs`,`ee`,`g`,`tt`,`u`,`gs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  qabbrev_tac `v = Value (ArrayV (make_array_value tv n vs))` >>
  `make_slot_child_post_mods DF lo d ctx func ce cx
     (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) es sa sb s0 G0 tn0
     (LocatedValue (ArrayT et n) (mk_ptr (Var q) LocMemory)) H (INL v) ee g tt u` suffices_by
    (pure_rewrite_tac[make_slot_child_post_mods_def] >> disch_then ACCEPT_TAC) >>
  qunabbrev_tac `v` >> qunabbrev_tac `Q` >> qunabbrev_tac `ai` >>
  irule (INST_TYPE [alpha |-> ``:exception``] make_array_loop_result_from_completed_mods) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (qexists_tac `gs` >> first_assum ACCEPT_TAC) >>
  qexistsl [`base`,`cap`,`env`,`mods`,`off`,`ps`,`sh`,`si`,`sj`,`st0`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (qpat_assum `!p n. _ ==> mem_bytes_at p n sj.vs_memory = mem_bytes_at p n si.vs_memory`
        mp_tac >> simp[Abbr `off`])
  >- simp[Abbr `ps`, Abbr `h`]
  >- simp[Abbr `cap`] >>
  simp[Abbr `off`, Abbr `h`]
QED

Finalise array_route_vv_mods

Theorem make_array_route_from_elements_mods:
  make_elements_contract_mods /\ ^init_contract /\ ^completion_contract /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray (SOME et) n) args) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  strip_tac >> conj_asm1_tac
  >- (irule array_route_vv_mods >>
      rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >>
      rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  drule_all_then ACCEPT_TAC make_array_materialized_value_from_vv_mods
QED
