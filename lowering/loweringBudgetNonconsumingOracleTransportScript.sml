Theory loweringBudgetNonconsumingOracleTransport
Ancestors
  venomExecSemantics venomState oracleStateProps opcodeClass ptrSafeRun list
  loweringBudgetFrameOracleTransport dftCommutation memSafeRun ptrDiscipline
  fragExec fragGasOrigin fragGasPathPtr fragGasOriginPtr gasEvents
  ctxLookupAgreeHelpers venomInst

Theorem pack_dret_dynamic_outcomes_update:
  !pairs cursor s ptrs fc t os.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    pack_dret_dynamic cursor pairs (s with vs_outcomes := os) =
      (ptrs,fc,t with vs_outcomes := os)
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def, mcopy_def, write_memory_with_expansion_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `os` mp_tac) >> simp[]
QED

val _ = augment_srw_ss [rewrites
  [operand_outcomes_update, eval_operands_outcomes_update,
   one_phi_outcomes_update, active_inst_outcomes_update,
   state_operations_outcomes_update, lookup_var_outcomes_update,
   step_prov_outcomes_update, entry_prov_outcomes_update,
   entry_taint_outcomes_update, write_ranges_outcomes_update,
   read_ranges_outcomes_update, ghost_components_outcomes_update,
   taint_parts_outcomes_update, ptr_predicates_outcomes_update,
   memory_checks_outcomes_update]];

Theorem exec_pure1_outcomes_update[local]:
  exec_pure1 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure1 f inst s)
Proof
  simp[exec_pure1_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_pure2_outcomes_update[local]:
  exec_pure2 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure2 f inst s)
Proof
  simp[exec_pure2_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_pure3_outcomes_update[local]:
  exec_pure3 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure3 f inst s)
Proof
  simp[exec_pure3_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_read0_outcomes_update[local]:
  (!s os. f (s with vs_outcomes := os) = f s) ==>
  exec_read0 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_read0 f inst s)
Proof
  strip_tac >> simp[exec_read0_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_read1_outcomes_update[local]:
  (!v s os. f v (s with vs_outcomes := os) = f v s) ==>
  exec_read1 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_read1 f inst s)
Proof
  strip_tac >> simp[exec_read1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_write2_outcomes_update[local]:
  (!v w s os. f v w (s with vs_outcomes := os) = (f v w s with vs_outcomes := os)) ==>
  exec_write2 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_write2 f inst s)
Proof
  strip_tac >> simp[exec_write2_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_gas_outcomes_update[local]:
  exec_gas inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_gas inst s)
Proof
  simp[exec_gas_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem exec_alloca_outcomes_update[local]:
  exec_alloca inst (s with vs_outcomes := os) n =
  map_result_state (\t. t with vs_outcomes := os) (exec_alloca inst s n)
Proof
  simp[exec_alloca_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

(* map_result_state pushed through the case and if shapes of step_inst. *)
val map_result_rands =
 let
  val project = ``\r:exec_result. map_result_state f r``
  fun through ty = BETA_RULE (ISPEC project (TypeBase.case_rand_of ty))
 in
  map through [``:'a list``, ``:'a option``, ``:'a # 'b``, ``:operand``] @
  [BETA_RULE (PART_MATCH (rator o lhs) COND_RAND project)]
 end;

(* Select the checked dispatch equation for the case split's opcode. *)
fun outcomes_opcode_tac eq =
  PURE_ONCE_REWRITE_TAC [MATCH_MP (valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th))))))
                    (rhs (concl eq)))
    (CONJUNCTS step_inst_base_opcode_eqs))) eq];

Theorem step_inst_base_outcomes_update[local]:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  step_inst_base inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (step_inst_base inst s)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _` outcomes_opcode_tac >>
  simp[exec_pure1_outcomes_update, exec_pure2_outcomes_update,
       exec_pure3_outcomes_update, exec_gas_outcomes_update, exec_alloca_outcomes_update] >>
  all_tac
  >>~- ([`exec_read0 _ _ _ = _`], irule exec_read0_outcomes_update >> simp[])
  >>~- ([`exec_read1 _ _ _ = _`], irule exec_read1_outcomes_update >> simp[])
  >>~- ([`exec_write2 _ _ _ = _`], irule exec_write2_outcomes_update >> simp[]) >>
  all_tac
  >~ [`inst.inst_opcode = DRET`] >- suspend "dret"
  >~ [`inst.inst_opcode = SSTORE`] >- suspend "sstore"
  >~ [`inst.inst_opcode = TSTORE`] >- suspend "tstore" >>
  CONV_TAC (REDEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  simp_tac bool_ss (map_result_state_def :: map_result_rands) >>
  simp[halt_state_def, revert_state_def, set_returndata_def]
QED
Resume step_inst_base_outcomes_update[dret]:
  `!(pairs:(bytes32 # bytes32) list) cursor st.
     pack_dret_dynamic cursor pairs (st with vs_outcomes := os) =
     (FST (pack_dret_dynamic cursor pairs st),
      FST (SND (pack_dret_dynamic cursor pairs st)),
      SND (SND (pack_dret_dynamic cursor pairs st)) with vs_outcomes := os)` by
    (rpt gen_tac >> irule pack_dret_dynamic_outcomes_update >> simp[]) >>
  pop_assum (simp o single) >>
  CONV_TAC (REDEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  simp_tac bool_ss (map_result_state_def :: pairTheory.ELIM_UNCURRY ::
                   map_result_rands) >>
  simp[]
QED
Resume step_inst_base_outcomes_update[sstore]:
  IF_CASES_TAC >> simp[map_result_state_def, exec_write2_outcomes_update]
QED
Resume step_inst_base_outcomes_update[tstore]:
  IF_CASES_TAC >> simp[map_result_state_def, exec_write2_outcomes_update]
QED
Finalise step_inst_base_outcomes_update

Theorem step_inst_outcomes_update:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  step_inst fuel ctx inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (step_inst fuel ctx inst s)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  simp[Once step_inst_def, step_inst_base_outcomes_update] >>
  simp[Once step_inst_def]
QED

Theorem nonconsuming_step_outcomes_update:
  !fuel ctx i s t os.
    i.inst_opcode <> INVOKE /\
    ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
    step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx i (s with vs_outcomes := os) =
      OK (t with vs_outcomes := os)
Proof
  rpt strip_tac >> gvs[step_inst_outcomes_update, map_result_state_def]
QED

Theorem intret_outcomes_update:
  !fuel ctx i s ret t os.
    step_inst fuel ctx i s = IntRet ret t ==>
    step_inst fuel ctx i (s with vs_outcomes := os) =
      IntRet ret (t with vs_outcomes := os)
Proof
  rpt gen_tac >> strip_tac >>
  `i.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `step_inst_base i s = IntRet ret t` by gvs[Once step_inst_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_outcomes_update, map_result_state_def]
QED

Theorem ghost_step_outcomes_update:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  ghost_step fuel ctx PG G tn inst (s with vs_outcomes := os) =
    ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >> simp[ghost_step_def, step_inst_outcomes_update] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[MEM, dftCommutationTheory.map_result_state_def,
       step_prov_outcomes_update, step_taint_noncall_outcomes_update]
QED

Theorem ptr_inst_ok_outcomes_update:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst (s with vs_outcomes := os) =
    ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, ptr_predicates_outcomes_update, step_inst_outcomes_update] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[MEM, dftCommutationTheory.map_result_state_def,
       step_taint_noncall_outcomes_update, ret_taint_def,
       operand_outcomes_update, eval_operands_outcomes_update]
QED

Theorem ptr_safe_outcomes_update:
  (!D lo fuel ctx fn PG G tn inst s os.
    ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
    ptr_safe_step D lo fuel ctx fn PG G tn inst (s with vs_outcomes := os) =
      ptr_safe_step D lo fuel ctx fn PG G tn inst s) /\
  (!D lo fuel ctx fn PG G tn bb s.
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions ==>
    !os. ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_outcomes := os) =
      ptr_safe_block D lo fuel ctx fn PG G tn bb s) /\
  (!D lo fuel ctx fn PG G tn s.
    EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
    !os. ptr_safe_blocks D lo fuel ctx fn PG G tn (s with vs_outcomes := os) =
      ptr_safe_blocks D lo fuel ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[ptr_safe_step_def, ptr_inst_ok_outcomes_update])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
      once_rewrite_tac[ptr_safe_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `~MEM inst.inst_opcode
        [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
        (drule_all EVERY_get_instruction >> simp[]) >>
      simp[ptr_inst_ok_outcomes_update, step_inst_outcomes_update, ghost_step_outcomes_update] >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[dftCommutationTheory.map_result_state_def] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >>~- ([`OK s1`], Cases_on `s1.vs_halted` >>
        gvs[venom_state_fupdcanon, entry_prov_outcomes_update,
            entry_taint_outcomes_update]) >>
      gvs[venom_state_fupdcanon, entry_prov_outcomes_update,
          entry_taint_outcomes_update]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel` >> once_rewrite_tac[ptr_safe_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions` by
    (drule_all EVERY_fn_lookup_block >> simp[]) >>
  simp[eval_phis_outcomes_update] >> Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[map_result_state_def, venom_state_fupdcanon]
QED

Theorem exit_result_outcomes_update:
  exit_result (map_result_state (\t. t with vs_outcomes := os) r) =
    exit_result r
Proof
  Cases_on `r` >> simp[exit_result_def, map_result_state_def]
QED

val _ = augment_srw_ss [rewrites [exit_result_outcomes_update]];

Theorem gas_origin_edge_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_origin_edge memory explicit ctx fn s marks r ==>
  gas_origin_edge memory explicit ctx fn (s with vs_outcomes := os) marks
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  rewrite_tac[gas_origin_edge_def] >> strip_tac >>
  rename1 `lookup_block s.vs_current_bb _ = SOME blk` >>
  rename1 `step_inst fl _ ins s = mid` >>
  `~MEM ins.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
    (imp_res_tac EVERY_fn_lookup_block >> imp_res_tac EVERY_get_instruction >>
     fs[]) >>
  `step_inst fl ctx ins (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) mid` by
    simp[step_inst_outcomes_update] >>
  `ins.inst_opcode <> INVOKE` by fs[MEM] >>
  `memory ==> revert_forward_at blk s.vs_inst_idx \/
    mem_safe_step fl ctx ins (s with vs_outcomes := os)` by
    simp[mem_safe_step_outcomes_update] >>
  gvs[]
  >- (qexists_tac `fl` >> simp[gas_events_step_outcomes_update, map_result_state_def])
  >- (qexists_tac `fl` >> simp[gas_events_step_outcomes_update, map_result_state_def])
  >- (qexists_tac `fl` >>
      simp[gas_events_step_outcomes_update, eval_phis_outcomes_update,
           map_result_state_def])
  >- (qexists_tac `fl` >>
      simp[gas_events_step_outcomes_update, jump_to_def, map_result_state_def] >>
      metis_tac[]) >>
  qexists_tac `fl` >> simp[gas_events_step_outcomes_update]
QED

Theorem gas_origin_path_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s marks r. gas_origin_path memory explicit ctx fn s marks r ==>
  gas_origin_path memory explicit ctx fn (s with vs_outcomes := os) marks
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  strip_tac >>
  qsuff_tac `!memory' explicit' ctx' fn' s marks r.
    gas_origin_path memory' explicit' ctx' fn' s marks r ==>
    memory' = memory /\ explicit' = explicit /\ ctx' = ctx /\ fn' = fn ==>
    gas_origin_path memory explicit ctx fn (s with vs_outcomes := os) marks
      (map_result_state (\t. t with vs_outcomes := os) r)`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
  >- (simp[map_result_state_def] >> irule (cj 1 gas_origin_path_rules) >> simp[])
  >- (drule_all (SRULE [] gas_origin_edge_outcomes_update) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_path_rules]) >>
  drule_all (SRULE [] gas_origin_edge_outcomes_update) >> strip_tac >>
  metis_tac[cj 3 gas_origin_path_rules, exit_result_outcomes_update]
QED

Theorem gas_path_ptr_edge_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  gas_path_ptr_edge D lo ctx fn PG G tn (s with vs_outcomes := os) n G' tn'
    (map_result_state (\t. t with vs_outcomes := os) r)
Proof
  rewrite_tac[gas_path_ptr_edge_def] >> strip_tac >>
  rename1 `lookup_block s.vs_current_bb _ = SOME blk` >>
  rename1 `step_inst fl _ ins s = mid` >>
  `~MEM ins.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]` by
    (imp_res_tac EVERY_fn_lookup_block >> imp_res_tac EVERY_get_instruction >>
     fs[]) >>
  `step_inst fl ctx ins (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) mid` by
    simp[step_inst_outcomes_update] >>
  `ins.inst_opcode <> INVOKE` by fs[MEM] >>
  `ptr_safe_step D lo fl ctx fn PG G tn ins (s with vs_outcomes := os)` by
    simp[cj 1 ptr_safe_outcomes_update] >>
  `gas_count_step fl ctx ins (s with vs_outcomes := os) =
    gas_count_step fl ctx ins s` by
    metis_tac[cj 1 gas_events_length, gas_events_step_outcomes_update] >>
  gvs[]
  >- (qexists_tac `fl` >> simp[ghost_step_outcomes_update, map_result_state_def])
  >- (qexists_tac `fl` >> simp[map_result_state_def])
  >- (qexists_tac `fl` >>
      simp[eval_phis_outcomes_update, map_result_state_def,
           entry_prov_outcomes_update, entry_taint_outcomes_update])
  >- (qexists_tac `fl` >> simp[jump_to_def, map_result_state_def] >> metis_tac[]) >>
  qexists_tac `fl` >> simp[]
QED

Theorem gas_origin_ptr_edge_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s with vs_outcomes := os,G,tn) marks
    (map_result_state (\t. t with vs_outcomes := os) r,G',tn')
Proof
  simp[gas_origin_ptr_edge_def] >> strip_tac >>
  conj_tac >- metis_tac[SRULE [] gas_origin_edge_outcomes_update] >>
  metis_tac[SRULE [] gas_path_ptr_edge_outcomes_update]
QED

Theorem gas_origin_ptr_path_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s G tn marks r G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s with vs_outcomes := os,G,tn) marks
      (map_result_state (\t. t with vs_outcomes := os) r,G',tn')
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !s G tn r G' tn'.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\ out = (r,G',tn') ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s with vs_outcomes := os,G,tn) marks
        (map_result_state (\t. t with vs_outcomes := os) r,G',tn')`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (simp[map_result_state_def] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (drule_all (SRULE [] gas_origin_ptr_edge_outcomes_update) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_ptr_path_rules]) >>
  drule_all (SRULE [] gas_origin_ptr_edge_outcomes_update) >> strip_tac >>
  metis_tac[cj 3 gas_origin_ptr_path_rules, exit_result_outcomes_update]
QED

Theorem gas_origin_ptr_focus_outcomes_update:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn) ==>
  !s G tn marks leaf leaf_pg leaf_g leaf_tn finish.
    gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
    gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
      (s with vs_outcomes := os,G,tn) marks
      (leaf,leaf_pg,leaf_g,leaf_tn,finish with vs_outcomes := os)
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_focus cx st marks out ==>
    !s G tn leaf leaf_pg leaf_g leaf_tn finish.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\
      out = (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
      gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
        (s with vs_outcomes := os,G,tn) marks
        (leaf,leaf_pg,leaf_g,leaf_tn,finish with vs_outcomes := os)`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all (SRULE [] gas_origin_ptr_path_outcomes_update) >>
      simp[map_result_state_def] >> metis_tac[cj 1 gas_origin_ptr_focus_rules])
  >- (drule_all (SRULE [] gas_origin_ptr_path_outcomes_update) >>
      simp[map_result_state_def] >> metis_tac[cj 2 gas_origin_ptr_focus_rules]) >>
  imp_res_tac EVERY_fn_lookup_block >> imp_res_tac EVERY_get_instruction >>
  fs[]
QED
