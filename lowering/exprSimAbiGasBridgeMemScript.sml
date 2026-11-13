(* A cut observer supplies both execution and memory checks of the same path. *)
Theory exprSimAbiGasBridgeMem
Ancestors
  exprSimAbiGasBridge memContinuationExit fragGasPathMem contextCodegenRel
  instMemFrontier fragExecMem abiEncoderObserver venomExecSemantics
  venomExecProofs venomState emitHelper venomInst memSafeRun exprLoweringProps
  compileEnv fragExec list rich_list fragGasPath gasCount codegenRel unitTransformDefs
  arithmetic

Theorem mem_cont_sim_gas_path_mem:
  !ctx sa sb Q fn s.
    (!fn'. fn_has_code sa sb fn' /\ fn_inst_ids_distinct fn' /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP ==>
            MEM i (fn_insts fn)) /\
       (sa.cs_blocks = sb.cs_blocks \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           mem_cont_sim ctx fn' s t) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?id. !inst. MEM inst (fn_insts fn) ==> inst.inst_id <> id` by
    metis_tac[frag_observer_fresh_id] >>
  qpat_x_assum `!fn'. _` (qspec_then `frag_observer sa sb fn id` mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[frag_observer_has_code]
      >- metis_tac[frag_observer_ids_distinct]
      >- metis_tac[frag_observer_nonstop_inclusion] >>
      metis_tac[frag_observer_end_phi_zero]) >>
  strip_tac >> rename1 `Q t` >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t) /\
          mem_safe_run fuel ctx (frag_observer sa sb fn id) s` by
    suspend "safe_stop" >>
  `!fuel. mem_safe_run fuel ctx (frag_observer sa sb fn id) s` by
    (irule mem_safe_run_all_fuel >> qexists_tac `fuel` >> simp[]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `!ct observed cut a b. local_prefix ct observed cut a b ==>
    !saa sbb func oid.
    observed = frag_observer saa sbb func oid /\ cut = frag_observer_cut sbb /\
    cs_extends saa sbb /\ fn_has_code saa sbb func /\ frag_gas_free saa sbb /\
    (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region saa sbb /\
    (!fuel. mem_safe_run fuel ct observed a) ==>
    gas_path_mem ct func a 0 (OK b)` by suspend "safe_prefix" >>
  `gas_path_mem ctx fn s 0 (OK u)` by
    (qpat_x_assum `!ct observed cut a b. _`
       (qspecl_then [`ctx`, `frag_observer sa sb fn id`, `frag_observer_cut sb`,
          `s`, `u`] mp_tac) >> simp[] >>
     disch_then (qspecl_then [`sa`, `sb`, `fn`, `id`] mp_tac) >> simp[] >>
     metis_tac[frag_observer_start_region]) >>
  drule local_prefix_endpoint >> strip_tac >>
  qexists_tac `u` >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED

Resume mem_cont_sim_gas_path_mem[safe_stop]:
  `step_inst 0 ctx (mk_inst id STOP [] []) t = Halt (stop_view t)` by
    (simp[step_inst_non_invoke, stop_view_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  `mem_safe_step 0 ctx (mk_inst id STOP [] []) t` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         mk_inst_def] >>
  qspecl_then [`0`, `ctx`, `frag_observer sa sb fn id`, `t`,
    `<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
    `mk_inst id STOP [] []`, `Halt (stop_view t)`] mp_tac run_from_step_exit >>
  simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >> strip_tac >>
  irule mem_cont_sim_exit_run >> simp[exit_result_def] >> metis_tac[]
QED

Resume mem_cont_sim_gas_path_mem[safe_prefix]:
  rpt (pop_assum kall_tac) >> ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ct (frag_observer saa sbb func oid)
    (frag_observer_cut sbb) a middle` >>
  `!fuel. mem_safe_run fuel ct (frag_observer saa sbb func oid) middle` by
    suspend "next_safe" >>
  `gas_path_mem_edge ct func a 0 (OK middle)` by suspend "memory_edge" >>
  `gas_path_mem ct func middle 0 (OK b)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_region_closed_def, frag_observer_region_closed]) >>
  metis_tac[cj 2 gas_path_mem_rules, ADD]
QED

Resume mem_cont_sim_gas_path_mem[next_safe]:
  qpat_x_assum `abi_observer_step _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  rename1 `step_inst 0 ct inst a = OK stepped` >>
  qx_gen_tac `budget`
  >- (`step_inst budget ct inst a = OK stepped` by
        metis_tac[step_inst_non_invoke] >>
      qspecl_then [`budget`, `ct`, `frag_observer saa sbb func oid`, `a`,
        `bb`, `inst`, `stepped`] mp_tac mem_safe_run_step >>
      simp[] >> metis_tac[]) >>
  `step_inst (SUC budget) ct inst a = OK stepped` by
    metis_tac[step_inst_non_invoke] >>
  `mem_safe_blocks (SUC budget) ct (frag_observer saa sbb func oid) stepped` by
    (irule mem_safe_run_terminator >> metis_tac[]) >>
  drule_all mem_safe_blocks_run >> metis_tac[]
QED

Resume mem_cont_sim_gas_path_mem[memory_edge]:
  `!xs ys sid left right k.
    left.bb_instructions = xs ++ [mk_inst sid STOP [] []] /\
    right.bb_instructions = xs ++ ys /\ revert_forward_at left k ==>
    revert_forward_at right k` by suspend "prefix_forward" >>
  `gas_path_edge ct func a 0 (OK middle)` by
    (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  qpat_x_assum `abi_observer_step _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  rename1 `step_inst 0 ct inst a = OK stepped` >>
  `revert_forward_at bb a.vs_inst_idx \/ mem_safe_step 0 ct inst a` by
    (irule mem_safe_run_head >> metis_tac[]) >>
  `?original. lookup_block a.vs_current_bb func.fn_blocks = SOME original /\
              get_instruction original a.vs_inst_idx = SOME inst` by
    (irule frag_observer_instruction_agrees >> metis_tac[]) >>
  `revert_forward_at original a.vs_inst_idx \/ mem_safe_step 0 ct inst a` by
    (Cases_on `mem_safe_step 0 ct inst a` >> simp[] >>
     `revert_forward_at bb a.vs_inst_idx` by metis_tac[] >>
     qpat_x_assum `lookup_block a.vs_current_bb
       (frag_observer saa sbb func oid).fn_blocks = SOME bb`
       (mp_tac o MATCH_MP frag_observer_lookup_cases) >>
     disch_then (DISJ_CASES_THEN2
       (fn th => strip_assume_tac th >>
         `?tail. original.bb_instructions = sbb.cs_current_insts ++ tail` by
           (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
            metis_tac[optionTheory.SOME_11]) >>
         qpat_x_assum `!xs ys sid left right k. _`
           (qspecl_then [`sbb.cs_current_insts`, `tail`, `oid`, `bb`,
             `original`, `a.vs_inst_idx`] mp_tac) >> simp[])
       (fn th => strip_assume_tac th >>
         `original = bb` by
           (fs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >> simp[]))) >>
  gvs[gas_path_edge_def, step_inst_non_invoke, exit_result_def,
      mem_safe_step_non_invoke] >>
  simp[gas_path_mem_edge_def, mem_safe_step_non_invoke, step_inst_non_invoke] >>
  metis_tac[]
QED

Resume mem_cont_sim_gas_path_mem[prefix_forward]:
  rpt (pop_assum kall_tac) >> rpt gen_tac >>
  simp[revert_forward_at_def, revert_forward_pair_def,
       get_instruction_def, EL_APPEND_EQN, mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  `j < LENGTH xs` by
    (Cases_on `j < LENGTH xs` >> simp[] >>
     `j = LENGTH xs` by decide_tac >>
     gvs[EL_APPEND_EQN, mk_inst_def]) >>
  `k < LENGTH xs` by
    (Cases_on `k < LENGTH xs` >> simp[] >>
     `k = LENGTH xs` by decide_tac >> gvs[EL_APPEND_EQN, mk_inst_def]) >>
  `k - LENGTH xs = 0 /\ j - LENGTH xs = 0` by decide_tac >>
  `j < LENGTH ys + LENGTH xs /\ k < LENGTH ys + LENGTH xs` by decide_tac >>
  qexists_tac `j` >>
  qpat_assum `k - LENGTH xs = 0` (fn isub =>
  qpat_assum `j - LENGTH xs = 0` (fn jsub =>
    fs[revert_forward_pair_def, get_instruction_def, EL_APPEND_EQN,
       TAKE_APPEND, DROP_APPEND, LENGTH_DROP, isub, jsub] >>
    metis_tac[DECIDE ``!x y z. x < y /\ y < z ==> x < z + 1``]))
QED

Finalise mem_cont_sim_gas_path_mem
