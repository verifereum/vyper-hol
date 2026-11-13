(* A cut observer supplies both execution and memory checks of the same path. *)
Theory exprSimAbiGasBridgeMem
Ancestors
  exprSimAbiGasBridge memContinuationExit fragGasPathMem contextCodegenRel
  instMemFrontier fragExecMem abiEncoderObserver venomExecSemantics
  venomExecProofs venomState emitHelper venomInst memSafeRun exprLoweringProps
  compileEnv fragExec list rich_list fragGasPath gasCount codegenRel unitTransformDefs
  arithmetic simplifyCfgFrameRf

Theorem frag_observer_forward_prefix[local]:
  !xs ys sid left right k.
    left.bb_instructions = xs ++ [mk_inst sid STOP [] []] /\
    right.bb_instructions = xs ++ ys /\ revert_forward_at left k ==>
    revert_forward_at right k
Proof
  rpt gen_tac >>
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
         inst_dload_in_section_def,
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
    revert_forward_at right k` by metis_tac[frag_observer_forward_prefix] >>
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

Finalise mem_cont_sim_gas_path_mem

(* Memory checks do not inspect the two control fields changed by relabelling. *)
Theorem frag_relabel_mem_safe_step[local]:
  frag_relabel_state L entry u v /\ inst.inst_opcode <> INVOKE ==>
  (mem_safe_step fuel ctx inst u <=> mem_safe_step fuel ctx inst v)
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> gvs[] >>
  simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       dret_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, frag_eval_operand_control,
       frag_eval_operands_control]
QED

Theorem frag_relabel_forward_nop_prefix[local]:
  left.bb_instructions = MAP (\id. mk_inst id NOP [] []) names ++ tail /\
  right.bb_instructions = old ++ tail /\ LENGTH old = LENGTH names /\
  revert_forward_pair left k j ==> revert_forward_pair right k j
Proof
  strip_tac >>
      qpat_x_assum `revert_forward_pair _ _ _`
        (strip_assume_tac o REWRITE_RULE[revert_forward_pair_def]) >>
      `!n inst. get_instruction left n = SOME inst /\
         inst.inst_opcode <> NOP ==> LENGTH names <= n` by
        (rpt strip_tac >> spose_not_then assume_tac >>
         `n < LENGTH names` by decide_tac >>
         gvs[get_instruction_def, EL_APPEND_EQN, EL_MAP, mk_inst_def]) >>
      `LENGTH names <= k /\ LENGTH names <= j` by
        (conj_tac >> first_x_assum irule >>
         goal_assum (drule_at Any) >> simp[]) >>
      `!n. LENGTH names <= n ==>
        get_instruction right n = get_instruction left n` by
        (rpt strip_tac >>
         simp[get_instruction_def, EL_APPEND_EQN] >>
         `~(n < LENGTH names)` by decide_tac >> simp[]) >>
      `TAKE k left.bb_instructions =
          MAP (\id. mk_inst id NOP [] []) names ++ TAKE (k-LENGTH names) tail /\
       TAKE k right.bb_instructions = old ++ TAKE (k-LENGTH names) tail /\
       TAKE j left.bb_instructions =
          MAP (\id. mk_inst id NOP [] []) names ++ TAKE (j-LENGTH names) tail /\
       TAKE j right.bb_instructions = old ++ TAKE (j-LENGTH names) tail` by
        simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
      `DROP (SUC k) right.bb_instructions = DROP (SUC k) left.bb_instructions /\
       DROP (SUC j) right.bb_instructions = DROP (SUC j) left.bb_instructions` by
        simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
      `EVERY (\i. i.inst_opcode <> ASSIGN)
        (REVERSE (MAP (\id. mk_inst id NOP [] []) names))` by
        simp[EVERY_REVERSE, EVERY_MAP, mk_inst_def] >>
      simp[revert_forward_pair_def, REVERSE_APPEND] >>
      conj_tac >- (rpt strip_tac >> metis_tac[LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ]) >>
      rpt conj_tac >> irule scfg_same_after_assigns_replace >>
      goal_assum (drule_at Any) >> gvs[REVERSE_APPEND]
QED

Theorem frag_relabel_forward_at[local]:
  frag_relabel_context sa sb L ids fn /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  lookup_block (if lbl = L then sa.cs_current_bb else lbl) fn.fn_blocks = SOME original /\
  revert_forward_at bb k ==> revert_forward_at original k
Proof
  strip_tac >> fs[frag_relabel_context_def] >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `?tail. original.bb_instructions = sb.cs_current_insts ++ tail` by
        (fs[fn_has_code_def, IS_PREFIX_APPEND] >> metis_tac[optionTheory.SOME_11]) >>
      irule frag_observer_forward_prefix >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> qexists_tac `id` >> simp[]) >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >>
  fs[MEM_APPEND] >> gvs[]
  >- (`MEM bb (emitted_blocks sa sb)` by
        (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
           [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
         metis_tac[MEM_APPEND]) >>
      `bb.bb_label <> L` by (fs[MEM_MAP] >> metis_tac[]) >>
      `original = bb` by (fs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >>
      simp[]) >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  `original = LAST (emitted_blocks sa sb)` by
    (fs[fn_has_code_def] >> metis_tac[MEM_LAST_NOT_NIL, optionTheory.SOME_11]) >>
  gvs[] >>
  `?tail. (LAST (emitted_blocks sa sb)).bb_instructions = sa.cs_current_insts ++ tail` by
    metis_tac[IS_PREFIX_APPEND] >>
  `!a b. revert_forward_pair
     <|bb_label := L;
       bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++ tail|> a b ==>
     revert_forward_pair (LAST (emitted_blocks sa sb)) a b` by
    (rpt gen_tac >>
     mp_tac (Q.INST
       [`left` |-> `<|bb_label := L;
           bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++ tail|>`,
        `right` |-> `LAST (emitted_blocks sa sb)`, `names` |-> `ids`,
        `old` |-> `sa.cs_current_insts`, `tail` |-> `tail`,
        `k` |-> `a`, `j` |-> `b`] frag_relabel_forward_nop_prefix) >>
     simp[]) >>
  fs[revert_forward_at_def, DROP_LENGTH_APPEND] >>
  qexists_tac `j` >> metis_tac[]
QED

Theorem mem_cont_sim_stop_relabel_observer_path:
  !ctx sa sb Q fn s L ids id t.
    frag_relabel_context sa sb L ids fn /\
    (!u rd. Q u ==> Q(u with vs_returndata := rd)) /\
    (!u prev. Q u ==> Q(u with vs_prev_bb := prev)) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_cont_sim ctx (frag_relabel_observer sa sb L ids fn id)
      (s with vs_current_bb := L) t ==>
    ?u. gas_path_mem ctx fn s 0 (OK u) /\ Q u /\ ~u.vs_halted /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `frag_relabel_context _ _ _ _ _`
    (fn th => MAP_EVERY assume_tac
      (CONJUNCTS (REWRITE_RULE[frag_relabel_context_def] th))) >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `((s with vs_current_bb := L).vs_current_bb,
    (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t) /\
     mem_safe_run fuel ctx (frag_relabel_observer sa sb L ids fn id)
       (s with vs_current_bb := L)` by suspend "safe_stop" >>
  `!budget. mem_safe_run budget ctx (frag_relabel_observer sa sb L ids fn id)
       (s with vs_current_bb := L)` by
    (irule mem_safe_run_all_fuel >> qexists_tac `fuel` >> simp[]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `!ct observed cut a b. local_prefix ct observed cut a b ==>
    !saa sbb label names func oid initial.
    observed = frag_relabel_observer saa sbb label names func oid /\
    cut = frag_observer_cut sbb /\
    frag_relabel_context saa sbb label names func /\
    (a.vs_current_bb,a.vs_inst_idx) IN
      frag_observer_region (start_relabel label names saa) (start_swap saa label names sbb) /\
    frag_relabel_state label saa.cs_current_bb a initial /\
    (!budget. mem_safe_run budget ct observed a) ==>
    ?actual. gas_path_mem ct func initial 0 (OK actual) /\
       frag_relabel_state label saa.cs_current_bb b actual` by suspend "safe_prefix" >>
  `?v. gas_path_mem ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (qpat_x_assum `!ct observed cut a b. _`
      (qspecl_then [`ctx`, `frag_relabel_observer sa sb L ids fn id`,
        `frag_observer_cut sb`, `s with vs_current_bb := L`, `u`] mp_tac) >>
     simp[] >> disch_then (qspecl_then [`sa`, `sb`, `L`, `ids`, `fn`, `id`, `s`] mp_tac) >>
     gvs[start_relabel_def]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  qexists_tac `v` >> gvs[frag_observer_cut_def]
QED

Resume mem_cont_sim_stop_relabel_observer_path[safe_stop]:
  `step_inst 0 ctx (mk_inst id STOP [] []) t = Halt (stop_view t)` by
    (simp[step_inst_non_invoke, stop_view_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  `mem_safe_step 0 ctx (mk_inst id STOP [] []) t` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, mk_inst_def] >>
  qspecl_then [`0`, `ctx`, `frag_relabel_observer sa sb L ids fn id`, `t`,
    `<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
    `mk_inst id STOP [] []`, `Halt (stop_view t)`] mp_tac run_from_step_exit >>
  simp[frag_relabel_observer_cut, frag_observer_cut_instruction] >> strip_tac >>
  irule mem_cont_sim_exit_run >> simp[exit_result_def] >> metis_tac[]
QED

Resume mem_cont_sim_stop_relabel_observer_path[safe_prefix]:
  rpt (pop_assum kall_tac) >> ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `initial` >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >>
      drule frag_relabel_state_fields >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ct (frag_relabel_observer saa sbb label names func oid)
    (frag_observer_cut sbb) a middle` >>
  `!budget. mem_safe_run budget ct
    (frag_relabel_observer saa sbb label names func oid) middle` by suspend "next_safe" >>
  drule_all frag_relabel_step_edge >> strip_tac >>
  rename1 `gas_path_edge ct func initial 0 (OK successor)` >>
  `gas_path_mem_edge ct func initial 0 (OK successor)` by suspend "memory_edge" >>
  `?actual. gas_path_mem ct func successor 0 (OK actual) /\
      frag_relabel_state label saa.cs_current_bb b actual` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_region_closed_def, frag_relabel_region_closed]) >>
  qexists_tac `actual` >> simp[] >>
  metis_tac[cj 2 gas_path_mem_rules, ADD]
QED

Resume mem_cont_sim_stop_relabel_observer_path[next_safe]:
  qpat_x_assum `abi_observer_step _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  rename1 `step_inst 0 ct inst a = OK stepped` >>
  qx_gen_tac `budget`
  >- (`step_inst budget ct inst a = OK stepped` by
        metis_tac[step_inst_non_invoke] >>
      qspecl_then [`budget`, `ct`, `frag_relabel_observer saa sbb label names func oid`,
        `a`, `bb`, `inst`, `stepped`] mp_tac mem_safe_run_step >>
      simp[] >> metis_tac[]) >>
  `step_inst (SUC budget) ct inst a = OK stepped` by
    metis_tac[step_inst_non_invoke] >>
  `mem_safe_blocks (SUC budget) ct
      (frag_relabel_observer saa sbb label names func oid) stepped` by
    (irule mem_safe_run_terminator >> metis_tac[]) >>
  drule_all mem_safe_blocks_run >> metis_tac[]
QED

Resume mem_cont_sim_stop_relabel_observer_path[memory_edge]:
  qpat_assum `abi_observer_step _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  `a.vs_current_bb = label ==> LENGTH saa.cs_current_insts <= a.vs_inst_idx` by
    (fs[frag_relabel_context_def] >> metis_tac[frag_relabel_region_entry_bound]) >>
  `?original. lookup_block
      (if a.vs_current_bb = label then saa.cs_current_bb else a.vs_current_bb)
        func.fn_blocks = SOME original /\
      get_instruction original a.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `revert_forward_at bb a.vs_inst_idx \/ mem_safe_step 0 ct inst a` by
    (irule mem_safe_run_head >> metis_tac[]) >>
  `revert_forward_at original initial.vs_inst_idx \/
     mem_safe_step 0 ct inst initial` by
    (qpat_assum `frag_relabel_state label saa.cs_current_bb a initial`
       (strip_assume_tac o MATCH_MP frag_relabel_state_fields) >>
     Cases_on `mem_safe_step 0 ct inst a`
     >- metis_tac[frag_relabel_mem_safe_step] >>
     `revert_forward_at bb a.vs_inst_idx` by metis_tac[] >>
     disj1_tac >>
     mp_tac (Q.INST
       [`sa` |-> `saa`, `sb` |-> `sbb`, `L` |-> `label`, `ids` |-> `names`,
        `fn` |-> `func`, `lbl` |-> `a.vs_current_bb`, `bb` |-> `bb`,
        `original` |-> `original`, `k` |-> `a.vs_inst_idx`, `id` |-> `oid`]
       frag_relabel_forward_at) >> simp[]) >>
  qpat_assum `frag_relabel_state label saa.cs_current_bb a initial`
    (strip_assume_tac o MATCH_MP frag_relabel_state_fields) >>
  qpat_x_assum `gas_path_edge ct func initial 0 (OK successor)` mp_tac >>
  simp[gas_path_edge_def, gas_path_mem_edge_def] >>
  rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[mem_safe_step_non_invoke]
QED

Finalise mem_cont_sim_stop_relabel_observer_path

Theorem mem_cont_sim_gas_path_mem_relabel:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           mem_cont_sim ctx fn' (s with vs_current_bb := L) t) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
    fn_has_code sa sb fn /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `frag_relabel_context sa sb L ids fn` by simp[frag_relabel_context_def] >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all mem_cont_sim_stop_relabel_observer_path >> simp[]
QED
