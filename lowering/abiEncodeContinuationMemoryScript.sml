(* Observer-polymorphic continuation safety for GAS-free fragments. *)
Theory abiEncodeContinuationMemory
Ancestors
  exprSimAbiGasBridge memContinuation fragGasPathMem
  o1LowerDloadForwardInversion stepWriteFootprintForward fragExec
  abiEncoderObserver abiDecoderLoop memSafeRun fragExecMem
  venomExecSemantics venomState venomInst compileEnv list
  emitHelper emitHelperProps instMemFrontier contextCodegenRel unitTransformDefs codegenRel

Theorem halt_run_not_forward[local]:
  run_from fuel ctx fn s = Halt h /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ~revert_forward_at bb s.vs_inst_idx
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s <> Halt h /\
   (!u. exec_block fuel ctx bb s <> OK u)` by
    metis_tac[revert_forward_at_no_halt, revert_forward_at_no_normal] >>
  gvs[run_from_def, AllCaseEqs()]
QED

Theorem observer_step_safe[local]:
  abi_observer_step ctx fn cut s t /\
  (!fuel. mem_safe_run fuel ctx fn s) ==>
  !fuel. mem_safe_run fuel ctx fn t
Proof
  rw[abi_observer_step_def] >> gvs[step_inst_non_invoke]
  >- metis_tac[mem_safe_run_step, step_inst_non_invoke] >>
  `!fuel. mem_safe_blocks (SUC fuel) ctx fn middle` by
    metis_tac[mem_safe_run_terminator, step_inst_non_invoke] >>
  metis_tac[mem_safe_blocks_run]
QED

Theorem observer_step_memory_edge[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t /\
  (!fuel. mem_safe_run fuel ctx (frag_observer sa sb fn id) s) /\
  run_from k ctx (frag_observer sa sb fn id) s = Halt h ==>
  gas_path_mem_edge ctx fn s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `gas_path_edge ctx fn s 0 (OK t)` by
    (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  `!bb inst fuel. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst ==>
     mem_safe_step fuel ctx inst s` by
    (qpat_assum `abi_observer_step _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
     drule_all frag_observer_instruction_agrees >> strip_tac >>
     `~revert_forward_at bb s.vs_inst_idx` by
       (irule halt_run_not_forward >> metis_tac[]) >>
     rpt strip_tac >> gvs[] >>
     metis_tac[mem_safe_run_head]) >>
  gvs[fragGasPathTheory.gas_path_edge_def, gas_path_mem_edge_def] >>
  metis_tac[]
QED

Theorem observer_prefix_memory_path[local]:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id k h.
  observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (!fuel. mem_safe_run fuel ctx observed s) /\
  run_from k ctx observed t = Halt h ==>
  gas_path_mem ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_strongind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ctx _ _ s middle` >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) middle = Halt h` by
    (drule local_prefix_sim >> rewrite_tac[abi_decode_sim_def] >>
     disch_then (qspecl_then [`k`, `Halt h`] mp_tac) >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt h` by
    (drule abi_observer_step_sim >> rewrite_tac[abi_decode_sim_def] >>
     disch_then (qspecl_then [`fuel`, `Halt h`] mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx fn s 0 (OK middle)` by
    (irule observer_step_memory_edge >> metis_tac[]) >>
  `gas_path_mem ctx fn middle 0 (OK t)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_step_safe, observer_region_closed_def,
               frag_observer_region_closed]) >>
  metis_tac[cj 2 gas_path_mem_rules, arithmeticTheory.ADD]
QED

Theorem stop_run_memory[local]:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  run_from 0 ctx fn t = Halt (stop_view t) /\ mem_safe_run 0 ctx fn t
Proof
  strip_tac >> conj_tac >- metis_tac[run_from_stop_view] >>
  simp[mem_safe_run_def, Once mem_safe_block_def, mem_safe_blocks_def,
       step_inst_non_invoke,
       step_inst_base_opcode_eqs, mk_inst_def,
       mem_safe_step_non_invoke, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  Cases_on `exec_block 0 ctx bb t` >> simp[]
QED

Theorem continuation_stop_memory[local]:
  mem_cont_sim ctx fn s t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  (?fuel. run_from fuel ctx fn s = Halt (stop_view t)) /\
  (!fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >> drule_all stop_run_memory >> strip_tac >>
  qpat_x_assum `mem_cont_sim _ _ _ _` (mp_tac o REWRITE_RULE[mem_cont_sim_def]) >>
  disch_then (qspecl_then [`0`, `Halt (stop_view t)`] mp_tac) >>
  simp[] >> strip_tac >> conj_tac >- metis_tac[] >>
  irule mem_safe_run_all_fuel >> qexists_tac `fuel'` >> simp[]
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
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
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
  `(?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)) /\
   (!fuel. mem_safe_run fuel ctx (frag_observer sa sb fn id) s)` by
    (irule continuation_stop_memory >> simp[] >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `run_from 0 ctx (frag_observer sa sb fn id) u = Halt (stop_view u)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     gvs[frag_observer_cut_def, frag_observer_cut_lookup,
         frag_observer_cut_instruction]) >>
  `gas_path_mem ctx fn s 0 (OK u)` by
    (drule observer_prefix_memory_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED
