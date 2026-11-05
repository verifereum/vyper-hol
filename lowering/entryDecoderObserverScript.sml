(* Endpoint observations from justified STOP continuations. *)
Theory entryDecoderObserver
Ancestors
  abiEncoderObserver abiDecoderLoop abiDecoderReentryPointer
  calldataFiniteTyped fragExecMem memSafeRun instMemFrontier unitTransformDefs
  codegenRel contextCodegenRel fragExec venomExecProofs
  venomExecSemantics venomState venomInst

Theorem decoder_observer_run_mono[local]:
  run_from n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
  run_from m ctx fn s = r
Proof
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[run_from_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `exec_block n ctx bb s` >>
  gvs[run_from_def] >>
  imp_res_tac (cj 2 fuel_mono) >>
  gvs[] >> Cases_on `v.vs_halted` >> gvs[] >>
  metis_tac[cj 3 fuel_mono]
QED

Theorem decoder_observer_terminal_unique[local]:
  run_from n ctx fn s = Halt a /\ run_from m ctx fn s = Halt b ==>
  a = b
Proof
  strip_tac >>
  `run_from (n + m) ctx fn s = Halt a` by
    (irule decoder_observer_run_mono >> simp[] >> qexists `n` >> simp[]) >>
  `run_from (n + m) ctx fn s = Halt b` by
    (irule decoder_observer_run_mono >> simp[] >> qexists `m` >> simp[]) >>
  gvs[]
QED

Theorem decoder_observer_stop_agreement:
  abi_decode_sim ctx fn s a /\ abi_decode_sim ctx fn s b /\
  lookup_block a.vs_current_bb fn.fn_blocks = SOME ba /\
  get_instruction ba a.vs_inst_idx = SOME (mk_inst ia STOP [] []) /\
  lookup_block b.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb b.vs_inst_idx = SOME (mk_inst ib STOP [] []) ==>
  stop_view a = stop_view b
Proof
  strip_tac >>
  `?n. run_from n ctx fn s = Halt (stop_view a)` by
    (metis_tac[abi_decode_sim_stop_run]) >>
  `?m. run_from m ctx fn s = Halt (stop_view b)` by
    (metis_tac[abi_decode_sim_stop_run]) >>
  metis_tac[decoder_observer_terminal_unique]
QED

Theorem decoder_observer_stop_extra_fields:
  stop_view a = stop_view b ==>
  a.vs_call_ctx = b.vs_call_ctx /\ a.vs_data_section = b.vs_data_section /\
  a.vs_outcomes = b.vs_outcomes /\ a.vs_fmp = b.vs_fmp
Proof
  simp[stop_view_def, halt_state_def, venom_state_component_equality]
QED

Theorem decoder_observer_halt_not_revert:
  run_from n ctx fn s = Halt a ==>
  !m z. run_from m ctx fn s <> Abort Revert_abort z
Proof
  rpt strip_tac >>
  `run_from (n + m) ctx fn s = Halt a` by
    (irule decoder_observer_run_mono >> simp[] >> qexists `n` >> simp[]) >>
  `run_from (n + m) ctx fn s = Abort Revert_abort z` by
    (irule decoder_observer_run_mono >> simp[] >> qexists `m` >> simp[]) >>
  gvs[]
QED

Theorem decoder_observer_word_source_stop:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecPrimWord clamp) st = ((),last) /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st bound src dst CALLDATALOAD (Lit 0w) sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st last fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH last.cs_current_insts) = SOME (mk_inst iid STOP [] []) ==>
  ?t fuel. val_in_memory tv v d t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx fn initial t /\
    run_from fuel ctx fn initial = Halt (stop_view t)
Proof
  strip_tac >>
  drule_all abi_decoder_primitive_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >>
  simp[] >> strip_tac >>
  `?fuel. run_from fuel ctx fn initial = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem decoder_observer_stop_safe:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid STOP [] []) ==>
  mem_safe_run 0 ctx fn s
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst iid STOP [] []) s = Halt (stop_view s)` by
    (simp[step_inst_non_invoke, stop_view_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  `mem_safe_step 0 ctx (mk_inst iid STOP [] []) s` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def] >>
  metis_tac[run_from_step_exit, exec_result_distinct]
QED

Theorem decoder_observer_owned_stop:
  abi_decode_sim ctx fn initial source /\
  lookup_block source.vs_current_bb fn.fn_blocks = SOME bs /\
  get_instruction bs source.vs_inst_idx = SOME (mk_inst is STOP [] []) /\
  lookup_block owned.vs_current_bb fn.fn_blocks = SOME bo /\
  get_instruction bo owned.vs_inst_idx = SOME (mk_inst io STOP [] []) /\
  (!fuel r. run_from fuel ctx fn owned = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn initial = r /\
      (mem_safe_run fuel ctx fn owned ==> mem_safe_run fuel' ctx fn initial)) ==>
  stop_view source = stop_view owned /\
  (!fuel. mem_safe_run fuel ctx fn initial)
Proof
  strip_tac >>
  `?n. run_from n ctx fn initial = Halt (stop_view source)` by
    metis_tac[abi_decode_sim_stop_run] >>
  `run_from 0 ctx fn owned = Halt (stop_view owned)` by
    metis_tac[run_from_stop_view] >>
  `mem_safe_run 0 ctx fn owned` by metis_tac[decoder_observer_stop_safe] >>
  qpat_x_assum `!fuel r. _` (qspecl_then [`0`, `Halt (stop_view owned)`] mp_tac) >>
  simp[] >> strip_tac >> conj_tac
  >- metis_tac[decoder_observer_terminal_unique] >>
  irule mem_safe_run_all_fuel >> qexists `fuel'` >> simp[]
QED

(* Bounded owned decoder application. The source endpoint can be supplied by
   decoder_observer_word_source_stop; STOP is code, not an assumed continuation. *)
Theorem decoder_observer_word_owned_agreement:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\ fn_has_code st last fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_sim ctx fn initial source /\
  source.vs_current_bb = last.cs_current_bb /\
  source.vs_inst_idx = LENGTH last.cs_current_insts /\
  lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH last.cs_current_insts) = SOME (mk_inst iid STOP [] []) ==>
  (?owned x. value_has_type tv x /\ val_wf tv x /\
    val_in_memory tv x d owned.vs_memory /\
    stop_view source = stop_view owned /\
    source.vs_memory = owned.vs_memory) /\
  (!fuel. mem_safe_run fuel ctx fn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?n. run_from n ctx fn initial = Halt (stop_view source)` by
    (irule abi_decode_sim_stop_run >> simp[] >> metis_tac[]) >>
  drule_all calldata_coherent_word_owned_run >> strip_tac
  >- metis_tac[decoder_observer_halt_not_revert] >>
  rename1 `val_in_memory tv x d owned.vs_memory` >>
  `stop_view source = stop_view owned /\
   (!fuel. mem_safe_run fuel ctx fn initial)` by
    (irule decoder_observer_owned_stop >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`bb`, `iid`] >> asm_rewrite_tac[]) >>
     conj_tac >- (qexistsl_tac [`bb`, `iid`] >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  drule stop_view_fields >> strip_tac >>
  conj_tac >- (qexistsl_tac [`owned`, `x`] >> simp[]) >> simp[]
QED
