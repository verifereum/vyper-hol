Theory dftPacketCallFreshCaller
Ancestors
  dftPacketPreterminalAgreement dftPacketPreterminalRows dftPacketRetainedOracle
  dftGasFromListTraceNames dftContractGas dftWf dftGasInvCallerExtract
  dftRunRel venomWf list rich_list finite_map arithmetic

(* The entire visit-name distinctness required by the embedding lemma comes
   from context well-formedness, not from distinctness of GAS observations. *)
Theorem dft_packet_call_target_prefix_covered:
  !N C root_tf root_entry j hbe p d fn be inst s bt ps ys cnt obs.
  o1_ctx_shape C /\ MEM root_tf C.ctx_functions /\
  j < LENGTH (trace_blocks [] 0 N C root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C root_tf root_entry) =
    ((p,d,(HD ys).inst_id),fn,HD ys,be) /\
  EL j (trace_blocks [] 0 N C root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C root_tf root_entry)) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bt.bb_instructions = ps ++ ys /\ bb_well_formed bt /\
  be.vs_inst_idx = LENGTH ps /\ cnt < LENGTH ys /\
  FOLDR (dft_exec_cons (N-d) C) OK (TAKE cnt ys) be = OK s ==>
  EVERY (\kw. MEM kw obs)
    (trace_gas (trace_block p d (N-d) C fn
      (bt with bb_instructions := TAKE (LENGTH ps + cnt) bt.bb_instructions) be))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) C.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) root_tf.fn_blocks` by
    (gvs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C root_tf root_entry))` by
    (irule (cj 3 trace_names_distinct) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE cnt ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `cnt < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  qpat_x_assum `obs = _` SUBST1_TAC >>
  qpat_assum `be.vs_inst_idx = LENGTH ps`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule dft_packet_preterminal_prefix_observations >>
  simp[DROP_APPEND] >> metis_tac[]
QED

Theorem dft_packet_call_fresh_Q:
  !N C7 C8 root_tf root_entry j hbe p d sf fn bb bt ps xs ys sched
    be inst s cnt obs ms ks q.
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,(HD ys).inst_id),fn,HD ys,be) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bt.bb_instructions = ps ++ ys /\ bb_well_formed bt /\
  be.vs_inst_idx = LENGTH ps /\ cnt < LENGTH ys /\ inst = EL cnt ys /\
  FOLDR (dft_exec_cons (N-d) C8) OK (TAKE cnt ys) be = OK s /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ dft_fn_rel sf fn /\
  MEM bb sf.fn_blocks /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv sf bb xs be /\
  LIST_REL (\r y. r < LENGTH xs /\
    y.inst_id = (EL r xs).inst_id /\ from_block [EL r xs] y) sched ys /\
  (inv_memory_observation inst.inst_opcode ==>
    EL (EL cnt sched) xs = inst /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL cnt sched) xs) /\
    (!r. r < EL cnt sched /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE cnt sched))) /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks) /\
  (!r. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE r ks)) (FLAT (TAKE r ms))) /\
  (!F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE cnt sched)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
    !u. FOLDR (dft_exec_cons (F-d) C7) OK (TAKE k xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    trace_gas (trace_block p d (F-d) C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
      (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE k ks), FLAT kgss)) /\
  q = EL cnt sched /\ inst.inst_opcode = INVOKE ==>
  !F kgss tail u.
    N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    FOLDR (dft_exec_cons (F-d) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
    (!callee args. setup_callee callee args (u with vs_gas_readings := s.vs_gas_readings) =
      setup_callee callee args s)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\kw. MEM kw obs) (trace_gas (trace_block p d (N-d) C8 fn
    (bt with bb_instructions := TAKE (LENGTH ps + cnt) bt.bb_instructions) be))` by
    (irule dft_packet_call_target_prefix_covered >> metis_tac[]) >>
  `inv_memory_observation inst.inst_opcode` by simp[dftGasInvCrossingProbeTheory.inv_memory_observation_def] >>
  `q < LENGTH xs` by
    (qpat_assum `LIST_REL _ sched ys` mp_tac >>
     qpat_assum `cnt < LENGTH ys` mp_tac >>
     qpat_assum `q = EL cnt sched` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EL q xs = inst /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE cnt sched))` by metis_tac[] >>
  qx_gen_tac `fuel` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!f k kgss tail. _ ==> _`
    (qspecl_then [`fuel`, `q`, `kgss`, `tail`] mp_tac) >>
  impl_tac >- simp[] >> disch_then drule >> strip_tac >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (TAKE q ms)) (FLAT kgss)` by
    (qpat_assum `LIST_REL (LIST_REL _) (TAKE q ms) kgss` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[REWRITE_RULE [quotientTheory.FUN_REL] finite_setTheory.FLAT_relates]) >>
  `LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE q ks)) (FLAT (TAKE q ms))` by metis_tac[] >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `ALL_DISTINCT (_ ++ _)`
       (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  drule_all dftPacketCommonOracleTheory.dft_packet_lookup_overlap >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE cnt ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `cnt < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `xs = TAKE q xs ++ inst::DROP (SUC q) xs` by
    (qpat_assum `q < LENGTH xs` mp_tac >>
     qpat_assum `EL q xs = inst` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule TAKE_DROP_SUC >> simp[]) >>
  `ys = TAKE cnt ys ++ inst::DROP (SUC cnt) ys` by
    (qpat_assum `cnt < LENGTH ys` mp_tac >>
     qpat_assum `inst = EL cnt ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule TAKE_DROP_SUC >> simp[]) >>
  irule native_invoke_caller_observations >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK s`)) >>
  goal_assum (drule_at (Pat `be.vs_inst_idx = LENGTH _`)) >>
  `LENGTH (TAKE q xs) = q /\ LENGTH (TAKE cnt ys) = cnt` by simp[] >>
  qpat_assum `LENGTH (TAKE q xs) = q` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `LENGTH (TAKE cnt ys) = cnt` (fn th => pure_rewrite_tac[th]) >>
  goal_assum (drule_at (Pat `trace_gas _ = ZIP _`)) >>
  qexistsl [`bt`, `fn`] >>
  qrefinel [`_`, `bb.bb_label`, `_`, `_`, `_`] >>
  goal_assum (drule_at (Pat `EVERY _ (trace_gas _)`)) >>
  qexistsl [`DROP (SUC cnt) ys`, `DROP (SUC q) xs`, `inst`] >>
  qpat_assum `xs = TAKE q xs ++ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `ys = TAKE cnt ys ++ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `LENGTH (FLAT (TAKE q ks)) = LENGTH (FLAT kgss)` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
