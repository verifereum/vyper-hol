Theory dftPacketReturnObservation
Ancestors
  dftPacketCallFreshCaller dftPacketCommonOracle dftPacketSuccessorObservation
  dftGasFromListTraceDefs dftRunRel dftWf venomWf venomExecSemantics
  arithmetic rich_list list

(* A successful source cut is compared with the native cursor immediately
   after the return, not with the suspended caller before the INVOKE. *)
Theorem dft_packet_return_observation:
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((a,e,next.inst_id),tf,next,v) /\
  trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs /\
  be.vs_current_bb = bb.bb_label /\
  get_instruction bt v.vs_inst_idx = SOME next /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ dft_fn_rel sf tf /\
  MEM bb sf.fn_blocks /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\ bb_well_formed bt /\
  dft_remaining_inv sf bb xs be /\ be.vs_inst_idx = LENGTH ps /\
  q < LENGTH xs /\ SUC pn < LENGTH ys /\ EL q xs = next /\
  next = EL (SUC pn) ys /\ inv_memory_observation next.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  FOLDR (dft_exec_cons ((F':num)-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  FOLDR (dft_exec_cons (N-e) C8) OK (TAKE (SUC pn) ys) be = OK v /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks) /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
  trace_gas (trace_block a e ((F':num)-e) C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ks),FLAT kgss) ==>
  (!op. MEM op next.inst_operands ==> eval_operand op u = eval_operand op v) /\
  u.vs_initial_fmp = v.vs_initial_fmp
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `hbe <= SUC j` by decide_tac >>
  `lookup_block be.vs_current_bb tf.fn_blocks = SOME bt` by simp[] >>
  `obs = trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry))` by metis_tac[] >>
  drule_all_then assume_tac dft_packet_call_target_prefix_covered >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) (FLAT kgss)` by
    (qpat_assum `LIST_REL (LIST_REL _) (TAKE q ms) kgss` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[REWRITE_RULE [quotientTheory.FUN_REL] finite_setTheory.FLAT_relates]) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     pop_assum (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dft_packet_common_oracle >>
  `(EL (SUC pn) ys).inst_id = next.inst_id` by metis_tac[] >>
  drule_all_then ACCEPT_TAC dft_packet_successor_observation_agreement
QED
