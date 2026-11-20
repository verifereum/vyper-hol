Theory gasFocusPacketEntryCursor
Ancestors
  gasFocusDftEntryRow gasFocusDftEntryState gasFocusDftEntryOccurrence
  gasFocusInitialSingletonPacket gasFocusCfgEntryCursor
  o1DftStageSsa dftContractGas dftRunRel dftDefs dftFinitePacket
  dftGasFromListTraceDefs frameJointTrace frameJointTransition
  o1PassContract o1PassLift venomPassSchedule lowerDloadDefs
  venomWf venomState venomInst venomExecProofs finite_map list option relation

(* The singleton packet, native head and CFG cursor share the same C8 configuration. *)
Theorem focus_packet_entry_cursor:
  ctx_pass_stage rp (CFP_Simple VP_DFT) view C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_pre 7 C7 C8 /\ o1_ctx_shape C7 /\ o1_ctx_shape C8 /\ o1_ctx_shape C9 /\
  EVERY wf_ssa C7.ctx_functions /\ EVERY wf_ssa C8.ctx_functions ==>
  ?schedules. !base N nm sf lbl.
    code_layout_valid base /\ base.vs_vars = FEMPTY /\ ~base.vs_halted /\ 0 < N /\
    C7.ctx_entry = SOME nm /\ lookup_function nm C7.ctx_functions = SOME sf /\
    fn_entry_label sf = SOME lbl ==>
    ?bb bt ps xs ys rho f9 current rooted_eval.
      ?tf. tf = dft_fn sf /\
      ?E. E = base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
      ?inst. inst = HD bt.bb_instructions /\
      ?i9. i9 = HD (HD f9.fn_blocks).bb_instructions /\
      ?q80. q80 = JointConfig [] [] FEMPTY entry_taint tf inst E [] FEMPTY []
            [OriginInitial E; OriginObserve (OriginSnapshot tf [] FEMPTY FEMPTY inst E)] /\
      ?q9. q9 = JointConfig [] [] FEMPTY entry_taint f9 i9 E [] FEMPTY []
            [OriginInitial E; OriginObserve (OriginSnapshot f9 [] FEMPTY FEMPTY i9 E)] /\
      ?T. T = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 tf E /\
      ?body_entry. body_entry = (if phi_prefix_length bt.bb_instructions < LENGTH ps
                       then NONE else SOME (E,0)) /\
      ?ms. ms = (if IS_SOME body_entry then
                 MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs else []) /\
      ?es. es = (if IS_SOME body_entry then
                 MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) xs else []) /\
      ?ks. ks = (if IS_SOME body_entry then
                 MAP (\i. if i.inst_opcode = GAS then [([],1,i.inst_id)] else []) xs else []) /\
        C8.ctx_entry = SOME nm /\ lookup_function nm C8.ctx_functions = SOME tf /\
        fn_entry_label tf = SOME lbl /\ dft_fn_rel sf tf /\
        lookup_block lbl sf.fn_blocks = SOME bb /\ lookup_block lbl tf.fn_blocks = SOME bt /\
        bb.bb_label = lbl /\ bt.bb_label = lbl /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        joint_initial base C8 q80 /\ joint_trace base C8 q80 [] [] q80 /\
        dftGasFromListTraceDefs$trace_context N C8 base = T /\
        (?tail. T = (([],1,inst.inst_id),tf,inst,E)::tail) /\
        0 < LENGTH T /\ EL 0 T = (([],1,inst.inst_id),tf,inst,E) /\
        TAKE 0 T = [] /\ LENGTH (TAKE 0 T) = 0 /\
        dftGasFromListTraceDefs$trace_gas (TAKE 0 T) = [] /\
        dft_focus_packet_rel N C7 C8 sf tf E (0,[])
          (FEMPTY |+ ([],(sf,tf,0,E,[1],NONE,NONE)))
          (FEMPTY |+ (([],1),(bb,bt,ps,xs,ys,rho,E,0,body_entry,0,OK E,F,NONE)))
          FEMPTY (FEMPTY |+ (([],1),ms)) (FEMPTY |+ (([],1),es))
          (FEMPTY |+ (([],1),ks)) rooted_eval [] 1 q80 (FLAT ms) (FLAT es)
          E.vs_gas_readings /\
        C9.ctx_entry = SOME nm /\ lookup_function nm C9.ctx_functions = SOME f9 /\
        fn_entry_label f9 = SOME lbl /\ joint_initial base C9 q9 /\
        cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q80 q9
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) >>
  strip_tac >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) focus_cfg_entry_cursor) >>
  disch_then (qx_choose_then `schedules` (mk_asm "cursor")) >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  qexists `schedules` >> qx_genl_tac [`root`,`N`,`nm`,`sf`,`lbl`] >> strip_tac >>
  drule_all (SRULE [LET_THM] focus_dft_entry_row) >>
  strip_tac >>
  rename1 `lookup_block lbl sf.fn_blocks = SOME sb` >>
  rename1 `lookup_block lbl (dft_fn sf).fn_blocks = SOME tb` >>
  rename1 `sb.bb_instructions = prefix ++ src` >>
  rename1 `tb.bb_instructions = prefix ++ dst` >>
  rename1 `PERM schedule (COUNT_LIST (LENGTH src))` >>
  `lookup_function nm C8.ctx_functions = SOME (dft_fn sf)` by
    (drule dft_ctx_functions_map >> simp[lookup_function_map]) >>
  `dft_fn_rel sf (dft_fn sf)` by
    (drule dft_fn_rel_lookup_function >> disch_then (qspec_then `nm` mp_tac) >>
     simp[OPTREL_def]) >>
  `fn_entry_label (dft_fn sf) = SOME lbl` by metis_tac[dft_fn_rel_entry_label] >>
  `MEM sf C7.ctx_functions /\ MEM (dft_fn sf) C8.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  drule_all (Q.INST [`tf` |-> `dft_fn sf`] (SRULE [LET_THM] focus_dft_entry_state)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_phis E _ = OK E` >>
  `E.vs_prev_bb = NONE /\ E.vs_current_bb = lbl /\ E.vs_inst_idx = 0 /\
   E.vs_labels = root.vs_labels /\
   E with vs_inst_idx := phi_prefix_length tb.bb_instructions = E` by
    simp[Abbr `E`, venom_state_component_equality] >>
  qabbrev_tac `q80 = JointConfig [] [] FEMPTY entry_taint (dft_fn sf)
    (HD tb.bb_instructions) E [] FEMPTY []
    [OriginInitial E; OriginObserve (OriginSnapshot (dft_fn sf) [] FEMPTY FEMPTY
      (HD tb.bb_instructions) E)]` >>
  mp_tac (Q.INST [`root_base` |-> `root`, `sp` |-> `E`, `bt` |-> `tb`,
                  `inst` |-> `HD tb.bb_instructions`]
    (SRULE [LET_THM] focus_dft_entry_occurrence)) >>
  markerLib.REABBREV_TAC >>
  (impl_tac >- simp[IgnAsm `tb.bb_instructions = _`]) >>
  qpat_assum `E with vs_inst_idx := _ = E` (fn th => pure_rewrite_tac[th]) >>
  markerLib.REABBREV_TAC >> strip_tac >>
  asm_x "cursor" (qspecl_then [`root`, `q80`, `nm`, `dft_fn sf`, `lbl`] mp_tac) >>
  (impl_tac >- gvs[]) >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  markerLib.REABBREV_TAC >> strip_tac >>
  rename1 `lookup_function nm C9.ctx_functions = SOME f9` >>
  rename1 `cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q80 _` >>
  qexistsl [`sb`,`tb`,`prefix`,`src`,`dst`,`schedule`,`f9`,`current`] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> markerLib.REABBREV_TAC >>
  simp[] >>
  `fn_reachable sf E.vs_current_bb /\
   ctx_labels_bound C7 E.vs_labels /\ ctx_labels_bound C8 E.vs_labels /\
   get_instruction tb E.vs_inst_idx = SOME (HD tb.bb_instructions) /\
   E = E with vs_inst_idx := phi_prefix_length tb.bb_instructions` by
    metis_tac[] >>
  mp_tac (CONV_RULE (RAND_CONV (REPEATC Unwind.UNWIND_FORALL_CONV))
    (Q.SPECL [`N`, `C7`, `C8`, `sf`, `dft_fn sf`, `E`, `nm`, `lbl`,
              `sb`, `tb`, `prefix`, `src`, `dst`, `schedule`, `E`, `E`,
              `HD tb.bb_instructions`, `[]`, `FEMPTY`, `entry_taint`, `[]`,
              `FEMPTY`, `[]`, `[OriginInitial E; OriginObserve (OriginSnapshot
                (dft_fn sf) [] FEMPTY FEMPTY (HD tb.bb_instructions) E)]`]
       focus_initial_singleton_packet)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[Abbr `q80`] >> disch_then (irule_at Any)
QED
