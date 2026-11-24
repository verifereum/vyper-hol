(* Static confinement and opcode inventory for one saved ABI row. *)
Theory entryCreateExtRowCode
Ancestors
  entryIntCallStageBuffer createSizeEncodeCoreCode createSizeLocationCode
  createSizeTypedCopyCode createSizeCutOpens
  exprSimAbiEncodeObliviousSimulation exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge
  ctorCallFreeABIEncode deploySymSrcFrameABI
  deploySymSrcBlockFrame fragObserverCodeProps
  exprSimAbiEncodeObliviousLabels createSizeCutCode exprSimAbiDecodeSiteCoverage
  loweringShapeDefs exprLoweringProps exprLowering emitHelper fragExec
  venomInst compileEnv list rich_list pair

val row_safe = ``\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2``;

(* Erase only the old instructions on a proof copy of the compiler input.
   The encoder result and its emitted fragment are independent of them. *)
Theorem encode_to_buf_admin_ops[local]:
  compile_abi_encode_to_buf dst src info a = (n,b) ==>
  EVERY (\i. ^row_safe i.inst_opcode) (frag_code a b)
Proof
  strip_tac >> qabbrev_tac `a0 = a with cs_blocks := []` >>
  Cases_on `compile_abi_encode_to_buf dst src info a0` >>
  `a0 with cs_blocks := a0.cs_blocks ++ a.cs_blocks = a` by simp[Abbr `a0`] >>
  drule_then (qspec_then `a.cs_blocks` mp_tac)
    (REWRITE_RULE [deploy_blocks_frame_def] deploy_blocks_frame_abi_encode_to_buf) >>
  simp[] >> strip_tac >>
  `emitted_blocks a b = r.cs_blocks /\ emitted_blocks a0 r = r.cs_blocks` by
    (rpt conj_tac >> irule emitted_blocks_append >> simp[Abbr `a0`]) >>
  `frag_code a0 r = frag_code a b` by
    simp[frag_code_def, emitted_insts_def, Abbr `a0`] >>
  qabbrev_tac `ids = REPLICATE (LENGTH a0.cs_current_insts) (0:num)` >>
  `LENGTH ids = LENGTH a0.cs_current_insts` by simp[Abbr `ids`] >>
  `entry_action (compile_abi_encode_to_buf dst src info)` by
    simp[entry_action_encoder_mutual] >>
  `compile_abi_encode_to_buf dst src info (start_relabel "" ids a0) =
     (q,start_swap a0 "" ids r)` by
    metis_tac[entry_action_oblivious, frag_start_oblivious_def] >>
  `EVERY (\i. ^row_safe i.inst_opcode) (state_insts (start_relabel "" ids a0))` by
    simp[state_insts_def, all_blocks_def, start_relabel_def, Abbr `a0`, EVERY_MAP,
         EVERY_MEM, MEM_MAP, PULL_EXISTS, mk_inst_def] >>
  `EVERY (\i. ^row_safe i.inst_opcode) (state_insts (start_swap a0 "" ids r))` by
    (mp_tac (Q.INST [`P` |-> `^row_safe`] (cj 2 outcomes_free_abi_encode)) >>
     simp[DISJ_IMP_THM, FORALL_AND_THM] >>
     disch_then (qspecl_then [`dst`,`src`,`info`,`start_relabel "" ids a0`] mp_tac) >>
     fs[]) >>
  `frag_code (start_relabel "" ids a0) (start_swap a0 "" ids r) = frag_code a0 r` by
    (Cases_on `a0.cs_blocks = r.cs_blocks`
     >- (`a0.cs_blocks = [] /\ r.cs_blocks = []` by fs[Abbr `a0`] >>
         `entry_shape a0 r` by metis_tac[entry_action_run_shape] >>
         qpat_x_assum `entry_shape _ _` mp_tac >>
         simp[entry_shape_def] >> strip_tac >>
         `start_swap a0 "" ids r = r with <|cs_current_bb := "";
            cs_current_insts := MAP (\id. mk_inst id NOP [] []) ids ++ tail|>` by
           (irule start_swap_open >> metis_tac[]) >>
         simp[start_relabel_def, frag_code_def, emitted_blocks_def,
              emitted_insts_def, DROP_APPEND, Abbr `a0`]) >>
     irule start_relabel_frag_code >>
     metis_tac[create_encode_to_buf_cut_code, create_cut_code_def, SND]) >>
  fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]
QED

Theorem row_admin_join[local]:
  create_cut_code {} a b /\ create_cut_code {} b c /\
  EVERY (\i. ^row_safe i.inst_opcode) (frag_code a b) /\
  EVERY (\i. ^row_safe i.inst_opcode) (frag_code b c) ==>
  create_cut_code {} a c /\ EVERY (\i. ^row_safe i.inst_opcode) (frag_code a c)
Proof
  strip_tac >> conj_tac >- metis_tac[create_cut_code_join] >>
  `cs_extends a b /\ cs_extends b c` by fs[create_cut_code_def] >>
  drule_all abi_decode_frag_code_compose >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem row_admin_bind[local]:
  (create_cut_code {} a (SND (m a)) /\
   EVERY (\i. ^row_safe i.inst_opcode) (frag_code a (SND (m a)))) /\
  (!x b. create_cut_code {} b (SND (k x b)) /\
     EVERY (\i. ^row_safe i.inst_opcode) (frag_code b (SND (k x b)))) ==>
  create_cut_code {} a (SND (comp_bind m k a)) /\
  EVERY (\i. ^row_safe i.inst_opcode) (frag_code a (SND (comp_bind m k a)))
Proof
  Cases_on `m a` >> simp[comp_bind_def] >> metis_tac[row_admin_join]
QED

Theorem row_admin_atoms[local]:
  code_action ^row_safe m /\ create_cut_code {} a (SND (m a)) ==>
  create_cut_code {} a (SND (m a)) /\
  EVERY (\i. ^row_safe i.inst_opcode) (frag_code a (SND (m a)))
Proof
  strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `code_action _ m` mp_tac >>
  Cases_on `m a` >> simp[code_action_def] >>
  disch_then drule >> simp[code_step_def]
QED

Theorem row_admin_return[local,simp]:
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (frag_code a (SND (comp_return x a)))
Proof
  simp[comp_return_def, frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem extcall_pack_row_admin_code:
  compile_abi_encode_value_rows ce dst cursor off [(saved,ty)] a = ((),b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)
Proof
  `create_cut_code {} a
     (SND (compile_abi_encode_value_rows ce dst cursor off [(saved,ty)] a)) /\
   EVERY (\i. ^row_safe i.inst_opcode)
     (frag_code a (SND (compile_abi_encode_value_rows ce dst cursor off [(saved,ty)] a)))` suffices_by
    (strip_tac >> strip_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[compile_abi_encode_value_rows_def, LET_THM, comp_ignore_bind_def] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >> simp[] >>
  rpt (FIRST [match_mp_tac (BETA_RULE row_admin_bind) >> conj_tac,
              gen_tac,
              CHANGED_TAC (simp[]),
              (match_mp_tac (BETA_RULE row_admin_atoms) >>
                simp[code_action_emit_op, code_action_emit_void, saved_value_admin_actions,
                     create_cut_code_emit_op, create_cut_code_emit_void, create_cut_targets_def,
                     create_unwrap_cut_code, create_store_memory_cut_code] >> NO_TAC),
              rename1 `compile_abi_encode_to_buf d p info s` >>
                Cases_on `compile_abi_encode_to_buf d p info s` >>
                simp[] >> metis_tac[encode_to_buf_admin_ops,create_encode_to_buf_cut_code,SND]])
QED
