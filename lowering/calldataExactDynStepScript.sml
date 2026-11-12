Theory calldataExactDynStep
Ancestors
  calldataDynOwned calldataSourceCorrespondence abiDecoderFrame
  fragExecMem abiDecoderContract arithmetic list words
  calldataDynStep venomExecSemantics venomState venomMemDefs
  abiDecoderReentryAddress abiDecoderExecution abiDecoderDynamicLoopSetup

(* The header and element-address setup cannot reject.  In particular this
   boundary retains the actual child pointer, rather than quantifying a
   value predicate independently of the child's input. *)
Theorem calldata_exact_header_entry:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st0 = (ops,middle) /\ fn_has_code st0 middle fn /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\
  eval_operand ip u = SOME p /\ eval_operand src u = SOME srcword /\
  eval_operand dst u = SOME (n2w d) /\ mload (w2n p) u = n2w j /\
  abi_decode_load CALLDATALOAD srcword u = n2w n /\
  j < n /\ n < dimword (:256) /\ w2n p+32 <= u.vs_alloca_next /\
  hiv <> hcv /\ src <> Var hiv /\
  abi_decoder_operand_live st0.cs_next_var src /\
  abi_decoder_operand_live st0.cs_next_var dst /\
  (!op. op = ip \/ op = src \/ op = dst \/
      abi_decoder_operand_live st0.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) ==>
  ?entry.
    ~entry.vs_halted /\ entry.vs_current_bb = middle.cs_current_bb /\
    entry.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) entry = SOME (n2w j) /\
    eval_operand (FST (SND ops)) entry = SOME
      (if dec_info_needs_offset di then n2w (w2n srcword+32) +
        abi_decode_load CALLDATALOAD (n2w (w2n srcword+32+j*abi_sz):bytes32) u
       else n2w (w2n srcword+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) entry = SOME (n2w (d+32+j*mem_sz)) /\
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\
    entry.vs_allocas = u.vs_allocas /\ entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live st0.cs_next_var op ==>
      eval_operand op entry = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn u))
Proof
  strip_tac >>
  qabbrev_tac `head = jump_to body_lbl
    (abi_decode_header_state hiv hcv hcmp hdone j n u)` >>
  `j <= n` by decide_tac >>
  `head = jump_to (if j<n then body_lbl else exit_lbl)
    (abi_decode_header_state hiv hcv hcmp hdone j n u)` by simp[Abbr `head`] >>
  `lookup_block (if j<n then body_lbl else exit_lbl) fn.fn_blocks = SOME body_bb` by simp[] >>
  drule_all calldata_header_owned_safe_transfer >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  `~head.vs_halted /\ head.vs_current_bb = st0.cs_current_bb /\
    head.vs_inst_idx = LENGTH st0.cs_current_insts` by
    simp[Abbr `head`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  `eval_operand ip head = SOME p /\
    eval_operand src head = SOME (n2w (w2n srcword)) /\
    eval_operand dst head = SOME (n2w d)` by metis_tac[n2w_w2n] >>
  `mload (w2n p) head = n2w j` by
    gvs[mload_def] >>
  `w2n p+32 <= head.vs_alloca_next` by simp[] >>
  drule_all calldata_element_setup_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `head` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [combinTheory.K_THM] >>
  disch_then (qx_choose_then `entry` strip_assume_tac) >>
  `!op. abi_decoder_operand_live st0.cs_next_var op ==>
    eval_operand op entry = eval_operand op u` by metis_tac[] >>
  qexists_tac `entry` >>
  gvs[abi_decoder_address_frame_def, abi_decode_load_def, abi_decode_source_def] >>
  rpt strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn head = _ /\ _`
    (qspec_then `fuel` mp_tac) >> asm_rewrite_tac[] >>
  strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn u = _ /\ _`
    (qspec_then `fuel'` mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
