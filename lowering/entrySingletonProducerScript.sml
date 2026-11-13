(* Canonical source-valued singleton registration producers. *)
Theory entrySingletonProducer
Ancestors
  entryRegistrationSingletonFrame entryCanonicalValidPre entryCanonicalReadyPre
  entrySourceMemoryConsumer entryFutureAllocation entryCompletedExitPhi
  entryZeroReservePre entryCanonicalMemberDecode entryDecoderStateFrame
  entryOwnedLiteralHistory abiAllocationHistory
  calldataSourceMemberFold calldataMemberResourceFrame abiDecoderAppend abiDecoderCode fragExec compileEnv
  abiDecoderContract abiValidMember words list arithmetic

Theorem entry_canonical_registration_address[local]:
  has_types (pre ++ at::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  4 + LENGTH bs < dimword (:256) /\
  off = 4 + SUM (MAP abi_member_head_size pre) /\
  (dyn /\ ~prim <=> is_dynamic at) /\
  ready.vs_call_ctx = initial.vs_call_ctx /\
  eval_operand src ready = SOME
    (if dyn /\ ~prim then n2w 4 + abi_decode_load CALLDATALOAD
      (n2w 4 + n2w (off-4):bytes32) initial
     else n2w 4 + n2w (off-4)) ==>
  eval_operand src ready = SOME (n2w (4 + abi_decode_member_offset at bs
    (SUM (MAP abi_member_head_size pre)))) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD ready) = bs
Proof
  strip_tac >>
  `abi_decode_source CALLDATALOAD ready = abi_decode_source CALLDATALOAD initial` by
    simp[abi_decode_source_def] >>
  drule_all entry_canonical_member_window >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (Cases_on `is_dynamic at` >>
    gvs[abi_decode_member_offset_def, GSYM word_add_n2w]) >>
  gvs[]
QED

Theorem entry_registration_singleton_source_endpoint:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
  (prim ==> ?c. info = DecPrimWord c) /\ fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var /\
  n = type_memory_bytes ce ty /\ n = type_memory_size tv /\
  info = type_to_abi_dec_info sf ce ty /\ abi_decoder_coherent ce env sf ty tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  at = vyper_to_abi_type env ty /\
  has_types (pre ++ at::post) (pvs ++ av::rest) /\ LENGTH pre = LENGTH pvs /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  4 + LENGTH bs < dimword (:256) /\ off = 4 + SUM (MAP abi_member_head_size pre) /\
  (dyn /\ ~prim <=> is_dynamic at) /\
  (!id. st.cs_next_id <= id ==> FLOOKUP initial.vs_allocas id = NONE) /\
  compile_register_positional_args cef remaining next_off final = (cer,registered) /\
  compile_guarded_body cer F nk ut iv stmts rt registered = ((),completed) /\
  ~block_is_terminated registered /\ fn_has_code final completed fn ==>
  ?dst src first ready p out scratch.
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst n) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
      ins.inst_id = st.cs_next_id) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info first = ((),final) /\
    fn_has_code first final fn /\ st.cs_next_id < first.cs_next_id /\
    st.cs_next_var <= first.cs_next_var /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand dst ready = SOME (n2w p) /\
    eval_operand src ready = SOME (n2w (4 + abi_decode_member_offset at bs
      (SUM (MAP abi_member_head_size pre)))) /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var dst /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (p,n) /\ p+n < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv ctx fn site ready /\
    initial.vs_alloca_next <= ready.vs_alloca_next /\
    ready.vs_memory = initial.vs_memory /\ ready.vs_call_ctx = initial.vs_call_ctx /\
    ready.vs_data_section = initial.vs_data_section /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn ready = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn ready ==> mem_safe_run fuel' ctx fn initial)) /\
    entry_decoder_obs initial ready /\ alloca_history fn ready /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) ready) /\
    fresh_vars_wrt limit_st ready /\
    ((!fuel. mem_safe_run fuel ctx fn ready) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    calldata_member_success ctx fn site limit_st first final p (type_memory_size tv)
      tv v ready out scratch /\
    entry_decoder_obs initial out /\ alloca_history fn out /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) out) /\
    (!id. final.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_registration_singleton_prefix_frame >> strip_tac >>
  drule_all entry_canonical_registration_address >> strip_tac >>
  qexistsl [`dst`,`src`,`first`,`ready`,`p`] >>
  simp[SF SFY_ss] >> suspend "endpoint"
QED

Resume entry_registration_singleton_source_endpoint[endpoint]:
  qpat_x_assum `compile_register_positional_args ce _ _ st = _` kall_tac >>
  qpat_x_assum `fn_has_code st final fn` kall_tac >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas _ = SOME entry ==> _` kall_tac >>
  qpat_x_assum `!fuel r. _` kall_tac >>
  qpat_x_assum `(!fuel. mem_safe_run _ _ _ ready) ==> _` kall_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` kall_tac >>
  qpat_x_assum `!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==> _` kall_tac >>
  qpat_x_assum `eval_operand src ready = SOME (if _ then _ else _)` kall_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand src ready = SOME (n2w (4+k))` >>
  qabbrev_tac `bytes = abi_decode_member_bytes at bs
    (DROP (SUM (MAP abi_member_head_size pre)) bs)` >>
  `?nv. abi_to_vyper env ty av = SOME nv /\
    abi_decoder_valid_pre ce env sf ty tv bytes nv first src dst CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 (4+k) p (p + type_memory_bytes ce ty) 0 ready` by
    (irule entry_canonical_valid_pre >>
      qpat_assum `n = type_memory_bytes ce ty`
        (fn th => asm_rewrite_tac[GSYM th]) >>
      conj_tac >- gvs[] >>
      conj_tac
      >- (qexistsl [`SUM (MAP abi_member_head_size pre)`,`at`,`bs`,
            `post`,`pre`,`pvs`,`rest`] >>
          simp_tac bool_ss [Abbr `k`, Abbr `bytes`] >> gvs[]) >>
      qexists_tac `v` >> asm_rewrite_tac[]) >>
  `calldata_member_own fn first.cs_next_id final.cs_next_id ready` by
    (irule entry_absent_member_ownership >> rpt strip_tac >>
      `id <> st.cs_next_id /\ st.cs_next_id <= id` by decide_tac >>
      metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all entry_decoder_completed_containing_exit_phi >>
  disch_then assume_tac >> suspend "child"
QED

Resume entry_registration_singleton_source_endpoint[child]:
  `?out scratch. calldata_member_success ctx fn site limit_st first final p
    (type_memory_size tv) tv nv ready out scratch /\
    entry_decoder_obs ready out /\ alloca_history fn out` by
    (irule entry_zero_reserve_child_endpoint >>
      asm_rewrite_tac[] >> conj_tac >- gvs[] >>
      conj_tac
      >- (qexistsl [`p`,`n`,`st.cs_next_id`] >> gvs[]) >>
      qexistsl [`bytes`,`ce`,`dst`,`env`,`4+k`,`sf`,`src`,`ty`] >>
      gvs[]) >>
  suspend "original"
QED

Resume entry_registration_singleton_source_endpoint[original]:
  `dec at bytes = av` by
    (drule_all entry_canonical_member_decode >>
      simp_tac bool_ss [Abbr `bytes`]) >>
  `vyper_to_abi env ty v = SOME (dec (vyper_to_abi_type env ty) bytes)` by
    metis_tac[] >>
  drule_all entry_member_success_original_value >> strip_tac >>
  `abi_alloca_history (fn_insts fn) initial ==>
    abi_alloca_history (fn_insts fn) out` by
    (strip_tac >> fs[calldata_member_success_def] >>
     drule_at (Pat `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _`)
       owned_member_literal_history >> simp[]) >>
  qexistsl [`out`,`scratch`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[entry_decoder_obs_trans] >>
  suspend "future"
QED

Resume entry_registration_singleton_source_endpoint[future]:
  `calldata_member_resource_frame ctx fn site limit_st first.cs_next_id
    final.cs_next_id first.cs_next_var p (type_memory_size tv) ready out scratch` by
    fs[calldata_member_success_def] >>
  drule calldata_member_resource_observations >> strip_tac >>
  `st.cs_next_id < final.cs_next_id` by
    (drule_all abi_decoder_to_buf_code >>
      simp[abi_decoder_code_def] >> rpt strip_tac >> decide_tac) >>
  rpt strip_tac >>
  `id <> st.cs_next_id /\ st.cs_next_id <= id` by decide_tac >>
  `FLOOKUP out.vs_allocas id = FLOOKUP ready.vs_allocas id` by metis_tac[] >>
  metis_tac[]
QED

Finalise entry_registration_singleton_source_endpoint

(* Source provenance (not a claim of transitive admission-freedom):
   entryDecodePropsScript.sml:381-391 admits compile_abi_clamp_structure.
   calldataWordLive uses it in calldata_word_accepted_live (238),
   calldata_word_rejected_live (285), and calldata_word_prefix_live (335).
   The first two feed calldataValidOwnedWord.valid_word_owned_sequence
   (111-115); that sequence and prefix_live feed
   entryDecoderAtomicEndpoint.entry_valid_word_owned_endpoint (60,84-88).
   entryDecoderMemberEndpoint.entry_member_word_contract (69-74) feeds
   entryAtomicMemberContracts.entry_base_child_contract / entry_flag_child_contract,
   then entryCoherentMemberContract.entry_coherent_child_contract, then
   entryZeroReservePre.entry_zero_reserve_child_endpoint, used above.
   Inspection of these proofs and calldataWordLeaf's opcode/prefix leaves
   found no locally introduced admission. The clean source-word execution
   uses abiDecoderClampedWord's constructive sequence, not the admitted
   structure fact. Independent aggregate/nonbulk/bulk and induction branches
   retain their strict audits in entryCoherentMemberContract. Here strict
   audits also protect the independent singleton producers and word leaves.
   Tag inclusion below is an additional guard, not the provenance argument. *)
val () =
  let val (shared_tags, _) = Tag.dest_tag
        (Thm.tag entryDecodePropsTheory.compile_abi_clamp_structure)
      fun audit (label, th, inherited) =
        let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
        in if null axioms andalso null (Thm.hyp th) andalso
              List.all (fn name => name = "DISK_THM" orelse
                (inherited andalso List.exists (fn a => a = name) shared_tags)) oracles
           then () else raise Fail ("entry singleton unexpected admission: " ^ label)
        end
  in List.app audit
    [("address",entry_canonical_registration_address,false),
     ("prefix",entry_registration_singleton_prefix_frame,false),
     ("valid pre",entry_canonical_valid_pre,false),
     ("phi",entry_decoder_completed_containing_exit_phi,false),
     ("word shape",abiDecoderClampedWordTheory.abi_decoder_clamped_word_shape,false),
     ("word copied",abiDecoderClampedWordTheory.abi_decoder_clamped_word_copied_window,false),
     ("word opcodes",calldataWordLeafTheory.calldata_word_opcodes,false),
     ("clamp repeat",calldataWordLiveTheory.calldata_clamp_repeat,false),
     ("clamp safe",calldataWordLeafTheory.calldata_clamp_instruction_safe,false),
     ("word accepted",calldataWordLiveTheory.calldata_word_accepted_live,true),
     ("word rejected",calldataWordLiveTheory.calldata_word_rejected_live,true),
     ("word prefix",calldataWordLiveTheory.calldata_word_prefix_live,true),
     ("word sequence",calldataValidOwnedWordTheory.valid_word_owned_sequence,true),
     ("word endpoint",entryDecoderAtomicEndpointTheory.entry_valid_word_owned_endpoint,true),
     ("word contract",entryDecoderMemberEndpointTheory.entry_member_word_contract,true),
     ("base",entryAtomicMemberContractsTheory.entry_base_child_contract,true),
     ("flag",entryAtomicMemberContractsTheory.entry_flag_child_contract,true),
     ("coherent",entryCoherentMemberContractTheory.entry_coherent_child_contract,true),
     ("child",entry_zero_reserve_child_endpoint,true),
     ("endpoint",entry_registration_singleton_source_endpoint,true)]
  end;
