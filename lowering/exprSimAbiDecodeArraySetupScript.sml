(* Reusable actual-site index allocation, independent of executing function. *)
Theory exprSimAbiDecodeArraySetup
Ancestors
  exprSimAbiDecodeArrayPrefix exprSimAbiDecodeSiteOwnership
  abiDecoderArrayLoopInit exprSimAbiDecodeArraySource fragExec
  abiDecoderSiteEffect abiDecoderBytestringOutcome abiDecoderWordOutcome
  abiDecoderReentryAddress actualDecoderSites abiDecoderDynarrayPrefix
  abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderGuards abiEncoder
  abiDecoderArrayHeader abiDecoderContract abiDecoderRange abiDecoderReentry
  valueEncoding
  abiDecoderIndexInit venomExecSemantics venomExecProofs venomMemProps
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomMemDefs venomState venomInst finite_map words list rich_list arithmetic

Theorem abi_decode_index_site_registers[local]:
  exec_alloca inst s (32w:bytes32) = OK t /\ inst.inst_outputs = [out] /\
  lookup_var out t = SOME w ==>
  t.vs_vars = s.vs_vars |+ (out,w) /\ t.vs_labels = s.vs_labels
Proof
  rw[exec_alloca_def] >>
  gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_site_other_ids[local]:
  exec_alloca inst s (32w:bytes32) = OK t ==>
  !id. id <> inst.inst_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  rw[exec_alloca_def] >> gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_site_insts[local]:
  abi_decode_index_init st = (ip,st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE [ip; Lit 0w] []]
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]
QED

Theorem abi_decode_index_site_origin[local]:
  exec_alloca inst s (32w:bytes32) = OK t /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME(p,32) ==>
  p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas inst.inst_id = SOME(p,32)
Proof
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  simp[exec_alloca_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_init_site_sequence:
  abi_decode_index_init st = (ip,st') /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME(n2w p) /\ mload p t = 0w /\
    fresh_vars_wrt limit_st t /\
    decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32} s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME(p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas st.cs_next_id = SOME(p,32)) /\
    p + 32 <= t.vs_alloca_next /\ p < dimword(:256) /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   MEM inst (fn_insts func)` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all decode_site_allocation >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> strip_tac >>
  rename1 `exec_alloca inst s 32w = OK allocated` >>
  rename1 `FLOOKUP allocated.vs_allocas inst.inst_id = SOME(p,32)` >>
  drule_all abi_decode_index_site_registers >> strip_tac >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `p < dimword(:256)` by
    (fs[decode_site_resources_def, alloca_room_def] >> decide_tac) >>
  drule abi_decode_index_site_insts >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (qpat_x_assum `emitted_insts _ _ = _` (fn th => rewrite_tac[th]) >>
     `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]) s (32w:bytes32) = OK allocated` by
       (qunabbrev_tac `inst` >> first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
     qpat_x_assum `exec_alloca (mk_inst _ _ _ _) _ _ = _`
       (fn th => rewrite_tac[SRULE [mk_inst_def] th]) >>
     simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w]) >>
  `decode_site_effect ctx func st.cs_next_var {} s allocated` by
    (simp_tac bool_ss [decode_site_effect_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt gen_tac >> PairCases_on `entry` >> strip_tac >>
       first_x_assum irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     conj_tac
     >- (simp_tac bool_ss [decode_static_frame_def] >>
         qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[venom_state_component_equality]) >>
     simp_tac bool_ss [decode_memory_frame_def] >> rpt strip_tac >>
     `allocated.vs_memory = s.vs_memory` by
       (qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     simp[]) >>
  `decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32}
     allocated (mstore p 0w allocated)` by
    (`mstore p 0w allocated =
        write_memory_with_expansion p (word_to_bytes (0w:bytes32) T) allocated` by
       simp[mstore_def, write_memory_with_expansion_def] >>
     pop_assum SUBST1_TAC >> irule decode_site_effect_write >>
     simp[]) >>
  `decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32}
     s (mstore p 0w allocated)` by
    (drule_all decode_site_effect_trans >> simp[]) >>
  `p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas inst.inst_id = SOME(p,32)` by
    (drule_all abi_decode_index_site_origin >> simp[]) >>
  drule abi_decode_index_site_other_ids >> strip_tac >>
  qexistsl [`mstore p 0w allocated`, `p`] >>
  simp[eval_operand_def, fresh_vars_wrt_mstore, mload_mstore_same,
       mstore_def, write_memory_with_expansion_def, Abbr `inst`, mk_inst_def] >>
  fs[mk_inst_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* Existing source windows may be below the allocation frontier, including
   when the scratch allocation was made on a previous loop entry. *)
Theorem abi_decode_index_slot_separation:
  (p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas site = SOME(p,32)) /\
  q+len <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas site = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) ==>
  venomMemDefs$regions_disjoint (q,len) (p,32)
Proof
  strip_tac >- simp[regions_disjoint_def] >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_index_slot_output:
  decode_site_resources ctx func s /\
  decode_site_effect ctx func next writes s t /\
  FLOOKUP s.vs_allocas output = SOME(d,outsz) /\ output <> site /\
  FLOOKUP t.vs_allocas site = SOME(p,32) /\ off+len <= outsz ==>
  venomMemDefs$regions_disjoint (d+off,len) (p,32)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas output = SOME(d,outsz)` by
    (drule_all decode_site_effect_allocation >> simp[]) >>
  `alloca_inv t` by fs[decode_site_effect_def, decode_site_resources_def] >>
  `venomMemDefs$regions_disjoint (d,outsz) (p,32)` by
    (irule allocaSiteResourceTheory.alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_index_slot_source:
  decode_site_effect ctx func next {a | p <= a /\ a < p+32} s t /\
  venomMemDefs$regions_disjoint (q,len) (p,32) ==>
  mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory
Proof
  strip_tac >> irule decode_site_effect_protected >>
  goal_assum (drule_at Any) >> qexists `{(q,len)}` >>
  simp[decode_protects_def, regions_disjoint_def] >> rpt strip_tac >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_array_setup_step_static:
  (abi_bytes_opcode inst.inst_opcode \/ inst.inst_opcode = MUL) /\
  step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  strip_tac >- (drule_all abi_bytes_step_static >> simp[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def] >> simp[venom_state_component_equality]
QED

Theorem abi_decode_array_setup_sequence_static:
  !insts s t.
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `v = s with <|vs_vars := v.vs_vars; vs_memory := v.vs_memory|>` by
    (irule abi_decode_array_setup_step_static >> qexists `h` >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> fs[venom_state_component_equality]
QED

Theorem abi_decode_array_prepare_opcodes[local]:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn abi_sz st = (addr,guard_st) /\
  abi_decode_array_header dst addr opc guard_st = (cnt,header_st) /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL)
    (emitted_insts st header_st)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
       compile_abi_dec_addr_def, abi_decode_count_guard_def,
       abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
       abi_decode_array_header_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def, COND_RATOR, COND_RAND, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decode_source_opcode_def,
      abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_decode_dynarray_prepare_site_outcome:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn abi_sz st = (addr,guard_st) /\
  abi_decode_array_header dst addr opc guard_st = (cnt,header_st) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  eval_operand dst s = SOME(n2w d) /\ d < dimword(:256) /\
  abi_decode_load opc (n2w (b+pos):bytes32) s = n2w n /\
  pos < dimword(:256) /\ h < dimword(:256) /\
  n < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_sz < dimword(:256)) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx func s ==>
  (n <= maxn /\ pos+32+n*abi_sz <= h /\
   ?t. run_inst_seq (emitted_insts st header_st) s = OK t /\
       eval_operand cnt t = SOME(n2w n) /\ mem_word_at d t.vs_memory = n2w n /\
       fresh_vars_wrt header_st t /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
       decode_site_effect ctx func next {a | d <= a /\ a < d+32} s t /\
       t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
       t.vs_halted = s.vs_halted /\ inst_extends st header_st) \/
  ((h < pos+32 \/ maxn < n \/ h < pos+32+n*abi_sz) /\
   ?t. run_inst_seq (emitted_insts st header_st) s = Abort Revert_abort t)
Proof
  strip_tac >> drule_all abi_decode_dynarray_prepare_outcome >>
  disch_then strip_assume_tac
  >- (disj1_tac >> simp[] >>
      drule_all abi_decode_array_prepare_opcodes >> strip_tac >>
      drule_all abi_decode_array_setup_sequence_static >> strip_tac >>
      `decode_static_frame s t` by
        fs[decode_static_frame_def, venom_state_component_equality] >>
      `t.vs_fmp = s.vs_fmp` by fs[venom_state_component_equality] >>
      `decode_site_resources ctx func t` by
        (irule decode_site_resources_fields >> qexists `s` >> simp[]) >>
      `decode_memory_frame {a | d <= a /\ a < d+32} s t` by
        (irule abi_word_frame_memory >> qexists `d` >> simp[]) >>
      simp[decode_site_effect_def]) >>
  disj2_tac >> simp[] >> goal_assum (drule_at Any)
QED

Theorem abi_decode_array_prepared_site_init:
  abi_decode_index_init header_st = (ip,loop_st) /\
  inst_extends st header_st /\ st.cs_next_var <= header_st.cs_next_var /\
  run_inst_seq (emitted_insts st header_st) s = OK prepared /\
  decode_site_effect ctx func st.cs_next_var writes s prepared /\
  fresh_vars_wrt header_st prepared /\
  eval_operand cnt prepared = SOME(n2w n) /\
  mem_word_at d prepared.vs_memory = n2w n /\
  FLOOKUP prepared.vs_allocas output = SOME(root,outsz) /\
  d = root+off /\ off+32 <= outsz /\ output <> header_st.cs_next_id /\
  q+len <= prepared.vs_alloca_next /\
  (!b sz. FLOOKUP prepared.vs_allocas header_st.cs_next_id = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  decode_site_resources ctx func prepared /\ fn_inst_ids_distinct func /\
  MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand ip t = SOME(n2w p) /\ eval_operand cnt t = SOME(n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt loop_st t /\
    decode_site_effect ctx func st.cs_next_var
      (writes UNION {a | p <= a /\ a < p+32}) s t /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(p,32) /\
    (!id. id <> header_st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP prepared.vs_allocas id) /\
    mem_bytes_at q len t.vs_memory = mem_bytes_at q len prepared.vs_memory /\
    venomMemDefs$regions_disjoint (root,outsz) (p,32) /\
    t.vs_halted = prepared.vs_halted /\ inst_extends st loop_st
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `fresh_vars_wrt loop_st prepared` by
    (irule fresh_vars_wrt_mono >> qexists `header_st` >> simp[GREATER_EQ]) >>
  drule abi_decode_index_init_site_sequence >>
  disch_then (qspecl_then [`prepared`, `loop_st`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `venomMemDefs$regions_disjoint (q,len) (p,32)` by
    (irule abi_decode_index_slot_separation >> goal_assum (drule_at Any) >> simp[]) >>
  `venomMemDefs$regions_disjoint (root,outsz) (p,32)` by
    (`venomMemDefs$regions_disjoint (root+0,outsz) (p,32)` suffices_by simp[] >>
     metis_tac[abi_decode_index_slot_output, LESS_EQ_REFL, ADD_CLAUSES]) >>
  `venomMemDefs$regions_disjoint (d,32) (p,32)` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 prepared.vs_memory` by
    (metis_tac[abi_decode_index_slot_source]) >>
  `mem_word_at d t.vs_memory = n2w n` by
    fs[mem_word_at_def, mem_bytes_at_def] >>
  `mem_bytes_at q len t.vs_memory = mem_bytes_at q len prepared.vs_memory` by
    (metis_tac[abi_decode_index_slot_source]) >>
  `abi_decoder_operand_live header_st.cs_next_var cnt` by
    (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand cnt t = SOME(n2w n)` by
    (drule_all decode_site_effect_live >> simp[]) >>
  `decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32} prepared t` by
    (irule decode_site_effect_threshold >> goal_assum (drule_at Any) >>
     fs[inst_extends_def]) >>
  `decode_site_effect ctx func st.cs_next_var
     (writes UNION {a | p <= a /\ a < p+32}) s t` by
    (drule_all decode_site_effect_trans >> simp[]) >>
  `run_inst_seq (emitted_insts st loop_st) s = OK t /\ inst_extends st loop_st` by
    (irule abi_decode_sequence_chain >> qexistsl [`prepared`, `header_st`] >> simp[]) >>
  qexistsl [`t`, `p`] >> simp[]
QED

Theorem abi_decode_array_setup_site_outcome:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr opc guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  eval_operand dst s = SOME(n2w d) /\ d < dimword(:256) /\
  abi_decode_load opc (n2w (b+pos):bytes32) s = n2w n /\
  n = w2n (mem_word_at (b+pos) s.vs_memory) /\
  bs = mem_bytes_at (b+pos) (h-pos) s.vs_memory /\
  pos < dimword(:256) /\ h < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_member_head_size at < dimword(:256)) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx func s /\
  fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas output = SOME(root,outsz) /\
  d = root+off /\ off+32 <= outsz /\ output <> header_st.cs_next_id /\
  q+len <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (q,len) (d,32) /\
  (!b sz. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) ==>
  (n <= maxn /\ pos+32+n*abi_member_head_size at <= h /\
   ?t p. run_inst_seq (emitted_insts st loop_st) s = OK t /\
     eval_operand ip t = SOME(n2w p) /\ eval_operand cnt t = SOME(n2w n) /\
     mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
     fresh_vars_wrt loop_st t /\
     decode_site_effect ctx func st.cs_next_var
       ({a | d <= a /\ a < d+32} UNION {a | p <= a /\ a < p+32}) s t /\
     FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
     mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory /\
     venomMemDefs$regions_disjoint (root,outsz) (p,32) /\
     t.vs_halted = s.vs_halted /\ inst_extends st loop_st) \/
  (?t. run_inst_seq (emitted_insts st loop_st) s = Abort Revert_abort t /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `st.cs_next_var <= header_st.cs_next_var` by decide_tac >>
  `n < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
  drule_all abi_decode_dynarray_prepare_site_outcome >>
  disch_then (qspec_then `st.cs_next_var` mp_tac) >>
  disch_then strip_assume_tac
  >- (disj1_tac >> simp[] >>
      `decode_site_resources ctx func t` by fs[decode_site_effect_def] >>
      `mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory` by
        (irule abi_decode_index_slot_source >> goal_assum (drule_at Any) >> simp[]) >>
      `FLOOKUP t.vs_allocas output = SOME(root,outsz)` by simp[] >>
      `q+len <= t.vs_alloca_next` by simp[] >>
      `!b sz. FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(b,sz) ==>
         venomMemDefs$regions_disjoint (q,len) (b,sz)` by simp[] >>
      drule_all abi_decode_array_prepared_site_init >>
      strip_tac >> qexistsl [`t'`, `p`] >> gvs[]) >>
  disj2_tac >>
  `~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v)` by
    (irule abi_decode_dynarray_suffix_guard_reject >>
     goal_assum (drule_at Any) >> qexists `n` >> simp[]) >>
  `inst_extends st header_st` by
    (irule inst_extends_trans >> qexists `guard_st` >> simp[]) >>
  drule_all run_inst_seq_abort_extends >> strip_tac >>
  qexists `t` >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_index_init_registered_instruction:
  abi_decode_index_init st = (ip,st') /\ fn_has_code st st' fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `MEM inst (emitted_insts st st')` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, Abbr `inst`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]) >>
  `MEM inst (fn_insts fn)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     gvs[emitted_insts_def, MEM_APPEND] >>
     metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  first_x_assum irule >> simp[Abbr `inst`, mk_inst_def]
QED
