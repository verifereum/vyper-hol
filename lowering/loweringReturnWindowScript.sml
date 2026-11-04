(* Actual-site setup for the ABI return terminal. *)
Theory loweringReturnWindow
Ancestors
  externalReturnWindowResource abiEncoderWindowContract abiEncoderWindowRun
  abiEncoderPrimitiveEffect abiDecoderLoop abiEncoderRegisteredEffect
  loweringHalt fragExec context emitHelper compileEnv exprLoweringProps abiEncoderProps
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst venomMemDefs
  instIdxIndep words list rich_list finite_map pred_set arithmetic

Theorem return_buffer_alloca_member:
  compile_alloc_buffer msz st = (buf,sa) /\ fn_has_code st sa func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[fn_has_code_def] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
    [STRING #"%" (toString st.cs_next_var)]) bb.bb_instructions` by
    gvs[IS_PREFIX_APPEND] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem compile_alloc_buffer_window_setup:
  compile_alloc_buffer msz st = (buf,sa) /\ fn_has_code st sa func /\
  fn_has_code sa se func /\ fn_inst_ids_distinct func /\
  sa.cs_next_id <= se.cs_next_id /\ abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand op s = SOME (n2w sb) /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  alloca_inv s /\ alloca_room ctx func s /\
  sb + cap <= s.vs_alloca_next /\ LENGTH (enc at av) <= msz /\
  msz < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = msz /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids sa se /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t d. step_inst_base
    (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)]
      [STRING #"%" (toString st.cs_next_var)]) s = OK t /\
    abi_encoder_window_pre ctx func sa se buf.buf_operand op ei at av sb cap d
      (t with vs_inst_idx := LENGTH sa.cs_current_insts) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >> drule_all return_buffer_alloca_member >> disch_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w msz)] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp_tac (srw_ss()) [Abbr `inst`, mk_inst_def] >>
  `w2n (n2w msz : bytes32) = msz` by simp[] >>
  `op <> Var (STRING #"%" (toString st.cs_next_var))` by metis_tac[] >>
  `!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids sa se ==> i.inst_id <> inst.inst_id` by
    (simp_tac std_ss [frag_ids_def, IN_GSPEC_IFF] >> rpt strip_tac >>
     decide_tac) >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n (n2w msz : bytes32) /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)`
    by metis_tac[] >>
  `LENGTH (enc at av) <= w2n (n2w msz : bytes32)` by metis_tac[] >>
  drule_all return_window_allocate_entry_resources >> strip_tac >>
  qexistsl_tac [`t`, `d`] >> conj_tac
  >- (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `inst`, step_inst_base_def,
        eval_operands_def, eval_operand_def, mk_inst_def]) >>
  reverse conj_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (irule abi_encoder_inst_idx_alloca_inv >> first_assum ACCEPT_TAC) >>
  `alloca_room ctx func (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (irule alloca_room_fields >> qexists_tac `t` >>
     simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = _ ==> _` kall_tac >>
  qpat_x_assum `!i b sz. _ /\ _ /\ _ /\ FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  qpat_x_assum `!b sz. FLOOKUP s.vs_allocas inst.inst_id = _ ==> _` kall_tac >>
  qpat_x_assum `!id p sz. _ ==> FLOOKUP t.vs_allocas _ = _` kall_tac >>
  qpat_x_assum `!id. id <> inst.inst_id ==> _` kall_tac >>
  qpat_x_assum `!x. x <> _ ==> lookup_var x t = _` kall_tac >>
  qpat_x_assum `!i. _ /\ _ /\ _ ==> i.inst_id <> inst.inst_id` kall_tac >>
  simp_tac (srw_ss()) [abi_encoder_window_pre_def, eval_op_inst_idx] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_assum `buf.buf_operand = _` (rewrite_tac o single) >>
      simp_tac (srw_ss()) [eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `buf.buf_operand = _` (rewrite_tac o single) >>
      simp_tac (srw_ss()) [] >> metis_tac[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- decide_tac >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

(* Continuation simulation is enough at the terminal RETURN: no extraction
   of an intermediate encoder execution prefix is necessary. *)
Theorem compile_abi_encode_return_window_run:
  compile_abi_encode_to_buf (Var name) op ei sa = (len,se) /\
  emit_inst RETURN [Var name;len] [] se = (x,sf) /\
  fn_has_code sa se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  abi_encoder_window_pre ctx func sa se (Var name) op ei at av sb cap d s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  LENGTH (enc at av) < dimword (:256) ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    ss.vs_returndata = enc at av /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
  drule_all compile_abi_encode_to_buf_window_run >> strip_tac >>
  `eval_operand (Var name) actual = SOME (n2w d)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `lookup_block actual.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb actual.vs_inst_idx =
     SOME (mk_inst se.cs_next_id RETURN [Var name;len] [])` by simp[] >>
  `d < dimword (:256)` by
    (qpat_x_assum `alloca_room ctx func s` mp_tac >>
     simp_tac bool_ss [alloca_room_def] >> strip_tac >> decide_tac) >>
  `mem_bytes_at (w2n (n2w d : bytes32)) (LENGTH (enc at av))
     actual.vs_memory = enc at av` by simp[] >>
  drule_all (SRULE [] return_buffer_run) >>
  disch_then (qspecl_then [`0`, `ctx`] mp_tac) >> strip_tac >>
  qpat_x_assum `abi_decode_sim _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_sim_def] >>
    disch_then (qspec_then `0` mp_tac) >> asm_simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `steps` assume_tac) >>
  qexistsl_tac [`steps`, `ss`] >>
  gvs[abi_encoder_registered_effect_def]
QED

Theorem compile_alloc_encode_return_window_run:
  compile_alloc_buffer msz st = (buf,sa) /\
  compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se) /\
  emit_inst RETURN [buf.buf_operand;len] [] se = (x,sf) /\
  fn_has_code st sa func /\ fn_has_code sa se func /\
  fn_has_code se sf func /\ fn_inst_ids_distinct func /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand op s = SOME (n2w sb) /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  alloca_inv s /\ alloca_room ctx func s /\
  sb + cap <= s.vs_alloca_next /\ LENGTH (enc at av) <= msz /\
  msz < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = msz /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids sa se /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    ss.vs_returndata = enc at av /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  drule compile_abi_encode_to_buf_next_id >> strip_tac >>
  drule_all compile_alloc_buffer_window_setup >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb` by
    (`step_inst 0 ctx (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)]
        [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_preserves_control_flow >>
     simp_tac (srw_ss()) [mk_inst_def, is_terminator_def] >> strip_tac >>
     drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  `LENGTH (enc at av) < dimword (:256)` by decide_tac >>
  `~(t with vs_inst_idx := LENGTH sa.cs_current_insts).vs_halted /\
   (t with vs_inst_idx := LENGTH sa.cs_current_insts).vs_current_bb = sa.cs_current_bb /\
   (t with vs_inst_idx := LENGTH sa.cs_current_insts).vs_inst_idx =
      LENGTH sa.cs_current_insts` by
    (simp_tac (srw_ss()) [] >> asm_rewrite_tac[]) >>
  qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
  drule_all compile_abi_encode_return_window_run >> strip_tac >>
  qpat_assum `fn_has_code st sa func`
    (mp_then Any mp_tac fn_has_code_same_block) >>
  qpat_assum `sa.cs_current_insts = _` (rewrite_tac o single) >>
  qpat_assum `sa.cs_current_bb = _` (rewrite_tac o single) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)]
       [STRING #"%" (toString st.cs_next_var)])` by
    (qpat_assum `s.vs_current_bb = _` (rewrite_tac o single) >>
     qpat_assum `s.vs_inst_idx = _` (rewrite_tac o single) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule run_from_step >>
  simp_tac (srw_ss()) [mk_inst_def, is_terminator_def] >>
  disch_then drule >> disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  simp_tac (srw_ss()) [is_terminator_def] >>
  disch_then drule >> disch_tac >>
  qexistsl_tac [`fuel`, `ss`] >>
  conj_tac
  >- (qpat_x_assum `run_from fuel ctx func s = _` SUBST1_TAC >>
      qpat_assum `s.vs_inst_idx = _` (rewrite_tac o single) >>
      qpat_x_assum `run_from fuel ctx func (t with vs_inst_idx := _) = _` mp_tac >>
      qpat_assum `sa.cs_current_insts = _` (rewrite_tac o single) >>
      simp_tac (srw_ss()) [ADD1]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `ss.vs_accounts = _` (rewrite_tac o single) >>
  qpat_assum `ss.vs_transient = _` (rewrite_tac o single) >>
  qpat_assum `ss.vs_logs = _` (rewrite_tac o single) >>
  qpat_assum `ss.vs_requests = _` (rewrite_tac o single) >>
  qpat_assum `ss.vs_pending_deletions = _` (rewrite_tac o single) >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The remaining optional-unlock resource fact; other unchanged fields and
   alloca_inv are already exported by optional_unlock_state. *)
Theorem optional_unlock_alloca_room:
  u = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
        vs_inst_idx := k ==>
  (alloca_room ctx func u <=> alloca_room ctx func s)
Proof
  strip_tac >> drule optional_unlock_state >> strip_tac >>
  eq_tac >> strip_tac >> irule alloca_room_fields
  >- (qexists_tac `u` >> simp[]) >>
  qexists_tac `s` >> simp[]
QED

Theorem external_return_window_code[local]:
  compile_external_return (SOME op) F F ei msz nr nkey ut iv st = (x,sf) /\
  (nr /\ ~iv ==> ut) /\ fn_has_code st sf func ==>
  ?st1 buf sa len se.
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      st = ((),st1) /\
    compile_external_return (SOME op) F F ei msz F nkey ut iv st1 = (x,sf) /\
    st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
    st1.cs_current_bb = st.cs_current_bb /\
    compile_alloc_buffer msz st1 = (buf,sa) /\
    compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se) /\
    emit_inst RETURN [buf.buf_operand;len] [] se = (x,sf) /\
    fn_has_code st st1 func /\ fn_has_code st1 sa func /\
    fn_has_code sa se func /\ fn_has_code se sf func
Proof
  strip_tac >> drule compile_external_return_unlock >> strip_tac >>
  drule_all optional_unlock_code >> disch_tac >>
  `st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
   st1.cs_current_bb = st.cs_current_bb /\ cs_extends st st1` by
    (qpat_x_assum `st1 = _` SUBST1_TAC >> rw[] >>
     irule cs_extends_same_block >> simp[]) >>
  qpat_x_assum `st1 = _` kall_tac >>
  qpat_assum `compile_external_return _ _ _ _ _ F _ _ _ _ = _`
    (mp_then Any mp_tac compile_external_return_abi_parts) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se)` >>
  drule compile_alloc_buffer_extends >> disch_tac >>
  drule compile_abi_encode_to_buf_extends >> disch_tac >>
  drule emit_inst_metadata >> strip_tac >>
  `cs_extends st1 se /\ cs_extends st1 sf /\ cs_extends st sf` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code st st1 func /\ fn_has_code st1 sf func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  `fn_has_code st1 sa func /\ fn_has_code sa sf func` by
    (irule fn_has_code_split >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa se func /\ fn_has_code se sf func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  qexistsl_tac [`st1`, `buf`, `sa`, `len`, `se`] >>
  asm_rewrite_tac[] >> Cases_on `x` >> simp_tac (srw_ss()) []
QED

Theorem optional_unlock_sim[local]:
  (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
    st = ((),st1) /\ (nr /\ ~iv ==> ut) /\ fn_has_code st st1 func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func s
    ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
      vs_inst_idx := LENGTH st1.cs_current_insts)
Proof
  strip_tac >> drule_all optional_unlock_code >> disch_tac >>
  Cases_on `nr /\ ~iv`
  >- (gvs[] >> drule fn_has_code_same_block >> simp[] >> strip_tac >>
      `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx =
         SOME (mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] [])` by simp[] >>
      `step_inst_base (mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []) s =
         OK (tstore (n2w nkey) 0w s)` by
        simp_tac (srw_ss()) [step_inst_base_def, mk_inst_def,
          exec_write2_def, eval_operand_def] >>
      `!fuel. run_from fuel ctx func s =
        run_from fuel ctx func (tstore (n2w nkey) 0w s with
          vs_inst_idx := SUC s.vs_inst_idx)` by
        (gen_tac >> irule run_from_step >>
         qexistsl_tac [`bb`, `mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []`] >>
         simp[mk_inst_def, is_terminator_def]) >>
      simp_tac bool_ss [abi_decode_sim_def] >> rpt strip_tac >>
      qexists_tac `fuel` >> simp[ADD1]) >>
  gvs[] >>
  `s with vs_inst_idx := LENGTH st.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  asm_rewrite_tac[abi_decode_sim_refl]
QED

Theorem optional_unlock_control[local]:
  u = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with vs_inst_idx := k /\
  ~s.vs_halted /\ s.vs_current_bb = lbl ==>
  ~u.vs_halted /\ u.vs_current_bb = lbl /\ u.vs_inst_idx = k
Proof
  strip_tac >> Cases_on `nr /\ ~iv` >> gvs[tstore_def]
QED

Theorem compile_external_return_window_unlock_run:
  compile_external_return (SOME op) F F ei msz nr nkey ut iv st = (x,sf) /\
  (nr /\ ~iv ==> ut) /\ fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand op s = SOME (n2w sb) /\ alloca_inv s /\ alloca_room ctx func s /\
  sb + cap <= s.vs_alloca_next /\ LENGTH (enc at av) <= msz /\ msz < dimword (:256) /\
  (!st1 buf sa len se.
    compile_external_return (SOME op) F F ei msz F nkey ut iv st1 = (x,sf) /\
    st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
    compile_alloc_buffer msz st1 = (buf,sa) /\
    compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se) /\
    emit_inst RETURN [buf.buf_operand;len] [] se = (x,sf) ==>
    (!b sz. FLOOKUP s.vs_allocas st1.cs_next_id = SOME (b,sz) ==>
      sz = msz /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids sa se /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz))) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    ss.vs_returndata = enc at av /\ ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient = (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
                      else s.vs_transient) /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >> drule_all external_return_window_code >> strip_tac >>
  qpat_x_assum `!st1 buf sa len se. _` (drule_all_then strip_assume_tac) >>
  drule_all optional_unlock_sim >> disch_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func s u` >>
  `u = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
     vs_inst_idx := LENGTH st1.cs_current_insts` by simp_tac (srw_ss()) [Abbr `u`] >>
  drule optional_unlock_alloca_room >> disch_tac >>
  drule optional_unlock_state >> strip_tac >>
  `(!y. op = Var y ==> not_fresh_at st1 y)` by
    (rpt strip_tac >>
     qpat_x_assum `!y. op = Var y ==> not_fresh_at st y` drule >>
     simp_tac bool_ss [not_fresh_at_def] >>
     qpat_assum `st1.cs_next_var = _` (rewrite_tac o single) >>
     simp_tac bool_ss []) >>
  `abi_encoder_window_input ei at av sb cap u.vs_memory /\
   eval_operand op u = SOME (n2w sb) /\ alloca_inv u /\ alloca_room ctx func u /\
   sb + cap <= u.vs_alloca_next /\
   (!b sz. FLOOKUP u.vs_allocas st1.cs_next_id = SOME (b,sz) ==>
     sz = msz /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids sa se /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz))` by
    (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all optional_unlock_control >> strip_tac >>
  `u.vs_current_bb = st1.cs_current_bb` by metis_tac[] >>
  qpat_x_assum `abi_encoder_window_input _ _ _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `eval_operand op s = _` kall_tac >>
  qpat_x_assum `alloca_inv s` kall_tac >>
  qpat_x_assum `alloca_room ctx func s` kall_tac >>
  qpat_x_assum `!b sz. FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  qpat_x_assum `!inst b sz. _ /\ _ /\ _ /\ FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  drule_all compile_alloc_encode_return_window_run >> strip_tac >>
  qpat_x_assum `!ctx. abi_decode_sim ctx func s u`
    (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [abi_decode_sim_def] >>
  disch_then (qspec_then `fuel` mp_tac) >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `steps` assume_tac) >>
  qexistsl_tac [`steps`, `ss`] >>
  asm_rewrite_tac []
QED
