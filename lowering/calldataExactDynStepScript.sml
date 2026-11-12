Theory calldataExactDynStep
Ancestors
  calldataDynOwned calldataSourceCorrespondence abiDecoderFrame calldataRegistrationExec
  fragExecMem abiDecoderContract arithmetic list words valueEncodingProofs valueEncodingProps
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

(* Post-child composition is independent of the source decoder.  In particular
   the value supplied by the child is not existentially re-selected here. *)
Theorem calldata_exact_owned_child_backedge:
  (Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  (H = \i s.
    ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
    i <= n /\ n <= maxn /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    eval_operand ip s = SOME (n2w p) /\ mload p s = n2w i /\
    mem_word_at d s.vs_memory = n2w n /\
    s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
    FLOOKUP s.vs_allocas header_id = SOME (p,32) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ Own lo hi s /\
    initial.vs_alloca_next <= s.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP s.vs_allocas id = SOME (q,k)) /\
    (!id. id < lo \/ hi <= id ==>
      FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live live op ==>
      eval_operand op s = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
      !q k. MEM (q,k) scratch ==> ?id. lo <= id /\ id < hi /\
        FLOOKUP s.vs_allocas id = SOME (q,k)) /\
  lo <= header_id /\ header_id < child_lo /\ child_lo <= child_hi /\ child_hi <= hi /\
  p < dimword (:256) /\ n < dimword (:256) /\ j < n /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (oid < lo \/ hi <= oid) /\ base_addr <= d /\
  d+(32+maxn*type_memory_size tv) <= base_addr+cap /\ H j u /\
  entry.vs_memory = u.vs_memory /\ entry.vs_allocas = u.vs_allocas /\
  entry.vs_alloca_next = u.vs_alloca_next /\
  entry.vs_call_ctx = u.vs_call_ctx /\ entry.vs_data_section = u.vs_data_section /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live live op ==>
    eval_operand op entry = eval_operand op u /\
    abi_decoder_operand_live child_live op /\ op <> Var nv) /\
  abi_decoder_operand_live child_live (Var biv) /\
  eval_operand (Var biv) entry = SOME (n2w j) /\ ip <> Var nv /\
  lookup_block child.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts back_id biv nv ip hdr /\
  child.vs_inst_idx = LENGTH prefix /\ ~child.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\ phi_prefix_length next_bb.bb_instructions = 0 /\
  val_wf tv x /\ val_in_memory tv x (d+32+j*type_memory_size tv) child.vs_memory /\
  Rel entry child /\
  child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
  alloca_inv child /\ alloca_frontier_inv ctx fn site child /\ Own child_lo child_hi child /\
  entry.vs_alloca_next <= child.vs_alloca_next /\
  (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  (!id. id < child_lo \/ child_hi <= id ==>
    FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
  (!op. abi_decoder_operand_live child_live op ==>
    eval_operand op child = eval_operand op entry) /\
  abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::new_scratch) entry child /\
  (!q k. MEM (q,k) new_scratch ==> ?id. child_lo <= id /\ id < child_hi /\
    FLOOKUP child.vs_allocas id = SOME (q,k)) ==>
  ?v. H (SUC j) v /\ val_wf tv x /\
    val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
    mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel entry v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `H j u` mp_tac >>
  qpat_assum `H = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >> strip_tac >>
  `p+32 <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas header_id = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `eval_operand (Var biv) child = SOME (n2w j) /\
    eval_operand ip child = SOME (n2w p) /\
    w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` by
    (simp[] >> metis_tac[]) >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) child))` >>
  `v = jump_to hdr
    (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) child))` by simp[Abbr `v`] >>
  drule_all calldata_backedge_owned_safe_transfer >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  `d+32+j*type_memory_size tv+type_memory_size tv <= d+(32+maxn*type_memory_size tv)` by
    ( `j+1 <= maxn` by decide_tac >>
      `(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
      qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `!a len. d <= a /\ a+len <= d+(32+maxn*type_memory_size tv) ==>
    mem_bytes_at a len v.vs_memory = mem_bytes_at a len child.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  suspend "compose"
QED
Resume calldata_exact_owned_child_backedge[compose]:
  `oid < child_lo \/ child_hi <= oid` by decide_tac >>
  `FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap)` by metis_tac[] >>
  `base_addr <= d /\ d+32+j*type_memory_size tv <= base_addr+cap` by decide_tac >>
  `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) entry.vs_memory` by
    (qpat_assum `abi_decode_footprint_frame _ entry child` mp_tac >>
     qpat_assum `alloca_inv child` mp_tac >>
     qpat_assum `!id. id < child_lo \/ child_hi <= id ==> _` mp_tac >>
     qpat_assum `oid < lo \/ hi <= oid` mp_tac >>
     qpat_assum `lo <= header_id` mp_tac >>
     qpat_assum `header_id < child_lo` mp_tac >>
     qpat_assum `child_hi <= hi` mp_tac >>
     qpat_assum `FLOOKUP entry.vs_allocas oid = _` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d+32+j*type_memory_size tv <= base_addr+cap` mp_tac >>
     qpat_assum `!q k. MEM (q,k) new_scratch ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt disch_tac >>
     `oid < child_lo \/ child_hi <= oid` by decide_tac >>
     drule calldata_child_preserves_contained_prefix >>
     disch_then irule >> asm_rewrite_tac[] >>
     qexistsl_tac [`base_addr`,`cap`,`child_hi`,`child_lo`,`oid`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory` by
    ( `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory` by
        (first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory` by
    (irule val_in_memory_mem_agree >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`type_memory_size tv`,`child.vs_memory`] >>
     simp[]) >>
  `Rel entry v` by suspend "transfer" >>
  qexists_tac `v` >> reverse conj_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `Own lo hi child` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Own lo hi u`, `Own child_lo child_hi child`,
        `lo <= header_id`, `header_id < child_lo`, `child_lo <= child_hi`,
        `child_hi <= hi`, `entry.vs_allocas = u.vs_allocas`,
        `entry.vs_alloca_next = u.vs_alloca_next`,
        `entry.vs_alloca_next <= child.vs_alloca_next`,
        `!id. id < child_lo \/ child_hi <= id ==> _`] >>
     qpat_assum `Own = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     qpat_x_assum `entry.vs_allocas = _` SUBST_ALL_TAC >>
     qpat_x_assum `entry.vs_alloca_next = _` SUBST_ALL_TAC >>
     rpt gen_tac >> strip_tac >>
     irule (GEN_ALL calldataDynOwnedTheory.calldata_owned_interval_replace) >>
     conj_tac >- (qexistsl [`child_lo`,`child_hi`,`hi`,`lo`,`u`] >>
       asm_rewrite_tac[] >> decide_tac) >>
     asm_rewrite_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
    mload p v = n2w (SUC j)` by
    (qpat_assum `v = _` mp_tac >> qpat_assum `p < dimword (:256)` mp_tac >>
     qpat_assum `~child.vs_halted` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt disch_tac >> qpat_x_assum `v = _` SUBST_ALL_TAC >>
     ntac 3 (conj_tac >- simp[jump_to_def, mstore_def, update_var_def]) >>
     simp[jump_to_def, GSYM mem_word_at_eq_mload, mstore_mem_word_at_same]) >>
  `abi_decode_footprint_frame [(p,32)] child v` by
    (qpat_assum `v = _` mp_tac >> qpat_assum `p < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     qpat_x_assum `v = _` SUBST_ALL_TAC >>
     irule (cj 1 abi_decode_backedge_observations) >> simp[]) >>
  qpat_x_assum `v = _` kall_tac >>
  qpat_x_assum `Abbrev (v = _)` kall_tac >>
  `Own lo hi v` by
    (qpat_assum `Own lo hi child` mp_tac >>
     qpat_assum `Own = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> asm_rewrite_tac[]) >>
  qpat_x_assum `Own = _` kall_tac >>
  `!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live live op ==>
    eval_operand op v = eval_operand op u` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!op. op = src \/ _ ==> _`,
        `!op. abi_decoder_operand_live child_live op ==> _`,
        `!op. op <> Var nv ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `mem_word_at d v.vs_memory = n2w n` by
    (qpat_assum `mem_bytes_at d _ v.vs_memory = mem_bytes_at d _ u.vs_memory` mp_tac >>
     qpat_assum `mem_word_at d u.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`,`32`] mp_tac) >>
     simp[] >> disch_tac >>
     qpat_x_assum `mem_word_at d u.vs_memory = _` mp_tac >>
     simp[abiStaticAggregatePropsTheory.mem_word_at_bytes]) >>
  qpat_assum `H = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  map_every (fn opq =>
    qpat_assum `!op. op = src \/ _ ==> eval_operand op v = _`
      (qspec_then opq mp_tac)) [`src`,`dst`,`ip`] >>
  simp[] >> rpt disch_tac >> asm_rewrite_tac[] >>
  `!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
    FLOOKUP child.vs_allocas id = SOME (q,k)` by
    (qpat_assum `!id q k. FLOOKUP entry.vs_allocas id = _ ==> _` mp_tac >>
     qpat_assum `entry.vs_allocas = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     qpat_x_assum `entry.vs_allocas = _` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!id. id < child_lo \/ child_hi <= id ==> _`,
        `!id. id < lo \/ hi <= id ==> _`,
        `entry.vs_allocas = _`, `lo <= header_id`,
        `header_id < child_lo`, `child_hi <= hi`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     rpt strip_tac >>
     `id < child_lo \/ child_hi <= id` by decide_tac >>
     metis_tac[] ) >> (
  `abi_decode_footprint_frame
     ((d+32+j*type_memory_size tv,type_memory_size tv)::new_scratch) u child` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_footprint_frame _ entry child`,
        `entry.vs_memory = _`, `entry.vs_call_ctx = _`,
        `entry.vs_data_section = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_footprint_frame_def]) >>
  `abi_decode_footprint_frame
     ((d,32+maxn*type_memory_size tv)::(scratch++new_scratch)) initial child` by
    (irule calldata_footprint_accumulate >>
     qexistsl [`d+32+j*type_memory_size tv`,`type_memory_size tv`,`u`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  `abi_decode_footprint_frame
     ((d,32+maxn*type_memory_size tv)::(scratch++new_scratch++[(p,32)])) initial v` by
    (qpat_assum `abi_decode_footprint_frame _ initial child` mp_tac >>
     qpat_assum `abi_decode_footprint_frame [(p,32)] child v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule_all registration_footprint_append >> simp[APPEND_ASSOC]) >>
  qexists `scratch++new_scratch++[(p,32)]` >>
  conj_tac >-
    (qpat_assum `abi_decode_footprint_frame _ initial v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ADD_COMM]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!q k. MEM (q,k) scratch ==> _`,
     `!q k. MEM (q,k) new_scratch ==> _`,
     `!id q k. FLOOKUP u.vs_allocas id = _ ==> _`,
     `FLOOKUP u.vs_allocas header_id = _`,
     `lo <= header_id`, `header_id < child_lo`, `child_hi <= hi`,
     `child_lo <= child_hi`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- (first_x_assum drule >> strip_tac >> qexists `id` >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      first_assum irule >> first_assum ACCEPT_TAC)
  >- (first_x_assum drule >> strip_tac >> qexists `id` >> simp[] >> decide_tac)
  >> qexists `header_id` >> simp[] >>
  first_assum irule >> first_assum ACCEPT_TAC))
QED
Resume calldata_exact_owned_child_backedge[transfer]:
  markerLib.RESUME_TAC >>
  qpat_assum `Rel entry child` mp_tac >>
  qpat_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx fn child = _ /\ _` mp_tac >>
  qpat_assum `Rel = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >> POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx fn child = _ /\ _`
    (qspecl_then [`fuel`,`r`] mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx fn entry = _ /\ _`
    (qspecl_then [`fuel'`,`r`] mp_tac) >> asm_rewrite_tac[] >> metis_tac[]
QED
Finalise calldata_exact_owned_child_backedge
