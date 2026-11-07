(* Source-indexed successful dynamic-array iteration boundaries. *)
Theory calldataValidOwnedStep
Ancestors
  calldataValidOwnedChild calldataDynOwned abiEncoderChildSuffix valueEncodingProps valueEncodingProofs
  abiDecoderValidArrayEntry abiDecoderValidContract abiDecoderContract
  abiDecoderLoopRegisters abiDecoderArrayInvariant abiDecoderReentry abiDecoderArrayBackedge
  abiDecoderExecution abiDecoderTypedContract
  compileEnv emitHelperProps exprLoweringProps fragExecMem
  venomState venomExecSemantics words list arithmetic

(* A successful child plus an unchanged prefix extends the exact source prefix.
   In particular this does not require a positive element stride. *)
Theorem calldata_valid_prefix_advance[local]:
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) before) /\
  mem_bytes_at d (32+j*type_memory_size tv) after =
    mem_bytes_at d (32+j*type_memory_size tv) before /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) after ==>
  !k. k < SUC j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) after
Proof
  strip_tac >> rpt strip_tac >> Cases_on `k = j` >- gvs[] >>
  `k < j /\ k < LENGTH vs` by decide_tac >>
  `val_wf tv (EL k vs)` by fs[EVERY_EL] >>
  `val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) before` by simp[] >>
  `k*type_memory_size tv+type_memory_size tv <= j*type_memory_size tv` by
    (`(k+1)*type_memory_size tv <= j*type_memory_size tv` by
       simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(k+1)*_ <= j*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
  irule val_in_memory_mem_agree >> conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`type_memory_size tv`,`before`] >>
  asm_rewrite_tac[LESS_EQ_REFL] >> first_x_assum irule >> decide_tac
QED

(* Extend the source prefix through the real index-cell write and backedge. *)
Theorem calldata_valid_backedge_prefix[local]:
  t = jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) child)) /\
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) before) /\
  mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) before /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
  (d+(32+SUC j*type_memory_size tv) <= p \/ p+32 <= d) ==>
  (!k. k < SUC j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) t.vs_memory) /\
  mem_bytes_at d (32+j*type_memory_size tv) t.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) before
Proof
  strip_tac >>
  `!a len. a+len <= p \/ p+32 <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len child.vs_memory` by
    (drule (cj 8 calldata_backedge_owned_state) >> simp[]) >>
  qpat_x_assum `t = jump_to _ _` kall_tac >>
  `mem_bytes_at d (32+j*type_memory_size tv) t.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) before` by
    (`mem_bytes_at d (32+j*type_memory_size tv) t.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory` by
       (first_x_assum irule >> fs[MULT_CLAUSES] >> decide_tac) >>
     asm_rewrite_tac[]) >>
  `val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory` by
    (irule val_in_memory_mem_agree >> conj_tac >- fs[EVERY_EL] >>
     qexistsl_tac [`type_memory_size tv`,`child.vs_memory`] >>
     asm_rewrite_tac[LESS_EQ_REFL] >> sym_tac >> first_x_assum irule >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  asm_rewrite_tac[] >> metis_tac[calldata_valid_prefix_advance]
QED

(* The successful count branch preserves the original source window and the
   actual allocation frontier needed by the source-specific setup theorem. *)
Theorem calldata_valid_header_prepare[local]:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d outsz b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    ~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0 /\
    fresh_vars_wrt limit_st head /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
      d outsz b cap head /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD head) = bs /\
    eval_operand ip head = SOME (n2w p) /\ mload p head = n2w j /\
    head.vs_memory = u.vs_memory /\ head.vs_call_ctx = u.vs_call_ctx /\
    head.vs_data_section = u.vs_data_section /\ head.vs_allocas = u.vs_allocas /\
    head.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op head = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn head = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn head ==> mem_safe_run fuel' ctx fn u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `head = jump_to body_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) u)` >>
  `src <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `STRING #"%" (toString next) <> STRING #"%" (toString (next+1))` by
    simp[] >>
  `mload (w2n (n2w p:bytes32)) u = n2w j /\
    w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  `head = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) u)` by simp[Abbr `head`] >>
  `j <= LENGTH vs` by decide_tac >>
  `lookup_block (if j < LENGTH vs then body_lbl else exit_lbl) fn.fn_blocks =
    SOME body_bb` by simp[] >>
  drule_all calldata_header_owned_safe_transfer >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `head = jump_to _ _` kall_tac >>
  drule_all abi_decoder_header_registers >> strip_tac >>
  `fresh_vars_wrt limit_st head /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op head = eval_operand op u)` by
    simp[Abbr `head`] >>
  `~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0` by
    simp[Abbr `head`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  qexists_tac `head` >> conj_tac >- simp[Abbr `head`] >>
  asm_rewrite_tac[] >>
  suspend "source_fields"
QED

Resume calldata_valid_header_prepare[source_fields]:
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
  qpat_assum `mem_bytes_at _ _ (abi_decode_source _ u) = _` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op head = _` mp_tac >>
  qpat_assum `abi_decoder_operand_live next src` mp_tac >>
  qpat_assum `abi_decoder_operand_live next dst` mp_tac >>
  qpat_assum `abi_decoder_operand_live next ip` mp_tac >>
  qpat_assum `head.vs_call_ctx = u.vs_call_ctx` mp_tac >>
  qpat_assum `head.vs_data_section = u.vs_data_section` mp_tac >>
  qpat_assum `head.vs_memory = u.vs_memory` mp_tac >>
  qpat_assum `eval_operand ip u = SOME (n2w p)` mp_tac >>
  qpat_assum `mload p u = n2w j` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  fs[abi_decoder_ranges_def, abi_decode_source_def, mload_def]
QED

Finalise calldata_valid_header_prepare

(* Reach the source-specific recursive entry, rather than quantifying over
   arbitrary decoder operands/source windows as the old owned step did. *)
Theorem calldata_valid_header_child_reach[local]:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  FLOOKUP u.vs_allocas iid = SOME (p,32) /\ alloca_inv u /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  ready.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_valid_header_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `head = jump_to _ _` (mk_asm "headdef") >>
  qpat_x_assum `lookup_block u.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block body_lbl _ = _` kall_tac >>
  qpat_x_assum `phi_prefix_length _ = _` kall_tac >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_decoder_operand_live st0.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  `eval_operand ip head = SOME (n2w p) /\ mload p head = n2w j /\
   FLOOKUP head.vs_allocas iid = SOME (p,32) /\ alloca_inv head` by
    (asm_rewrite_tac[] >> metis_tac[cj 1 calldata_alloca_invariants_fields]) >>
  drule_all calldata_valid_owned_array_child_entry >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  asm_rewrite_tac[listTheory.LENGTH, combinTheory.K_THM] >> strip_tac >>
  asm "headdef" (fn th => pure_rewrite_tac[GSYM th]) >>
  asm_x "headdef" kall_tac >>
  rename1 `entry.vs_current_bb = ready.cs_current_bb` >>
  qexists_tac `entry` >> asm_rewrite_tac[] >>
  suspend "child_fields"
QED

Resume calldata_valid_header_child_reach[child_fields]:
  `abi_decoder_address_frame st0.cs_next_var head entry` by
    fs[abi_decoder_valid_array_entry_def] >>
  qpat_x_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  fs[abiDecoderDynamicLoopSetupTheory.abi_decoder_address_frame_def] >>
  conj_tac
  >- metis_tac[abi_decoder_operand_live_mono] >>
  rpt strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ entry <> Error e) ==> _` drule >>
  disch_then (qx_choose_then `fhead` strip_assume_tac) >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ head <> Error e) ==> _`
    (qspec_then `fhead` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise calldata_valid_header_child_reach

(* The backedge writes the already-owned index cell, not a new footprint. *)
Theorem calldata_valid_successor_footprint[local]:
  abi_decode_footprint_frame ((d,sz)::old) initial u /\
  entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
  entry.vs_data_section = u.vs_data_section /\
  abi_decode_footprint_frame ((e,stride)::new) entry child /\
  d <= e /\ e+stride <= d+sz /\ MEM (p,32) old /\
  v = jump_to hdr (mstore p w (update_var nv w child)) ==>
  abi_decode_footprint_frame ((d,sz)::(old++new)) initial v
Proof
  strip_tac >>
  `abi_decode_footprint_frame ((d,sz)::old) initial entry` by
    (irule abi_encoder_footprint_memory >>
     fs[abiDecoderFrameTheory.abi_decode_footprint_frame_def] >> metis_tac[]) >>
  drule_all calldata_footprint_accumulate >> strip_tac >>
  `abi_decode_footprint_frame ((d,sz)::(old++new)) child (mstore p w child)` by
    (irule abi_encoder_store_footprint >> simp[MEM_APPEND]) >>
  `abi_decode_footprint_frame ((d,sz)::(old++new)) initial (mstore p w child)` by
    (irule abiDecoderFrameTheory.abi_decode_footprint_frame_trans >>
     qexists_tac `child` >> asm_rewrite_tac[]) >>
  irule abi_encoder_footprint_memory >>
  conj_tac
  >- fs[abiDecoderFrameTheory.abi_decode_footprint_frame_def,
        jump_to_def, mstore_def, update_var_def] >>
  conj_tac
  >- fs[abiDecoderFrameTheory.abi_decode_footprint_frame_def,
        jump_to_def, mstore_def, update_var_def] >>
  qexists_tac `mstore p w child` >>
  simp[jump_to_def, mstore_def, update_var_def]
QED

(* Only variables below the final register bound are written on the backedge;
   CALLDATALOAD's source window is unaffected by its index-cell store. *)
Theorem calldata_valid_backedge_source[local]:
  v = jump_to hdr (mstore p w
    (update_var (STRING #"%" (toString nvar)) w child)) /\
  nvar < limit_st.cs_next_var /\ fresh_vars_wrt limit_st child /\
  src <> Var (STRING #"%" (toString nvar)) /\
  dst <> Var (STRING #"%" (toString nvar)) /\
  child.vs_call_ctx = u.vs_call_ctx /\
  child.vs_data_section = u.vs_data_section /\
  eval_operand src child = eval_operand src u /\
  eval_operand dst child = eval_operand dst u /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz b cap u /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD u) = bs ==>
  fresh_vars_wrt limit_st v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz b cap v /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD v) = bs
Proof
  strip_tac >> conj_tac
  >- (asm_rewrite_tac[] >> simp[] >> irule fresh_vars_wrt_mstore >>
      irule abi_decoder_generated_update_fresh >> simp[]) >>
  `v.vs_call_ctx = child.vs_call_ctx /\
   v.vs_data_section = child.vs_data_section /\
   eval_operand src v = eval_operand src child /\
   eval_operand dst v = eval_operand dst child` by
    (`eval_operand src (update_var (STRING #"%" (toString nvar)) w child) =
        eval_operand src child /\
      eval_operand dst (update_var (STRING #"%" (toString nvar)) w child) =
        eval_operand dst child` by
       (Cases_on `src` >> Cases_on `dst` >>
        gvs[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
     asm_rewrite_tac[] >> simp[eval_operand_mstore] >>
     simp[jump_to_def, mstore_def, update_var_def]) >>
  fs[abi_decoder_ranges_def, abi_decode_source_def]
QED

(* Transport allocation evidence through a nested interval and its backedge. *)
Theorem calldata_valid_successor_allocations[local]:
  lo <= a /\ a <= b /\ b <= hi /\
  (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  (!id. id < a \/ b <= id ==>
    FLOOKUP child.vs_allocas id = FLOOKUP u.vs_allocas id) /\
  (!q k. MEM (q,k) old ==> ?id. lo <= id /\ id < hi /\
    FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  (!q k. MEM (q,k) new ==> ?id. a <= id /\ id < b /\
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  v.vs_allocas = child.vs_allocas ==>
  (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    FLOOKUP v.vs_allocas id = SOME (q,k)) /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  (!q k. MEM (q,k) (old++new) ==> ?id. lo <= id /\ id < hi /\
    FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  strip_tac >> asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < a \/ b <= id` by decide_tac >> metis_tac[]) >>
  `!q k. MEM (q,k) old ==> ?id. lo <= id /\ id < hi /\
      FLOOKUP child.vs_allocas id = SOME (q,k)` by
    metis_tac[] >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `id` >> simp[] >> decide_tac
QED

(* One successful iteration, with the source and element index fixed in the
   recursive premise. All predicates below are theorem-local abbreviations. *)
Theorem calldata_valid_owned_header_step:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      H = \j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
        mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
        s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
        FLOOKUP s.vs_allocas iid = SOME (p,32) /\
        FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
        alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
        Own st.cs_next_id end_st.cs_next_id s /\
        initial.vs_alloca_next <= s.vs_alloca_next /\
        (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
          FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
        (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op s = eval_operand op initial) /\
        abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
        MEM (p,32) scratch /\
        (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        fresh_vars_wrt limit_st s /\
        abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= st1.cs_next_id /\
  st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
        (STRING #"%" (toString nvar)) ip hdr|> /\
  FST ops = Var biv /\ abi_decoder_operand_live ready.cs_next_var (FST ops) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (iid < ready.cs_next_id \/ st1.cs_next_id <= iid) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var /\
  nvar < limit_st.cs_next_var /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  (!head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    Own ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) ==>
    ?child new.
      ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
      child.vs_inst_idx = LENGTH st1.cs_current_insts /\
      val_wf tv (EL j vs) /\
      val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
      fresh_vars_wrt limit_st child /\
      child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
      alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
      Own ready.cs_next_id st1.cs_next_id child /\
      entry.vs_alloca_next <= child.vs_alloca_next /\
      (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
        FLOOKUP child.vs_allocas id = SOME (q,k)) /\
      (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
      (!op. abi_decoder_operand_live ready.cs_next_var op ==>
        eval_operand op child = eval_operand op entry) /\
      abi_decode_footprint_frame
        ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
      (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP child.vs_allocas id = SOME (q,k)) /\ Safe entry child) /\
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  ?v new. H (SUC j) v (old++new) /\
    (!k. k < SUC j ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!head entry. _` (mk_asm "child") >>
  qpat_x_assum `H j u old` mp_tac >>
  qpat_assum `Abbrev (H = _)` (fn th => CONV_TAC
    (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL calldata_valid_header_child_reach) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "child_input"
QED

Resume calldata_valid_owned_header_step[child_input]:
  `j+1 <= maxn` by decide_tac >>
  `j*type_memory_size tv+type_memory_size tv <= maxn*type_memory_size tv` by
    (`(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `alloca_inv entry /\ alloca_frontier_inv ctx fn site entry` by
    (mp_tac (Q.INST [`s` |-> `u`, `t` |-> `entry`]
       (SPEC_ALL calldata_alloca_invariants_fields)) >> asm_rewrite_tac[]) >>
  `Own ready.cs_next_id st1.cs_next_id entry` by
    (qpat_x_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >> strip_tac >>
     asm_rewrite_tac[] >> match_mp_tac (Q.INST
       [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`]
       calldata_owned_interval_restrict) >> asm_rewrite_tac[]) >>
  `fresh_vars_wrt limit_st entry` by fs[abi_decoder_valid_array_entry_def] >>
  asm_x "child" (qspecl_then [`head`,`entry`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> strip_tac >>
  suspend "backedge"
QED

Resume calldata_valid_owned_header_step[backedge]:
  `eval_operand (FST ops) entry = SOME (n2w j)` by
    (qpat_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `!op. abi_decoder_operand_live next op ==>
    eval_operand op child = eval_operand op u` by
    (qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op entry = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand (Var biv) child = SOME (n2w j) /\
   eval_operand ip child = SOME (n2w p)` by
    (conj_tac
     >- (qpat_assum `FST ops = Var biv` mp_tac >>
         qpat_assum `eval_operand (FST ops) entry = _` mp_tac >>
         qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
         qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op child = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     qpat_assum `abi_decoder_operand_live next ip` mp_tac >>
     qpat_assum `eval_operand ip u = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op child = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` by
    (asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >> decide_tac) >>
  qabbrev_tac `v = jump_to hdr (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child))` >>
  qpat_x_assum `Abbrev (v = _)` (mk_asm "vdef" o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  suspend "backedge_run"
QED

Resume calldata_valid_owned_header_step[backedge_run]:
  `lookup_block child.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
        (STRING #"%" (toString nvar)) ip hdr|>` by asm_rewrite_tac[] >>
  `phi_prefix_length (abi_decode_header_insts hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) body_lbl exit_lbl) = 0` by
    simp[abi_decode_header_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
  `ip <> Var (STRING #"%" (toString nvar))` by
    (qpat_assum `!op. op = src \/ _ ==> _` (qspec_then `ip` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  asm "vdef" (mp_then Any mp_tac calldata_backedge_owned_safe_transfer) >>
  disch_then drule >> simp_tac (srw_ss()) [] >>
  `st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
    (STRING #"%" (toString nvar)) ip hdr =
   st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
    (STRING #"%" (toString nvar)) ip hdr` by REFL_TAC >>
  disch_then drule >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = SOME _`)) >>
  simp_tac (srw_ss()) [] >>
  disch_then (qspecl_then [`site`,`LENGTH vs`,`ctx`] mp_tac) >>
  asm_rewrite_tac[] >>
  (impl_tac >- (qpat_assum `w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` mp_tac >>
    rewrite_tac[w2n_n2w])) >> strip_tac >>
  asm_x "vdef" mp_tac >> asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >>
  disch_then (mk_asm "vdef") >>
  `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory` by
    (mp_tac (Q.INST [`s` |-> `entry`, `t` |-> `child`,
       `dst` |-> `d`, `stride` |-> `type_memory_size tv`, `scratch` |-> `new`,
       `output_id` |-> `oid`, `lo` |-> `ready.cs_next_id`,
       `hi` |-> `st1.cs_next_id`] (SPEC_ALL calldata_child_preserves_contained_prefix)) >>
     asm_rewrite_tac[] >> impl_tac >- decide_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`v`,`new`] >>
  conj_tac >- suspend "successor" >>
  conj_tac >- suspend "prefix" >> suspend "safe"
QED

Resume calldata_valid_owned_header_step[safe]:
  qpat_assum `Safe entry child` mp_tac >>
  qpat_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` mp_tac >>
  qpat_assum `!fuel. (!e. run_from fuel ctx fn v <> Error e) ==> _` mp_tac >>
  qpat_assum `Abbrev (Safe = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> POP_ASSUM_LIST (K all_tac) >>
  ntac 3 strip_tac >> rpt strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx fn v <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn child = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume calldata_valid_owned_header_step[prefix]:
  match_mp_tac (Q.INST [`before` |-> `u.vs_memory`,
    `nv` |-> `STRING #"%" (toString (nvar:num))`] (cj 1 calldata_valid_backedge_prefix)) >>
  asm "vdef" (fn th => rewrite_tac [th]) >> asm_rewrite_tac[] >>
  `SUC j * type_memory_size tv <= maxn * type_memory_size tv` by
    (simp[LE_MULT_RCANCEL] >> decide_tac) >> decide_tac
QED

Resume calldata_valid_owned_header_step[successor]:
  qpat_assum `Abbrev (H = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >>
  suspend "resources"
QED
Resume calldata_valid_owned_header_step[resources]:
  `fresh_vars_wrt limit_st v /\
   abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs) d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap v /\
   mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD v) = bs` by
    suspend "source_fields" >>
  `abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::(old++new)) initial v` by
    suspend "footprint" >>
  suspend "allocation_fields"
QED
Resume calldata_valid_owned_header_step[source_fields]:
  match_mp_tac (Q.INST [`u` |-> `u`, `child` |-> `child`, `w` |-> `n2w (SUC j):bytes32`]
    calldata_valid_backedge_source) >>
  asm "vdef" (fn th => rewrite_tac [th]) >> asm_rewrite_tac[] >>
  qpat_assum `!op. op = src \/ _ ==> _` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op child = _` mp_tac >>
  qpat_assum `abi_decoder_operand_live next src` mp_tac >>
  qpat_assum `abi_decoder_operand_live next dst` mp_tac >>
  qpat_assum `eval_operand src u = _` mp_tac >>
  qpat_assum `eval_operand dst u = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume calldata_valid_owned_header_step[footprint]:
  irule (GEN_ALL calldata_valid_successor_footprint) >>
  asm "vdef" (irule_at (Pat `v = _`)) >>
  qpat_assum `abi_decode_footprint_frame _ initial u`
    (irule_at (Pat `abi_decode_footprint_frame _ initial _`)) >>
  qpat_assum `abi_decode_footprint_frame _ entry child`
    (irule_at (Pat `abi_decode_footprint_frame _ _ child`)) >>
  asm_rewrite_tac[] >> decide_tac
QED
Resume calldata_valid_owned_header_step[allocation_fields]:
  qpat_assum `entry.vs_allocas = u.vs_allocas`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `a` |-> `ready.cs_next_id`, `b` |-> `st1.cs_next_id`]
    (SPEC_ALL calldata_valid_successor_allocations)) >>
  asm_rewrite_tac[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "owned_fields"
QED
Resume calldata_valid_owned_header_step[owned_fields]:
  `Own st.cs_next_id end_st.cs_next_id v` by
    (qpat_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
     qpat_assum `Own ready.cs_next_id st1.cs_next_id child` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >>
     ntac 2 strip_tac >> asm_rewrite_tac[] >>
     match_mp_tac (Q.INST [`s` |-> `u`, `a` |-> `ready.cs_next_id`,
       `b` |-> `st1.cs_next_id`] calldata_owned_interval_replace) >>
     asm_rewrite_tac[] >> decide_tac) >>
  asm_rewrite_tac[MEM_APPEND] >>
  suspend "remaining_fields"
QED
Resume calldata_valid_owned_header_step[remaining_fields]:
  `!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op u` by
    (qpat_assum `!op. op = src \/ _ ==> _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. op <> Var _ ==> eval_operand op v = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   eval_operand ip v = SOME (n2w p)` by
    (qpat_assum `!op. op = src \/ _ ==> eval_operand op v = _` mp_tac >>
     qpat_assum `eval_operand src u = _` mp_tac >>
     qpat_assum `eval_operand dst u = _` mp_tac >>
     qpat_assum `eval_operand ip u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op initial` by
    (qpat_assum `!op. op = src \/ _ ==> eval_operand op v = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `FLOOKUP child.vs_allocas iid = SOME (p,32) /\
   FLOOKUP child.vs_allocas oid = SOME (base_addr,cap)` by
    (qpat_assum `!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==> _` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas iid = _` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas oid = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "pc" >>
  suspend "counter_source"
QED
Resume calldata_valid_owned_header_step[pc]:
  asm "vdef" (fn th => rewrite_tac [th]) >>
  simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED
Resume calldata_valid_owned_header_step[counter_source]:
  `v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\ mload p v = n2w (SUC j)` by
    (asm "vdef" (fn th => rewrite_tac [th]) >>
     simp[jump_to_def, abi_decode_mload_jump, venomMemProofsTheory.mload_mstore_same_proof]) >>
  `abi_decode_load CALLDATALOAD srcword v = n2w (LENGTH vs)` by
    (qpat_assum `abi_decode_load CALLDATALOAD srcword u = _` mp_tac >>
     qpat_assum `v.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
     qpat_assum `u.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[abi_decode_load_def, abi_decode_source_def]) >>
  `mem_word_at d child.vs_memory = mem_word_at d u.vs_memory` by
    (qpat_assum `mem_bytes_at d _ child.vs_memory = mem_bytes_at d _ u.vs_memory`
       (mp_then Any mp_tac (cj 2 mem_bytes_at_agree_window)) >>
     disch_then (qspec_then `d` mp_tac) >> simp[]) >>
  `mem_word_at d v.vs_memory = mem_word_at d child.vs_memory` by
    (`mem_bytes_at d 32 v.vs_memory = mem_bytes_at d 32 child.vs_memory` by
       (qpat_x_assum `!a len. _ ==> mem_bytes_at a len v.vs_memory = _`
          (qspecl_then [`d`, `32`] mp_tac) >>
        simp[]) >>
     drule (cj 2 mem_bytes_at_agree_window) >>
     disch_then (qspec_then `d` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> decide_tac
QED

Finalise calldata_valid_owned_header_step
