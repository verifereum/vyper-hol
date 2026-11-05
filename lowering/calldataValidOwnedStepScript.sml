(* Source-indexed successful dynamic-array iteration boundaries. *)
Theory calldataValidOwnedStep
Ancestors
  calldataValidOwnedChild calldataDynOwned valueEncodingProps valueEncodingProofs
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
