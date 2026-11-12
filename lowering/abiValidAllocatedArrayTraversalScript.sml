(* Finite successful traversal, including the equal-count exit header. *)
Theory abiValidAllocatedArrayTraversal
Ancestors
  abiValidAllocatedArrayIteration abiValidAllocatedArrayLoop abiValidAllocatedArrayPrefix
  abiValidAllocatedArraySource abiValidAllocatedContract abiValidAllocatedMembers
  abiMalformedTraversal abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiDecoderLoop abiDecoderExecution abiDecoderContract abiDecoderCoherence
  abiDecoderArrayBackedge abiValidAllocatedArrayInit
  abiMalformedNavigation abiDecodeRanges abiValidAggregateHeads
  localPtrsProps exprSimDefs exprLoweringProps compileEnv fragExec
  venomState venomMemDefs venomExecSemantics venomInst valueEncoding valueEncodingProps
  vyperABI contractABI finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_array_exit:
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin (LENGTH vs) s /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl|> /\
  start.cs_next_var <= first /\
  first+4+abi_decode_position_header_delta base_op <= ceiling.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first base_op /\
  LENGTH vs < dimword (:256) /\ LENGTH vs = abi_head_word (DROP p xs) /\ p+32 <= L /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] ==>
  frag_outcome ctx func s final
    (\u. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d u.vs_memory /\
      abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
        sites dstid d outsz origin u /\ fresh_vars_wrt ceiling u) (K F)
Proof
  strip_tac >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
     base_op hi src dst B L xs p d outsz s /\
   eval_operand ip s = SOME (n2w slot) /\ mload slot s = n2w (LENGTH vs) /\
   slot < dimword (:256) /\ fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
   s.vs_current_bb = hdr /\ s.vs_inst_idx = 0` by
    fs[abi_valid_allocated_array_inv_def] >>
  `eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
   stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv start /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\ B+L < dimword (:256)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def, abi_decode_source_def] >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w (LENGTH vs)` by
    metis_tac[abi_checked_offset_load] >>
  `abi_decode_position_loop_ready hdr ip src MLOAD base_op B p
     (n2w slot) (LENGTH vs) (LENGTH vs) s` by
    simp[abi_decode_position_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first)) /\
   base_op <> Var (STRING #"%" (toString first))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >> qexists_tac `first` >> simp[]) >>
  drule_all abi_valid_allocated_position_header_effect >>
  disch_then (qspecl_then [`sites`, `outsz`, `dstid`, `d`] strip_assume_tac) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz s h` by
    (irule abi_valid_allocated_effect_weaken >>
     qhdtm_assum `abi_valid_allocated_effect` (irule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz origin h` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `s` >>
     fs[abi_valid_allocated_array_inv_def]) >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d h.vs_memory` by
    (drule abi_valid_allocated_array_inv_complete >> simp[]) >>
  simp[frag_outcome_def] >> qexists_tac `h` >> simp[] >>
  qpat_x_assum `abi_decode_sim ctx func s h` mp_tac >> simp[abi_decode_sim_def]
QED

Theorem abi_valid_allocated_array_traversal:
  EVERY (val_wf tv) vs /\ LENGTH vs < dimword (:256) /\
  32+LENGTH vs*type_memory_size tv <= outsz /\
  abi_valid_allocated_type_contract ce env sf ty tv /\
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\
  mem_sz = type_memory_size tv /\ childsz = type_memory_bytes ce ty /\
  abi_sz = abi_member_head_size (vyper_to_abi_type env ty) /\
  LENGTH xs = L /\ LENGTH vs = abi_head_word (DROP p xs) /\ p+32 <= L /\
  p+32+LENGTH vs*abi_sz <= L /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
    (DROP (p+32) xs) (DROP (p+32) xs) /\
  abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
    (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs /\
  (!k. k < LENGTH vs ==> d+32+k*mem_sz+childsz <= d+outsz) /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] /\
  setup.cs_current_bb = body_lbl /\ setup.cs_current_insts = [] /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  FST ops = Var iv /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi di child = ((),child_end) /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts bid iv (STRING #"%" (toString next)) ip hdr /\
  fn_inst_ids_distinct func /\
  child_sites = abi_malformed_scratch_sites child child_end func /\
  child_sites SUBSET sites /\ inst.inst_id NOTIN child_sites /\
  start.cs_next_var <= first /\ start.cs_next_var <= setup.cs_next_var /\
  setup.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= ceiling.cs_next_var /\
  first+4+abi_decode_position_header_delta base_op <= ceiling.cs_next_var /\
  abi_decoder_operand_live first ip /\ abi_decoder_operand_live first src /\
  abi_decoder_operand_live first base_op /\
  abi_decoder_operand_live setup.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  ip <> Var (STRING #"%" (toString next)) /\
  start.cs_next_var <= next /\ next < ceiling.cs_next_var /\
  (!k childpos cd incoming. k < LENGTH vs /\
    abi_valid_allocated_entry ce env sf ty tv (EL k vs) ctx func cenv cx es
      child child_end base_op hi (FST (SND ops)) (SND (SND ops))
      B L xs childpos cd dstid live ceiling incoming ==>
    ?u. abi_valid_allocated_post tv (EL k vs) ctx func cenv cx es
      child child_end ceiling dstid cd childsz incoming u) ==>
  !j s. j <= LENGTH vs /\
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin j s ==>
  frag_outcome ctx func s final
    (\u. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d u.vs_memory /\
      abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
        sites dstid d outsz origin u /\ fresh_vars_wrt ceiling u) (K F)
Proof
  strip_tac >> completeInduct_on `LENGTH vs-j` >> rpt strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
      drule abi_valid_allocated_array_exit >> disch_then irule >>
      simp[] >> qexistsl_tac [`body_lbl`, `first`, `hid`] >> simp[]) >>
  `j < LENGTH vs` by decide_tac >>
  `frag_outcome ctx func s header
    (abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
      sites dstid live base_op hi src dst B L xs p d outsz
      ip slot inst q hdr tv vs origin (SUC j)) (K F)` by
    (irule abi_valid_allocated_array_iteration >>
     qhdtm_assum `abi_valid_allocated_array_inv` (irule_at Any) >>
     goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >>
     goal_assum (drule_at (Pat `abi_valid_allocated_type_contract _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`hid`, `first`, `exit_lbl`] >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac
     >- (qpat_x_assum `!k. k < LENGTH vs ==> _` (qspec_then `j` mp_tac) >>
         simp[] >> decide_tac) >>
     metis_tac[]) >>
  irule frag_outcome_compose >>
  goal_assum (drule_at Any) >>
  rpt strip_tac >>
  qpat_x_assum `!m. m < _ ==> !vs j. _` (qspec_then `LENGTH vs-SUC j` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`vs`, `SUC j`] mp_tac) >> simp[] >>
  disch_then irule >> simp[] >> metis_tac[]
QED
