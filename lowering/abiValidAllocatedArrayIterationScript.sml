(* Compiled successful dynamic-array iteration, retaining the original frontier. *)
Theory abiValidAllocatedArrayIteration
Ancestors
  abiValidAllocatedArrayLoop abiValidAllocatedArrayPrefix abiValidAllocatedArraySource
  abiValidAllocatedArrayInit abiValidAllocatedMembers abiValidAllocatedContract
  abiMalformedTraversal abiMalformedRecursiveInterface abiMalformedSiteFrame abiMalformedMemberSetup
  abiDecoderArraySetupInputs abiDecoderSequenceReach abiDecoderStaticLoopSetup
  abiDecoderDynamicLoopSetup abiDecoderExecution abiDecoderContract abiDecoderLoop
  abiDecoderArrayBackedge abiDecoderReentry abiDecoderCoherence abiDecoderOffset abiMalformedNavigation
  abiDecodeRanges abiValidAggregateHeads abiDecoderOffsetHead abiDecoderDynamic emitHelperProps rich_list
  abiDecoderTypedCompose abiDecoderLoopRegisters abiDecoderLoopSetup
  localPtrsProps exprSimDefs exprLoweringProps compileEnv fragExec
  venomState venomMemDefs venomMemProps venomExecSemantics venomInst
  valueEncoding valueEncodingProps vyperABI contractABI finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_array_iteration:
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin j s /\
  j < LENGTH vs /\ EVERY (val_wf tv) vs /\ LENGTH vs < dimword (:256) /\
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
  d+32+j*mem_sz+childsz <= d+outsz /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
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
  (!childpos cd incoming.
    abi_valid_allocated_entry ce env sf ty tv (EL j vs) ctx func cenv cx es
      child child_end base_op hi (FST (SND ops)) (SND (SND ops))
      B L xs childpos cd dstid live ceiling incoming ==>
    ?u. abi_valid_allocated_post tv (EL j vs) ctx func cenv cx es
      child child_end ceiling dstid cd childsz incoming u) ==>
  frag_outcome ctx func s header
    (abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
      sites dstid live base_op hi src dst B L xs p d outsz
      ip slot inst q hdr tv vs origin (SUC j)) (K F)
Proof
  strip_tac >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
     base_op hi src dst B L xs p d outsz s /\
   eval_operand ip s = SOME (n2w slot) /\ mload slot s = n2w j /\
   slot < dimword (:256) /\ fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
   s.vs_current_bb = hdr /\ s.vs_inst_idx = 0` by
    fs[abi_valid_allocated_array_inv_def] >>
  `eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
   stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv start /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\ B+L < dimword (:256)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def, abi_decode_source_def] >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w (LENGTH vs)` by
    (metis_tac[abi_checked_offset_load]) >>
  `abi_decode_position_loop_ready hdr ip src MLOAD base_op B p (n2w slot) (LENGTH vs) j s` by
    simp[abi_decode_position_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first)) /\
   base_op <> Var (STRING #"%" (toString first))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >> qexists_tac `first` >> simp[]) >>
  `?h. abi_decode_sim ctx func s h /\
    abi_valid_allocated_effect ctx func cenv cx es first sites dstid d outsz s h /\
    fresh_vars_wrt ceiling h /\ h.vs_memory = s.vs_memory /\
    h.vs_current_bb = body_lbl /\ h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    h.vs_allocas = s.vs_allocas` by
    (`abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
     drule_all abi_malformed_position_header_sim >> strip_tac >>
     drule_all abi_malformed_header_resource >>
     disch_then (qspecl_then [`sites`, `p`, `LENGTH vs`, `body_lbl`,
       `j`, `dstid`, `B`] strip_assume_tac) >>
     qexists_tac `jump_to body_lbl
       (abi_decode_position_header_state base_op first B p j (LENGTH vs) s)` >>
     simp[abi_valid_allocated_effect_def] >>
     Cases_on `base_op = Lit 0w` >>
     fs[abi_valid_allocated_frame_def, abi_decode_position_header_state_def,
        jump_to_def, update_var_def, abi_decode_position_loop_ready_def] >>
     gvs[]) >>
  suspend "body"
QED

Resume abi_valid_allocated_array_iteration[body]:
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
    sites dstid d outsz s h` by
    (irule abi_valid_allocated_effect_weaken >>
     qhdtm_assum `abi_valid_allocated_effect` (irule_at Any) >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h` by
    fs[abi_valid_allocated_effect_def] >>
  `local_ptrs_reserved cenv setup` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es setup sites dstid live
    base_op hi src dst B L xs p d outsz h` by
    (irule abi_malformed_aggregate_reentry >>
     qpat_assum `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[]) >>
  `eval_operand ip h = SOME (n2w slot) /\ mload slot h = n2w j` by
    (fs[abi_valid_allocated_effect_def, abi_malformed_resource_post_def, mload_def] >> metis_tac[]) >>
  qabbrev_tac `(childpos:num) = p+32+(if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz)` >>
  `childpos <= L /\
   vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP childpos xs) /\
   abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP childpos xs)) = SOME (EL j vs) /\
   (is_dynamic (vyper_to_abi_type env ty) \/ childpos+static_length (vyper_to_abi_type env ty) <= L)` by
    (qunabbrev_tac `childpos` >>
     metis_tac[abi_valid_allocated_array_child_position]) >>
  `?a. run_inst_seq (emitted_insts setup child) h = OK a /\
    abi_malformed_entry ctx func cenv cx es child sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      childpos (d+32+j*mem_sz) childsz a /\
    abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h a /\
    eval_operand (FST ops) a = SOME (n2w j) /\
    eval_operand ip a = SOME (n2w slot) /\ fresh_vars_wrt ceiling a /\
    a.vs_memory = h.vs_memory` by
    (Cases_on `dec_info_needs_offset di`
     >- (`p+32+j*abi_sz+32 <= L /\
          p+32+abi_head_word (DROP (p+32+j*abi_sz) xs)+abi_sz <= L` by
          (`is_dynamic (vyper_to_abi_type env ty) /\
            (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
             (metis_tac[abi_decoder_needs_offset_iff, abi_decoder_coherent_dynamic,
                abi_decoder_nonempty_readable_head]) >>
           `abi_sz = 32` by simp[abi_member_head_size_def] >>
           `SUC j*abi_sz <= LENGTH vs*abi_sz` by
             (irule LESS_MONO_MULT2 >> decide_tac) >>
           `p+32+j*abi_sz+32 <= L` by
             (qpat_x_assum `SUC j*abi_sz <= _` mp_tac >>
              simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
           `32 <= LENGTH (DROP childpos xs)` by
             metis_tac[abi_valid_dynamic_head_min] >>
           qpat_x_assum `32 <= LENGTH (DROP childpos xs)` mp_tac >>
           simp[Abbr `childpos`, LENGTH_DROP] >> decide_tac) >>
         `child.cs_next_var <= ceiling.cs_next_var /\
          mload (w2n (n2w slot:bytes32)) h = n2w j` by
           simp[w2n_n2w] >>
         qunabbrev_tac `childpos` >>
         metis_tac[abi_valid_allocated_dynamic_setup]) >>
     `eval_operand src h = SOME (n2w p) /\
      eval_operand dst h = SOME (n2w d) /\
      abi_decoder_operand_live setup.cs_next_var src /\
      abi_decoder_operand_live setup.cs_next_var dst` by
       fs[abi_malformed_entry_def, EVERY_DEF] >>
     `child.cs_next_var <= ceiling.cs_next_var /\
      mload (w2n (n2w slot:bytes32)) h = n2w j` by simp[w2n_n2w] >>
     drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
     rename1 `run_inst_seq (emitted_insts setup child) h = OK a` >>
     `stmt_state_rel ctx func cenv cx es h` by fs[abi_malformed_entry_def] >>
     `abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h a` by
       (irule abi_malformed_setup_resource >>
        qhdtm_assum `abi_decode_array_element_setup` (irule_at Any) >> simp[]) >>
     `local_ptrs_reserved cenv child` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `setup` >> simp[]) >>
     qexists_tac `a` >> simp[] >>
     irule abi_malformed_child_entry >>
     qpat_assum `abi_malformed_entry _ _ _ _ _ setup _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qhdtm_assum `abi_malformed_resource_post` (irule_at Any) >>
     `d+outsz < dimword (:256)` by
       fs[abi_malformed_entry_def, abi_malformed_destination_def] >>
     `abi_decoder_operand_live child.cs_next_var base_op /\
      abi_decoder_operand_live child.cs_next_var hi` by
       (fs[abi_malformed_entry_def, EVERY_DEF] >> conj_tac >>
        irule abi_decoder_operand_live_mono >> qexists_tac `setup.cs_next_var` >> simp[]) >>
     `childpos = p+32+j*abi_sz` by simp[Abbr `childpos`] >>
     map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
       [`mem_sz = _`, `childsz = _`, `abi_sz = _`] >>
     fs[Abbr `childpos`] >> decide_tac) >>
  `child.cs_blocks = setup.cs_blocks /\ child.cs_current_bb = setup.cs_current_bb /\
   isPREFIX setup.cs_current_insts child.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts setup child)` by
    (`abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
     Cases_on `dec_info_needs_offset di` >>
     metis_tac[abi_decode_static_element_setup_shape, abi_decode_dynamic_element_setup_shape]) >>
  `inst_extends setup child` by metis_tac[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?b. b = a with vs_inst_idx := LENGTH child.cs_current_insts /\
    b.vs_current_bb = child.cs_current_bb /\
    b.vs_inst_idx = LENGTH child.cs_current_insts /\ abi_decode_sim ctx func h b` by
     (irule abi_decoder_run_sequence_reach >> simp[] >> metis_tac[]) >>
  suspend "child"
QED
Resume abi_valid_allocated_array_iteration[child]:
  markerLib.RESUME_TAC >>
  `~a.vs_halted` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     qpat_x_assum `a = _ with vs_vars := _` (mp_tac o AP_TERM ``\s. s.vs_halted``) >> simp[]) >>
  `abi_valid_allocated_entry ce env sf ty tv (EL j vs) ctx func cenv cx es
     child child_end base_op hi (FST (SND ops)) (SND (SND ops))
     B L xs childpos (d+32+j*mem_sz) dstid live ceiling b` by
    (simp[abi_valid_allocated_entry_def] >>
     conj_tac
     >- (fs[abi_malformed_entry_def, SUBSET_DEF] >> metis_tac[]) >>
     reverse conj_tac >- fs[fresh_vars_wrt_def] >>
     qpat_x_assum `abi_malformed_entry _ _ _ _ _ child _ _ _ _ _ _ _ _ _ _ _ _ _ a` mp_tac >>
     simp[abi_malformed_entry_def, abi_malformed_allocated_window_def,
          abi_malformed_destination_def, stmt_state_rel_inst_idx, eval_operand_def] >>
     strip_tac >> fs[SUBSET_DEF] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  `abi_valid_allocated_array_prefix tv vs j d b` by
    (fs[abi_valid_allocated_array_inv_def, abi_valid_allocated_array_prefix_def]) >>
  qhdtm_assum `abi_valid_allocated_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  `b.vs_allocas = s.vs_allocas` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     qpat_x_assum `a = _ with vs_vars := _`
       (mp_tac o AP_TERM ``\s. s.vs_allocas``) >> simp[]) >>
  `abi_valid_allocated_array_prefix tv vs (SUC j) d u` by
    (irule abi_valid_allocated_array_child_prefix >>
     qpat_x_assum `mem_sz = _` SUBST_ALL_TAC >>
     qhdtm_assum `abi_valid_allocated_frame` (irule_at Any) >>
     `alloca_inv b` by fs[abi_valid_allocated_entry_def, abi_malformed_entry_def, stmt_state_rel_def] >>
     qpat_assum `abi_malformed_entry _ _ _ _ _ start _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     pure_rewrite_tac[abi_malformed_entry_def, abi_malformed_destination_def] >> strip_tac >>
     goal_assum (drule_at Any) >> simp[] >> fs[SUBSET_DEF] >>
     qexistsl_tac [`sz`, `dstid`] >> simp[] >> metis_tac[]) >>
  `eval_operand ip u = SOME (n2w slot) /\
   eval_operand (Var iv) u = SOME (n2w j)` by
    (fs[abi_malformed_resource_post_def] >>
     `eval_operand ip b = SOME (n2w slot) /\
      eval_operand (Var iv) b = SOME (n2w j)` by
       (qpat_x_assum `FST ops = Var iv` (fn th => rewrite_tac[GSYM th]) >>
        Cases_on `ip` >> Cases_on `FST ops` >> fs[eval_operand_def, lookup_var_def]) >>
     metis_tac[]) >>
  suspend "backedge"
QED
Resume abi_valid_allocated_array_iteration[backedge]:
  markerLib.RESUME_TAC >>
  `abi_valid_allocated_effect ctx func cenv cx es setup.cs_next_var
     sites dstid d outsz h b` by
    (`abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h b` by
       (fs[abi_malformed_resource_post_def, stmt_state_rel_inst_idx,
           eval_operand_def, lookup_var_def]) >>
     `b.vs_memory = h.vs_memory /\ b.vs_allocas = h.vs_allocas` by
       (drule_all abi_malformed_setup_frame >> strip_tac >>
        qpat_x_assum `a = _ with vs_vars := _` SUBST_ALL_TAC >> fs[]) >>
     simp[abi_valid_allocated_effect_def, abi_valid_allocated_frame_def]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz h b` by
    (irule abi_valid_allocated_effect_weaken >>
     qhdtm_assum `abi_valid_allocated_effect` (irule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es child.cs_next_var
     sites dstid d outsz b u` by
    (simp[abi_valid_allocated_effect_def] >> conj_tac
     >- metis_tac[abi_malformed_resource_weaken, LESS_EQ_REFL] >>
     `d <= d+32+j*mem_sz` by decide_tac >>
     metis_tac[abi_valid_allocated_frame_weaken]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz b u` by
    (irule abi_valid_allocated_effect_weaken >>
     qhdtm_assum `abi_valid_allocated_effect` (irule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz s u` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `h` >> simp[] >>
     irule abi_valid_allocated_effect_trans >> qexists_tac `b` >> simp[]) >>
  `32+SUC j*type_memory_size tv <= outsz` by
    (`SUC j*type_memory_size tv <= LENGTH vs*type_memory_size tv` by
       (irule LESS_MONO_MULT2 >> decide_tac) >> decide_tac) >>
  drule_all abi_valid_allocated_array_backedge_advance >> strip_tac >>
  `abi_decode_sim ctx func u
     (jump_to hdr (mstore slot (n2w (SUC j))
       (update_var (STRING #"%" (toString next)) (n2w (SUC j)) u)))` by
    (qpat_assum `eval_operand ip u = SOME (n2w slot)`
       (mp_then Any mp_tac abi_decode_backedge_sim) >>
     simp[w2n_n2w] >> disch_then irule >>
     simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func u v` >>
  `abi_decode_sim ctx func s v` by
    (irule abi_decode_sim_trans >> qexists_tac `h` >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule abi_decode_sim_trans >> qexists_tac `b` >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule abi_decode_sim_trans >> qexists_tac `u` >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[frag_outcome_def] >> qexists_tac `v` >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  `~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0` by
    fs[abi_valid_allocated_array_inv_def] >>
  simp[] >> qpat_x_assum `abi_decode_sim ctx func s v` mp_tac >>
  simp[abi_decode_sim_def]
QED
Finalise abi_valid_allocated_array_iteration
