(* Traversal whose primitive child contract requires a readable head. *)
Theory abiMalformedConditionalTraversal
Ancestors
  abiMalformedTraversal
  abiMalformedRecursiveInterface abiMalformedNavigation abiMalformedPrefix contractABI abiDecoderLoopEmit
  abiDecoderLoop abiDecoderLoopCode abiDecoderLoopRegisters abiDecoderExecution abiDecoderReentry
  abiDecoderPrimitiveLoopEntry
  abiMalformedPruneState abiDecoderReentryAddress abiDecoderArrayBackedge abiDecoderContract
  exprSimAlloc localPtrsProps venomMemProps venomMemDefs valueEncodingProps
  exprLoweringProps emitHelperProps abiEncoder emitHelper venomInst
  abiDecoderLoopSetup abiDecoderIndexedAddress
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup
  abiDecoderReentryPointer abiDecoderAbortReentry abiDecoderVarExtend
  abiDecoderVarSequence fragExec compileEnv
  venomState venomExecSemantics finite_map pred_set words list arithmetic

Theorem abi_malformed_conditional_traversal_iteration:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin j s /\
  j < n /\ n = abi_head_word (DROP p xs) /\ p+32 <= L /\
  p+32+n*abi_sz <= L /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
  (case di of DecPrimWord clamp =>
    ~is_dynamic (vyper_to_abi_type env ty) /\ abi_sz = 32 | _ => T) /\
  abi_sz < dimword (:256) /\
  d+32+j*mem_sz+childsz <= d+outsz /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  setup.cs_current_bb = body_lbl /\ setup.cs_current_insts = [] /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  FST ops = Var iv /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts bid iv (STRING #"%" (toString next)) ip hdr /\
  fn_inst_ids_distinct func /\ child_sites SUBSET sites /\
  start.cs_next_var <= setup.cs_next_var /\ setup.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  (!cp cd ceiling incoming.
    child_end.cs_next_var <= ceiling.cs_next_var /\
    (case di of DecPrimWord clamp => cp+32 <= L | _ => T) ==>
    frag_exec ctx child child_end
      (\v. v = incoming /\
        abi_malformed_entry ctx func cenv cx es child child_sites dstid live
          base_op hi (FST (SND ops)) (SND (SND ops)) B L xs cp cd childsz v /\
        fresh_vars_wrt ceiling v)
      (\u. abi_malformed_reflected_post env ty
        (if is_dynamic (vyper_to_abi_type env ty) then DROP cp xs else TAKE abi_sz (DROP cp xs))
        ctx func cenv cx es child.cs_next_var child_sites dstid incoming u /\
        fresh_vars_wrt ceiling u)
      (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_outcome ctx func s header
    (abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin (SUC j))
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
      base_op hi src dst B L xs p d outsz s /\
   eval_operand ip s = SOME (n2w slot) /\ mload slot s = n2w j /\
   slot < dimword (:256) /\ fresh_vars_wrt limit_st s` by
    fs[abi_malformed_traversal_inv_def] >>
  `abi_malformed_allocated_window live B L xs s /\
   eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
   abi_decoder_operand_live start.cs_next_var src /\
   abi_decoder_operand_live start.cs_next_var base_op /\
   stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv start` by
    fs[abi_malformed_entry_def] >>
  `?h. abi_decode_sim ctx func s h /\ h.vs_current_bb = body_lbl /\
    h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
    fresh_vars_wrt limit_st h /\ mload slot h = n2w j /\
    abi_malformed_allocated_window live B L xs h` by
    (qsuff_tac `?h. abi_decode_sim ctx func s h /\
       h.vs_current_bb = (if j < n then body_lbl else exit_lbl) /\
       h.vs_inst_idx = 0 /\ ~h.vs_halted /\
       abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
       fresh_vars_wrt limit_st h /\ mload slot h = n2w j /\
       abi_malformed_allocated_window live B L xs h`
     >- simp[] >>
     irule abi_malformed_array_header >> simp[] >>
     reverse conj_tac >- (qexists_tac `start` >> simp[]) >>
     qexistsl_tac [`base_op`, `hid`, `ip`] >>
     qexistsl_tac [`p`, `src`] >> simp[]) >>
  `local_ptrs_reserved cenv setup /\ local_ptrs_reserved cenv child` by
    (conj_tac >> irule local_ptrs_reserved_next_var >>
     qexists_tac `start` >> simp[] >> decide_tac) >>
  `abi_malformed_entry ctx func cenv cx es setup sites dstid live
      base_op hi src dst B L xs p d outsz h /\
   eval_operand ip h = SOME (n2w slot)` by
    (`live NOTIN sites /\ live <> dstid /\
      abi_malformed_destination func cenv es.scopes dstid d outsz s` by
        fs[abi_malformed_entry_def] >>
     drule_all abi_malformed_resource_window >> strip_tac >>
     drule_all abi_malformed_resource_destination >> strip_tac >>
     qpat_x_assum `!cp cd ceiling incoming. _` kall_tac >>
     qhdtm_x_assum `abi_malformed_traversal_inv` kall_tac >>
     fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >>
     `EVERY (abi_decoder_operand_live setup.cs_next_var) [base_op;hi;src;dst]` by
       (fs[EVERY_DEF] >> rpt conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `start.cs_next_var` >> simp[]) >>
     fs[EVERY_DEF]) >>
  qabbrev_tac `off = if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz` >>
  qabbrev_tac `P = \u. abi_malformed_entry ctx func cenv cx es child sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p+32+off) (d+32+j*mem_sz) childsz u /\
    abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand ip u = SOME (n2w slot) /\ fresh_vars_wrt limit_st u` >>
  `abi_decoder_operand_live setup.cs_next_var ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  `(if dec_info_needs_offset di then
      p+32+j*abi_sz+32 <= L /\ abi_sz < dimword (:256)
    else p+32+j*abi_sz < dimword (:256))` by
    (`j*abi_sz+abi_sz <= n*abi_sz` by
       (`SUC j * abi_sz <= n * abi_sz` by
          (irule LESS_MONO_MULT >> decide_tac) >>
        qpat_x_assum `SUC j * abi_sz <= _` mp_tac >>
        simp_tac bool_ss [MULT_CLAUSES, ADD_COMM]) >>
     `B+L < dimword (:256)` by fs[abi_malformed_allocated_window_def] >>
     Cases_on `dec_info_needs_offset di`
     >- (`abi_sz = 32` by metis_tac[] >>
         qpat_x_assum `abi_sz = 32` SUBST_ALL_TAC >>
         simp[] >> decide_tac) >>
     qpat_x_assum `~dec_info_needs_offset di` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `frag_outcome ctx func h child P (\r. ?v. r = Abort Revert_abort v)` by
    (qpat_x_assum `!cp cd ceiling incoming. _` kall_tac >>
     qhdtm_x_assum `abi_malformed_traversal_inv` kall_tac >>
     irule abi_malformed_setup_child >> simp_tac bool_ss [] >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     qexistsl_tac [`childsz`, `j`, `limit_st`] >>
     simp[w2n_n2w] >>
     conj_tac >- fs[fn_has_code_def, emitted_blocks_def] >>
     simp[Abbr `P`] >>
     irule frag_exec_refl >> simp[]) >>
  `LENGTH xs = L` by
    (qhdtm_assum `abi_malformed_allocated_window` mp_tac >>
     simp_tac bool_ss [abi_malformed_allocated_window_def] >> strip_tac >>
     qpat_x_assum `mem_bytes_at B L _.vs_memory = xs` mp_tac >>
     disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def, LENGTH_TAKE, LENGTH_APPEND]) >>
  `abi_reflected_head_ok (vyper_to_abi_type env ty) (DROP (p+32) xs) j /\
   abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j =
     (if is_dynamic (vyper_to_abi_type env ty) then DROP (p+32+off) xs
      else TAKE abi_sz (DROP (p+32+off) xs))` by
    (drule_all abi_malformed_traversal_child_bytes >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[Abbr `off`]) >>
  `n < dimword (:256)` by
    (fs[vyperABITheory.abi_head_word_def, dec_number_def,
         dest_NumV_def, w2n_lt]) >>
  irule abi_malformed_outcome_sim >> qexists_tac `h` >> simp[] >>
  irule frag_outcome_compose >> qexistsl_tac [`P`, `child`] >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `abi_malformed_entry ctx func cenv cx es child child_sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p+32+off) (d+32+j*mem_sz) childsz t /\
   fresh_vars_wrt limit_st t` by
    (fs[Abbr `P`, abi_malformed_entry_def, SUBSET_DEF] >> metis_tac[]) >>
  `case di of DecPrimWord clamp => p+32+off+32 <= L | _ => T` by
    (Cases_on `di` >> fs[Abbr `off`] >>
     `SUC j * 32 <= n * 32` by (irule LESS_MONO_MULT >> decide_tac) >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  qpat_x_assum `!cp cd ceiling incoming. _`
    (qspecl_then [`p+32+off`, `d+32+j*mem_sz`, `limit_st`, `t`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  irule abi_malformed_traversal_child_backedge >>
  simp[] >>
  qexists_tac `\v. v = t` >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) origin j s`)) >>
  goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >> simp[] >>
  qexists_tac `child` >> simp[] >>
  irule frag_exec_conseq >>
  goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >>
  simp[] >>
  conj_tac >- fs[] >>
  qx_gen_tac `u` >> strip_tac >>
  `eval_operand (Var iv) t = SOME (n2w j)` by
    (qpat_assum `P t` mp_tac >> simp_tac bool_ss [Abbr `P`] >>
     strip_tac >> metis_tac[]) >>
  `eval_operand (Var iv) u = SOME (n2w j)` by
    (fs[abi_malformed_reflected_post_def, abi_malformed_resource_post_def] >>
     metis_tac[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid t u` by
    (fs[abi_malformed_reflected_post_def] >>
     irule abi_malformed_resource_weaken >>
     goal_assum (drule_at (Pat `abi_malformed_resource_post _ _ _ _ _ _ _ _ t u`)) >>
     simp[] >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid h t` by
    (irule abi_malformed_resource_weaken >>
     fs[Abbr `P`] >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u` by
    metis_tac[abi_malformed_resource_trans] >>
  fs[abi_malformed_reflected_post_def]
QED

(* Complete traversal reuses the unchanged finite-outcome machinery. *)
Theorem abi_malformed_conditional_traversal:
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\
  slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = prefix ++ [mk_inst entry_id JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] /\
  setup.cs_current_bb = body_lbl /\ setup.cs_current_insts = [] /\
  n = abi_head_word (DROP p xs) /\ p+32 <= L /\ p+32+n*abi_sz <= L /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
  (case di of DecPrimWord clamp =>
    ~is_dynamic (vyper_to_abi_type env ty) /\ abi_sz = 32 | _ => T) /\
  abi_sz < dimword (:256) /\
  (!j. j<n ==> d+32+j*mem_sz+childsz <= d+outsz) /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  FST ops = Var iv /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts bid iv (STRING #"%" (toString next)) ip hdr /\
  fn_inst_ids_distinct func /\ child_sites SUBSET sites /\
  start.cs_next_var <= setup.cs_next_var /\ setup.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  (!cp cd ceiling incoming.
    child_end.cs_next_var <= ceiling.cs_next_var /\
    (case di of DecPrimWord clamp => cp+32 <= L | _ => T) ==>
    frag_exec ctx child child_end
      (\v. v = incoming /\
        abi_malformed_entry ctx func cenv cx es child child_sites dstid live
          base_op hi (FST (SND ops)) (SND (SND ops)) B L xs cp cd childsz v /\
        fresh_vars_wrt ceiling v)
      (\u. abi_malformed_reflected_post env ty
        (if is_dynamic (vyper_to_abi_type env ty) then DROP cp xs else TAKE abi_sz (DROP cp xs))
        ctx func cenv cx es child.cs_next_var child_sites dstid incoming u /\
        fresh_vars_wrt ceiling u)
      (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_outcome ctx func s final
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) n avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
      fresh_vars_wrt limit_st u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `?h. abi_decode_sim ctx func s h /\
    abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n s 0 h /\
    h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\ ~h.vs_halted` by
    (irule abi_malformed_traversal_initial >> simp[] >>
     qexists_tac `entry_id` >> simp[]) >>
  irule abi_malformed_outcome_sim >> qexists_tac `h` >> simp[] >>
  irule abi_malformed_finite_outcome >> conj_tac >- simp[] >>
  qexistsl_tac [`header`,
    `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n s`,
    `0`, `n`] >>
  simp[] >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  qpat_x_assum `abi_sz = _` SUBST_ALL_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule abi_malformed_conditional_traversal_iteration >>
      goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) s k u`)) >>
      simp[] >>
      goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >>
      simp[] >> qexistsl_tac [`child_sites`, `childsz`, `exit_lbl`, `hid`] >>
      simp[] >> conj_tac >- (map_every qx_gen_tac [`pos`, `dest`, `ceil`, `initial`] >> strip_tac >>
        qpat_x_assum `!cp cd ceiling incoming. _`
          (qspecl_then [`pos`, `dest`, `ceil`, `initial`] mp_tac) >> simp[]) >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  qx_gen_tac `last` >> strip_tac >>
  irule abi_malformed_traversal_done >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) s (abi_head_word (DROP p xs)) last`)) >>
  simp[] >> qexistsl_tac [`body_lbl`, `hid`] >> simp[]
QED
