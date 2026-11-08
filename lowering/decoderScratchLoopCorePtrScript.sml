(* Joint physical and ghost loop endpoints, including immutable frames. *)
Theory decoderScratchLoopCorePtr
Ancestors decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr decoderGhostFramePtr ptrDiscipline abiScratchDecoderLoopInvariant
  abiScratchDecoderLoopControl abiDecoderValidArrayMemory
  abiScratchEffect abiScratchEncoderContract abiDecoderExecution abiDecoderReentry
  abiDecoderValidArrayBackedge abiDecoderContract venomState words arithmetic

Theorem decoder_scratch_header_ptr_core:
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  first <= lo /\ hi <= last /\
  iv = STRING #"%" (toString first_var) /\
  cv = STRING #"%" (toString (first_var+1)) /\
  cmp = STRING #"%" (toString (first_var+2)) /\
  done = STRING #"%" (toString (first_var+3)) /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid (Var q) src CALLDATALOAD iv cv cmp done /\
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ LENGTH vs < dimword (:256) /\
  slot + 32 < dimword (:256) /\ sb + LENGTH bs < dimword (:256) /\
  next <= first_var /\ first_var + 4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next (Var q) /\
  eval_operand (Var q) initial = SOME (n2w slot) /\
  eval_operand src initial = SOME (n2w sb) /\
  ptr_covers G tn q s 32 /\ DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  op_taint tn src = {} /\ allocas_from lower s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?H u h.
    h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
          (abi_decode_header_state iv cv cmp done j (LENGTH vs) s) /\
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
      first last lo hi next limit_st b cap initial
      (if j < LENGTH vs then body_lbl else exit_lbl) j h /\
    abi_decode_sim ctx fn s h /\
    h.vs_allocas = s.vs_allocas /\
    h.vs_initial_fmp = s.vs_initial_fmp /\ h.vs_fmp = s.vs_fmp /\
    ptr_covers H u q h 32 /\ mload slot h = n2w j /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x h = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!x. MEM x [iv;cv;cmp;done] ==>
       op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE) /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u h) ==>
       !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand src s = SOME (n2w sb)` by
    (fs[abi_scratch_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  drule_all abi_decoder_valid_array_memory_count >> strip_tac >>
  `abi_decode_loop_ready hdr (Var q) src CALLDATALOAD (n2w slot) (n2w sb) (LENGTH vs) j s` by
    fs[abi_decode_loop_ready_def, abi_decoder_valid_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `abi_decoder_operand_live first_var src /\ abi_decoder_operand_live first_var (Var q)` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `src <> Var iv /\ ALL_DISTINCT [q;iv;cv;cmp;done]` by
    (Cases_on `src` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
  qpat_assum `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
  `lookup_var q s = SOME (n2w slot)` by fs[eval_operand_def] >>
  `j <= LENGTH vs` by fs[abi_decode_loop_ready_def] >>
  qpat_x_assum `?bb. lookup_block body_lbl _ = _ /\ _` strip_assume_tac >>
  qpat_x_assum `?bb. lookup_block exit_lbl _ = _ /\ _` strip_assume_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME
     <|bb_label := hdr; bb_instructions :=
       abi_decode_header_insts hid (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|>` by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block s.vs_current_bb fn.fn_blocks = SOME headbb` >>
  `headbb.bb_instructions =
     abi_decode_header_insts hid (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl` by
    simp[Abbr `headbb`] >>
  drule_all decoder_index_header_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `abi_decode_sim ctx fn s t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     irule abi_decode_ready_header_sim >> simp[abi_decode_source_opcode_def] >> metis_tac[]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     asm_simp_tac bool_ss [] >>
     irule abi_scratch_decoder_header_effect >> simp[] >>
     fs[abi_scratch_effect_def, Excl "enc_def"]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial t` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  `abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
     first last lo hi next limit_st b cap initial
     (if j < LENGTH vs then body_lbl else exit_lbl) j t` by
    (pure_rewrite_tac [abi_scratch_decoder_loop_inv_def] >>
     conj_tac >-
       (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
        simp[abi_decode_header_state_def]) >>
     asm_simp_tac bool_ss [] >>
     qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  qexistsl_tac [`H`, `u`, `t`] >> asm_simp_tac bool_ss []
QED

Theorem decoder_scratch_backedge_ptr_core:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  nv = STRING #"%" (toString nv_counter) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  abi_decoder_valid_array_memory CALLDATALOAD bs tv vs sb d (SUC j) s /\ all_have_type tv vs /\
  abi_scratch_effect first last lo hi next limit_st d outsz b cap initial s /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  first <= site /\ site < last /\ lo <= site /\ site < hi /\ first <= lo /\ hi <= last /\
  slot + 32 < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand (Var q) s = SOME (n2w slot) /\
  abi_decoder_operand_live next (Var q) /\ next <= nv_counter /\ nv_counter < limit_st.cs_next_var /\
  ptr_covers G tn q s 32 /\ op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  DISJOINT P tn.t_mem /\ allocas_from lower s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?H u h.
    h = jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) /\
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
      first last lo hi next limit_st b cap initial hdr (SUC j) h /\
    abi_decode_sim ctx fn s h /\
    h.vs_allocas = s.vs_allocas /\ h.vs_initial_fmp = s.vs_initial_fmp /\ h.vs_fmp = s.vs_fmp /\
    ptr_covers H u q h 32 /\ mload slot h = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem /\
    DISJOINT P u.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\ u.t_mem SUBSET tn.t_mem /\
    (!x. x <> nv ==> lookup_var x h = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u h) ==>
       !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `q <> nv` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL]) >>
  `lookup_var q s = SOME (n2w slot)` by fs[eval_operand_def] >>
  drule_all decoder_index_backedge_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s`
    by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  `slot < dimword (:256) /\ abi_decode_source_opcode CALLDATALOAD` by
    simp[abi_decode_source_opcode_def] >>
  `bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
     (STRING #"%" (toString nv_counter)) (Var q) hdr` by metis_tac[] >>
  `(CALLDATALOAD = MLOAD ==> sb + LENGTH bs <= slot \/ slot + 32 <= sb)` by simp[] >>
  drule_all abi_decoder_valid_array_backedge >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  `result_st = t` by metis_tac[] >>
  qpat_x_assum `result_st = t` SUBST_ALL_TAC >>
  `t.vs_halted = s.vs_halted` by metis_tac[] >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s t` by
    (irule abi_scratch_single_write >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`site`, `slot`] >> fs[Excl "enc_def"]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial t` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  `abi_decode_sim ctx fn s t` by
    (qpat_assum `nv = STRING _ _` SUBST_ALL_TAC >>
     qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule abi_decode_backedge_sim >> simp[] >>
     conj_tac >- (qexists_tac `LENGTH vs` >> simp[]) >>
     qexistsl_tac [`id`, `Var q`, `iv`, `prefix`] >> simp[]) >>
  `abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
     first last lo hi next limit_st b cap initial hdr (SUC j) t` by
    asm_simp_tac bool_ss [abi_scratch_decoder_loop_inv_def] >>
  qexistsl_tac [`H`, `u`, `t`] >> asm_simp_tac bool_ss []
QED
