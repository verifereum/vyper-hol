(* Ordinary scratch invariants and pointer ghosts at one concrete loop endpoint. *)
Theory decoderScratchLoopPtr
Ancestors decoderScratchLoopCorePtr decoderLoopControlPtr decoderGhostFramePtr ptrDiscipline abiScratchDecoderLoopInvariant
  abiScratchDecoderLoopControl abiDecoderValidArrayMemory
  abiScratchEffect abiScratchEncoderContract abiDecoderExecution abiDecoderReentry
  abiDecoderValidArrayBackedge abiDecoderContract abiScratchDecoderContract
  abiEncoderArrayFrame abiDecoderAllocation abiDecoderLoop venomState words arithmetic

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem decoder_scratch_header_ptr:
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
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x h = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!x. MEM x [iv;cv;cmp;done] ==>
       op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE) /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u h) ==>
       !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all decoder_scratch_header_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `u`, `h`] >> asm_simp_tac bool_ss []
QED

Theorem decoder_scratch_backedge_ptr:
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
    (!x. x <> nv ==> lookup_var x h = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u h) ==>
       !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all decoder_scratch_backedge_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `u`, `h`] >> asm_simp_tac bool_ss []
QED

(* A recursive child preserves the parent's cursor at its actual endpoint. *)
Theorem decoder_child_cursor_frame_ptr:
  !first last lo hi start limit_st d sz b cap s t site slot q iv
   G tn H u j.
  abi_scratch_effect first last lo hi start.cs_next_var limit_st d sz b cap s t /\
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last /\
  site IN abi_decoder_ids first last /\ ~(site IN abi_decoder_ids lo hi) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  not_fresh_at start q /\ not_fresh_at start iv /\
  (!x. not_fresh_at start x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint u (Var x) = op_taint tn (Var x)) /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  mload slot s = n2w j /\ eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  u.t_mem SUBSET tn.t_mem /\ DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem ==>
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w j /\
  ptr_covers H u q t 32 /\ lookup_var q t = SOME (n2w slot) /\
  eval_operand (Var iv) t = SOME (n2w j) /\
  op_taint u (Var iv) = {} /\ op_prov H (Var iv) = NONE /\
  DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_slot >> strip_tac >>
  `lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
   op_taint u (Var q) = op_taint tn (Var q)` by metis_tac[] >>
  `lookup_var iv t = lookup_var iv s /\ FLOOKUP H iv = FLOOKUP G iv /\
   op_taint u (Var iv) = op_taint tn (Var iv)` by metis_tac[] >>
  `ptr_covers H u q t 32` by
    (drule_at (Pat `ptr_covers _ _ _ _ _`) ptr_covers_frame >>
     disch_then irule >> simp[]) >>
  simp[eval_operand_def, op_prov_def] >>
  fs[eval_operand_def, op_prov_def] >>
  ASM_SET_TAC[]
QED

(* The recursive child and the backedge share the supplied endpoint t. *)
Theorem decoder_scratch_child_backedge_ptr:
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial body_lbl j s /\
  j < LENGTH vs /\ all_have_type tv vs /\
  val_in_memory tv (EL j vs) (d + 32 + j * type_memory_size tv) t.vs_memory /\
  abi_scratch_effect first last child_lo child_hi start.cs_next_var limit_st
    (d + 32 + j * type_memory_size tv) (type_memory_size tv) b cap s t /\
  lo <= child_lo /\ child_hi <= hi /\ next <= start.cs_next_var /\
  first <= site /\ site < last /\ (site < child_lo \/ child_hi <= site) /\
  d + 32 + j * type_memory_size tv + type_memory_size tv <= d + outsz /\
  first <= lo /\ hi <= last /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) hi_op src dst 0 sb (LENGTH bs) d outsz first last b cap s /\
  not_fresh_at start q /\ not_fresh_at start iv /\
  (!x. not_fresh_at start x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint u (Var x) = op_taint tn (Var x)) /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  u.t_mem SUBSET tn.t_mem /\ DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  DISJOINT P tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  nv = STRING #"%" (toString nv_counter) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  t.vs_inst_idx = LENGTH prefix /\ lo <= site /\ site < hi /\
  slot + 32 < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  abi_decoder_operand_live next (Var q) /\ next <= nv_counter /\ nv_counter < limit_st.cs_next_var /\
  allocas_from lower t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  abi_decode_sim ctx fn s t /\
  ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
    !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s) ==>
  ?K v h.
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d outsz slot site
      first last lo hi next limit_st b cap initial hdr (SUC j) h /\
    abi_decode_sim ctx fn s h /\
    h.vs_allocas = t.vs_allocas /\ h.vs_initial_fmp = t.vs_initial_fmp /\ h.vs_fmp = t.vs_fmp /\
    ptr_covers K v q h 32 /\ mload slot h = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot + 32} v.t_mem /\
    DISJOINT P v.t_mem /\ v.t_stor = tn.t_stor /\ v.t_trans = tn.t_trans /\
    (!x. not_fresh_at start x /\ x <> nv ==>
      lookup_var x h = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
      op_taint v (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG K v h) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (calldata_pos abi_scratch_decoder_child_advance) >> strip_tac >>
  `abi_decoder_budget first last b cap s /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ mload slot s = n2w j` by
    fs[abi_scratch_decoder_loop_inv_def, abi_scratch_effect_def, Excl "enc_def"] >>
  `first <= child_lo /\ child_hi <= last` by decide_tac >>
  `abi_footprint_disjoint (d + 32 + j * type_memory_size tv) (type_memory_size tv)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def, cj 1 arithmeticTheory.ADD_CLAUSES]) >>
     irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `outsz`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `site IN abi_decoder_ids first last /\ ~(site IN abi_decoder_ids child_lo child_hi)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all decoder_child_cursor_frame_ptr >> strip_tac >>
  `DISJOINT P u.t_mem` by ASM_SET_TAC[] >>
  `eval_operand (Var q) t = SOME (n2w slot)` by simp[eval_operand_def] >>
  drule_all decoder_scratch_backedge_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `abi_decode_sim ctx fn s h` by
    (irule abi_decode_sim_trans >> qexists_tac `t` >> simp[]) >>
  qpat_x_assum `h = _` kall_tac >>
  qexistsl_tac [`H'`, `u'`, `h`] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED
