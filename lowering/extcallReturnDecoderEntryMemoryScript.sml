(* The return allocation and size guard supply the canonical decoder entry. *)
Theory extcallReturnDecoderEntryMemory
Ancestors
  abiDecodeMemTyped extcallReturnTyping exprSimExtCallCase abiBoundaryChecks
  abiDecoderCoherence abiDecoderContract abiDecoderReentry actualDecoderSites
  abiCallerAllocation exprSafeOperand exprLoweringProps loweringStateRelDefs
  exprSimAbiDecodeEntryMetadata exprSimAbiDecodeEntryCoherence
  exprSimHypsDefs emitHelperProps freshWrites compileEnv context exprLowering vyperABI
  valueEncodingDefs valueEncoding vyperState vyperValue vyperAST
  venomState venomMemDefs words list arithmetic finite_map

(* Reuse the canonical quotation, without adding a second HOL definition. *)
val return_entry = fst (dest_conj (fst (dest_imp (concl
  (Q.INST [`env` |-> `get_tenv cx`, `sf` |-> `ce.ce_struct_fields`,
    `ty` |-> `if needs_external_call_wrap rt then TupleT [rt] else rt`,
    `src` |-> `Lit 0w`, `dst` |-> `out`, `base_op` |-> `buf`, `sb` |-> `0`,
    `B` |-> `w2n (ro:bytes32)`, `P` |-> `LENGTH (TAKE cap (data:word8 list))`,
    `H` |-> `LENGTH (TAKE cap (data:word8 list))`,
    `snap` |-> `TAKE cap (data:word8 list)`,
    `keep_word` |-> `\q. F`] abi_decode_typed_scalar_memory)))));

Theorem extcall_return_decoder_entry:
  expr_body_pre ce cx env0
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt) es /\
  rt <> NoneT /\
  extcall_returned ctx func ce cx rt es sa s0 st addr buf cap target
    has def dt opt data ee s /\
  compile_abi_decode_to_buf out (Lit 0w) MLOAD buf hi
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if needs_external_call_wrap rt then TupleT [rt] else rt)) st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  cap = abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap rt then TupleT [rt] else rt) /\
  FLOOKUP s.vs_allocas outid = SOME (d,type_memory_bytes ce rt) /\
  outid < st.cs_next_id /\
  eval_operand buf s = SOME ro /\
  FLOOKUP s.vs_allocas live = SOME (w2n ro,bufsize) /\
  cap <= bufsize /\ live < outid /\
  d + type_memory_bytes ce rt < dimword(:256) /\
  safe_operand st out /\ safe_operand st hi /\ hi <> Lit 0w /\ buf <> Lit 0w /\
  eval_operand out s = SOME (n2w d) /\
  eval_operand hi s = SOME (n2w (MIN (LENGTH data) cap)) /\
  fin.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ?tv. ^return_entry
Proof
  strip_tac >> drule_all extcall_return_decoder_types >> strip_tac >>
  `stmt_state_rel ctx func ce cx ee s` by fs[extcall_returned_def] >>
  drule stmt_state_rel_decode_site_resources >> strip_tac >>
  `type_memory_bytes ce
    (if needs_external_call_wrap rt then TupleT [rt] else rt) =
    type_memory_bytes ce rt` by
    (Cases_on `needs_external_call_wrap rt` >> simp[singleton_tuple_memory_sizes]) >>
  suspend "resources"
QED

Resume extcall_return_decoder_entry[resources]:
  markerLib.RESUME_TAC >>
  `alloca_inv s /\ alloca_room ctx func s /\ fmp_room ctx func s` by
    fs[decode_site_resources_def] >>
  `w2n ro + cap < dimword(:256) /\
   mem_bytes_at (w2n ro) (LENGTH (TAKE cap data)) s.vs_memory = TAKE cap data /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts /\ safe_operand st buf` by
    (fs[extcall_returned_def, EVERY_DEF] >> metis_tac[]) >>
  `LENGTH (TAKE cap data) <= cap` by simp[LENGTH_TAKE_EQ] >>
  `w2n ro + LENGTH (TAKE cap data) <= s.vs_alloca_next` by
    (qpat_x_assum `cap = _` kall_tac >> irule abi_caller_allocation_end >>
     simp[] >> qexistsl_tac [`bufsize`,`live`,`w2n ro`] >> fs[] >> decide_tac) >>
  `w2n ro + bufsize <= d \/ d + type_memory_bytes ce rt <= w2n ro` by
    (irule abi_caller_allocation_separate >>
     simp[] >> qexistsl_tac [`live`,`s`,`outid`] >> simp[] >> decide_tac) >>
  `!id p n. st.cs_next_id <= id /\ id < fin.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (p,n) ==>
    w2n ro + LENGTH (TAKE cap data) <= p \/ p+n <= w2n ro` by
    (rpt strip_tac >>
     `w2n ro+bufsize <= p \/ p+n <= w2n ro` by
       (irule abi_caller_allocation_separate >>
        simp[] >> qexistsl_tac [`live`,`s`,`id`] >> simp[] >> decide_tac) >> decide_tac) >>
  suspend "entry"
QED

Resume extcall_return_decoder_entry[entry]:
  markerLib.RESUME_TAC >>
  `!inst w p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) ==> n = w2n w` by
    fs[decode_site_resources_def] >>
  `EVERY (abi_decoder_operand_live st.cs_next_var) [Lit 0w;out;buf;hi]` by
    (Cases_on `out` >> Cases_on `buf` >> Cases_on `hi` >>
     fs[safe_operand_def, not_fresh_at_def, EVERY_DEF,
       abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `!clamp. type_to_abi_dec_info ce.ce_struct_fields ce
    (if needs_external_call_wrap rt then TupleT [rt] else rt) <> DecPrimWord clamp` by
    (Cases_on `rt` >> simp[needs_external_call_wrap_def, type_to_abi_dec_info_def] >>
     IF_CASES_TAC >> simp[type_to_abi_dec_info_def]) >>
  `w2n ro + LENGTH (TAKE cap data) < dimword(:256)` by decide_tac >>
  `w2n ro + LENGTH (TAKE cap data) <= d \/
   d + type_memory_bytes ce rt <= w2n ro` by decide_tac >>
  `eval_operand hi s = SOME (n2w (LENGTH (TAKE cap data)))` by
    (qpat_assum `eval_operand hi s = SOME (n2w (MIN _ _))` mp_tac >>
     simp[MIN_DEF, LENGTH_TAKE_EQ] >> rpt IF_CASES_TAC >> fs[]) >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  qexists_tac `tv` >> simp_tac bool_ss [LET_THM] >>
  asm_simp_tac (srw_ss()) [EVERY_DEF, eval_operand_def,
    n2w_w2n, decode_site_resources_def] >>
  (rpt conj_tac >> rpt strip_tac
  >~ [`n = w2n w`]
  >- (qpat_x_assum `!inst w p n. _`
        (qspecl_then [`inst`,`w`,`p`,`n`] mp_tac) >> simp[])
  >~ [`?oid root sz. oid < st.cs_next_id /\
    FLOOKUP s.vs_allocas oid = SOME (root,sz) /\ root <= d /\
    d + type_memory_bytes ce rt <= root + sz`]
  >- (qexistsl_tac [`outid`,`d`,`type_memory_bytes ce rt`] >> simp[])
  >~ [`p + n <= w2n ro`]
  >- (qpat_x_assum `!id p n. _` drule_all >> simp[]) >>
  metis_tac[])
QED

Finalise extcall_return_decoder_entry
