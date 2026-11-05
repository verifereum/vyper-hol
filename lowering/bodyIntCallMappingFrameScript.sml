Theory bodyIntCallMappingFrame
Ancestors
  exprSimHash bodyIntCallSemanticFrame exprLowering exprLoweringProps
  valueEncodingProps valueEncodingProofs vyperStorage venomExecSemantics
  byte words emitHelper emitHelperProps compileEnv venomInst venomState context list
  abiDecodeStaticProps valueEncoding

(* The scratch layout is base-slot first, then the already encoded key. *)
Theorem mapping_scratch_bytes:
  mem_bytes_at a 64 (mstore (a + 32) key (mstore a slot s)).vs_memory =
    word_to_bytes_be slot ++ word_to_bytes_be key
Proof
  rewrite_tac[GSYM (EVAL ``32 + 32:num``)] >>
  rewrite_tac[mem_bytes_at_split_padded] >>
  simp[mstore_mem_bytes_at_disjoint, mem_bytes_at_mstore_same,
       word_to_bytes_be_def]
QED

Theorem mapping_scratch_hash:
  word_of_bytes T (0w:bytes32)
    (Keccak_256_w64
      (mem_bytes_at a 64 (mstore (a + 32) key (mstore a slot s)).vs_memory)) =
  hashmap_slot slot key
Proof
  simp[mapping_scratch_bytes, hashmap_slot_def, word_of_bytes_be_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping scratch bytes have unproved dependencies"
  end) [mapping_scratch_bytes, mapping_scratch_hash];

Theorem mapping_hash_tail_run:
  !ptr base key sa s1 kp s2 s3 out sb s addr slot kw.
  emit_void MSTORE [ptr; base] sa = ((),s1) /\
  emit_op ADD [ptr; Lit 32w] s1 = (kp,s2) /\
  emit_void MSTORE [kp; key] s2 = ((),s3) /\
  emit_op SHA3 [ptr; Lit 64w] s3 = (out,sb) /\
  eval_operand ptr s = SOME addr /\ eval_operand base s = SOME slot /\
  eval_operand key s = SOME kw /\ w2n addr + 64 < dimword (:256) /\
  (!x. ptr = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (hashmap_slot slot kw) /\
    t.vs_memory = (mstore (w2n addr + 32) kw (mstore (w2n addr) slot s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_write2_def] >>
  rename1 `eval_operand pop s = SOME addr` >>
  `eval_operand pop (mstore (w2n addr) slot s) = SOME addr` by
    metis_tac[eval_operand_mstore] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ mid` >>
  `eval_operand key mid = SOME kw` by
    (Cases_on `key` >>
     gvs[Abbr `mid`, eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  `eval_operand pop mid = SOME addr` by
    (Cases_on `pop` >>
     gvs[Abbr `mid`, eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
       eval_operand_def, Abbr `mid`, lookup_var_update_var] >>
  `w2n (addr + 32w) = w2n addr + 32` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ stored` >>
  `eval_operand pop stored = SOME addr` by
    (simp[Abbr `stored`] >> metis_tac[eval_operand_mstore]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       GSYM mem_bytes_at_def] >>
  `stored.vs_memory =
    (mstore (w2n addr + 32) kw (mstore (w2n addr) slot s)).vs_memory` by
    (simp_tac (srw_ss()) [Abbr `stored`] >>
     asm_simp_tac (srw_ss()) [mstore_def, update_var_def, LET_THM]) >>
  simp[run_inst_seq_def, mapping_scratch_hash, lookup_var_update_var] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >-
    simp_tac (srw_ss()) [Abbr `stored`, mstore_def, update_var_def, LET_THM] >>
  rpt strip_tac >>
  qpat_x_assum `not_fresh_at sa x` mp_tac >>
  simp[not_fresh_at_def] >> strip_tac >>
  first_assum (qspec_then `sa.cs_next_var` mp_tac) >>
  first_x_assum (qspec_then `sa.cs_next_var + 1` mp_tac) >>
  simp[] >> rpt strip_tac >>
  simp_tac (srw_ss()) [Abbr `stored`, lookup_var_def, update_var_def,
                      mstore_def, LET_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

val () =
  let val th = mapping_hash_tail_run
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Mapping hash tail has unproved dependencies"
  end;
