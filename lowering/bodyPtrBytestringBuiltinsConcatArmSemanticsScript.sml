(* Semantic endpoint contracts for Concat's allocation-local writes. *)
Theory bodyPtrBytestringBuiltinsConcatArmSemantics
Ancestors
  exprSimConcatStore exprSimAlloc exprSimProps exprLoweringProps
  compileEnv venomState venomExecSemantics valueEncodingProps valueEncodingProofs
  allocaFootprint abiDecodeStaticProps venomMemProps words arithmetic list finite_map

Theorem concat_fixed_endpoint_state:
  stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv sx /\
  (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (ob,64) /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (ob+64 <= lb \/ lb+lsz <= ob)) /\
  32+k+32 <= bsz /\
  u = (mstore ob nw (mstore (B+32+k) wd t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore (B+32+k) wd t)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`B`,`binst`,`bsz`] >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore ob nw (mstore (B+32+k) wd t))` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`ob`,`oinst`,`64`] >>
     simp[mstore_def, local_region_def, lookup_var_def] >>
     metis_tac[local_region_def, lookup_var_def]) >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_inst_idx] >>
  conj_tac >> rpt strip_tac >>
  `not_fresh_at sx p` by metis_tac[local_ptrs_reserved_def] >>
  simp_tac (srw_ss()) [lookup_var_def, mstore_fields] >>
  first_x_assum irule >> simp[]
QED

Theorem concat_fixed_endpoint_memory:
  LENGTH bs = m /\ m <= 32 /\ 32+k+32 <= bsz /\
  (B+bsz <= ob \/ ob+64 <= B) /\
  u = (mstore ob (n2w (k+m))
    (mstore (B+32+k) (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  mem_bytes_at (B+32) (k+m) u.vs_memory =
    mem_bytes_at (B+32) k t.vs_memory ++ bs /\
  mload ob u = n2w (k+m) /\
  (!p n. (p+n <= B \/ B+bsz <= p) /\
    (p+n <= ob \/ ob+64 <= p) ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (irule concat_fixed_mem >> simp[] >> decide_tac) >>
  conj_tac
  >- (qmatch_goalsub_abbrev_tac `mload ob (s1 with <|vs_vars := V; vs_inst_idx := j|>)` >>
      `mload ob (s1 with <|vs_vars := V; vs_inst_idx := j|>) = mload ob s1` by
        simp[mload_def] >>
      asm_rewrite_tac[] >> simp[Abbr `s1`, mload_mstore_same]) >>
  rpt gen_tac >> disch_tac >> irule EQ_TRANS >>
  qexists_tac `mem_bytes_at p n
    (mstore (B+32+k) (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) t).vs_memory` >>
  conj_tac
  >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem concat_fixed_endpoint_fields:
  (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
  u = (mstore ob nw (mstore a wd t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  u.vs_allocas = t.vs_allocas /\ u.vs_current_bb = t.vs_current_bb /\
  u.vs_halted = t.vs_halted /\ u.vs_inst_idx = j /\
  u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
  u.vs_transient = t.vs_transient /\
  (!z. not_fresh_at sx z ==> lookup_var z u = lookup_var z t)
Proof
  strip_tac >> qpat_x_assum `u = _` SUBST1_TAC >>
  simp[Once abiDecodeStaticPropsTheory.mstore_with_memory] >>
  simp[Once abiDecodeStaticPropsTheory.mstore_with_memory] >>
  simp[lookup_var_def] >>
  ntac 4 (simp[Once abiDecodeStaticPropsTheory.mstore_with_memory])
QED

Theorem concat_bytes_endpoint_state:
  stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv sx /\
  (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (ob,64) /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (ob+64 <= lb \/ lb+lsz <= ob)) /\
  32+k+N <= bsz /\
  u = (mstore ob nw (mcopy (B+32+k) src N t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mcopy (B+32+k) src N t)` by
    (irule alloca_mcopy_state_rel >> simp[] >>
     qexistsl_tac [`B`,`binst`,`bsz`] >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore ob nw (mcopy (B+32+k) src N t))` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`ob`,`oinst`,`64`] >>
     simp[mcopy_def, write_memory_with_expansion_def, local_region_def, lookup_var_def] >>
     metis_tac[local_region_def, lookup_var_def]) >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_inst_idx] >>
  conj_tac >> rpt strip_tac >>
  `not_fresh_at sx p` by metis_tac[local_ptrs_reserved_def] >>
  simp_tac (srw_ss()) [lookup_var_def, mstore_fields] >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem concat_bytes_endpoint_memory:
  mem_bytes_at src (LENGTH bs) t.vs_memory = bs /\
  32+k+LENGTH bs <= bsz /\ (B+bsz <= ob \/ ob+64 <= B) /\
  u = (mstore ob (n2w (k+LENGTH bs))
    (mcopy (B+32+k) src (LENGTH bs) t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory =
    mem_bytes_at (B+32) k t.vs_memory ++ bs /\
  mload ob u = n2w (k+LENGTH bs) /\
  (!p n. (p+n <= B \/ B+bsz <= p) /\
    (p+n <= ob \/ ob+64 <= p) ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `u = _` SUBST1_TAC >> simp_tac (srw_ss()) [] >> conj_tac
  >- (irule concat_bytes_mem >> simp[] >> decide_tac) >>
  conj_tac
  >- (qmatch_goalsub_abbrev_tac `mload ob (s1 with <|vs_vars := V; vs_inst_idx := j|>)` >>
      `mload ob (s1 with <|vs_vars := V; vs_inst_idx := j|>) = mload ob s1` by
        simp[mload_def] >>
      asm_rewrite_tac[] >> simp[Abbr `s1`, mload_mstore_same]) >>
  rpt gen_tac >> disch_tac >> irule EQ_TRANS >>
  qexists_tac `mem_bytes_at p n (mcopy (B+32+k) src (LENGTH bs) t).vs_memory` >>
  conj_tac
  >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule valueEncodingProofsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem concat_bytes_endpoint_fields:
  (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
  u = (mstore ob nw (mcopy a src N t) with
    <|vs_vars := V; vs_inst_idx := j|>) ==>
  u.vs_allocas = t.vs_allocas /\ u.vs_current_bb = t.vs_current_bb /\
  u.vs_halted = t.vs_halted /\ u.vs_inst_idx = j /\
  u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
  u.vs_transient = t.vs_transient /\
  (!z. not_fresh_at sx z ==> lookup_var z u = lookup_var z t)
Proof
  strip_tac >> qpat_x_assum `u = _` SUBST1_TAC >>
  ntac 4 (simp[Once abiDecodeStaticPropsTheory.mstore_with_memory]) >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED
