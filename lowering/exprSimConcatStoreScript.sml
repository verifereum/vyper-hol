(* Concat case: stores into the concat buffer keep the state relation. *)
Theory exprSimConcatStore
Ancestors
  valueEncodingDefs arithmetic list compileEnv loweringStateRelDefs exprLoweringProps localPtrsProps loweringSlice
  immutableMemoryFrame valueEncodingProps valueEncodingProofs venomState
  venomExecSemantics byte

(* An MCOPY whose destination lies inside one tracked ALLOCA, disjoint from
   every live local, keeps stmt_state_rel; the MSTORE counterpart is
   literal_mstore_state_rel. *)
Theorem alloca_mcopy_state_rel:
  !ctx func cenv cx es s inst b sz d src n.
    stmt_state_rel ctx func cenv cx es s /\ b <= d /\ d + n <= b + sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b) ==>
    stmt_state_rel ctx func cenv cx es (mcopy d src n s)
Proof
  rpt strip_tac >>
  `(mcopy d src n s with vs_memory := s.vs_memory) = s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  `!q. lookup_var q (mcopy d src n s) = lookup_var q s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def] >>
  `!nm lo len. local_region cenv es.scopes (mcopy d src n s) nm lo len <=>
               local_region cenv es.scopes s nm lo len` by
    simp[local_region_def] >>
  `LENGTH s.vs_memory <= LENGTH (mcopy d src n s).vs_memory` by
    simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF] >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  rewrite_tac[Once stmt_state_rel_def] >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes (mcopy d src n s)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`mem_bytes_at _ _ (mcopy _ _ _ _).vs_memory`]
     >- (rpt strip_tac >> rename1 `local_region _ _ _ nm lo len` >>
         `lo + len <= d \/ d + n <= lo` by
           (qpat_x_assum `!name lb lsz. local_region _ _ s _ _ _ ==> _` drule >>
            decide_tac) >>
         simp[mcopy_mem_bytes_at_disjoint]) >>
     rpt strip_tac >> gvs[state_rel_def, mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mcopy d src n s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     reverse conj_tac >- gvs[state_rel_def] >>
     rpt strip_tac >>
     qpat_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     rewrite_tac[immutable_alloca_sep_def] >>
     disch_then (drule_all o CONJUNCT2) >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
     irule mcopy_mem_bytes_at_disjoint >> gvs[regions_disjoint_def]) >>
  rewrite_tac[stmt_state_rel_def] >>
  conj_tac
  >- (irule state_rel_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s` >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
      rpt strip_tac >> qexists_tac `id` >>
      gvs[local_region_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  first_assum MATCH_ACCEPT_TAC
QED

(* After a bytesM operand's full-word store at D + k and the offset store at
   ob (outside the grown window), the window [D, D + k + LENGTH bs) holds the
   old prefix followed by the operand's bytes. *)
Theorem concat_fixed_mem:
  !D k bs ob x s.
    LENGTH bs <= 32 /\ (D + (k + LENGTH bs) <= ob \/ ob + 32 <= D) ==>
    mem_bytes_at D (k + LENGTH bs)
      (mstore ob x (mstore (D + k) (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) s)).vs_memory =
    mem_bytes_at D k s.vs_memory ++ bs
Proof
  rpt strip_tac >>
  qabbrev_tac `wd = word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32` >>
  qabbrev_tac `mm = (mstore (D + k) wd s).vs_memory` >>
  `mem_bytes_at D (k + LENGTH bs) (mstore ob x (mstore (D + k) wd s)).vs_memory =
   mem_bytes_at D (k + LENGTH bs) mm` by
    (qunabbrev_tac `mm` >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >> rewrite_tac[mem_bytes_at_split_padded] >>
  `mem_bytes_at D k mm = mem_bytes_at D k s.vs_memory` by
    (qunabbrev_tac `mm` >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  `mem_bytes_at (D + k) (LENGTH bs + (32 - LENGTH bs)) mm = word_to_bytes wd T` by
    (`LENGTH bs + (32 - LENGTH bs) = 32` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[Abbr `mm`, mem_bytes_at_mstore_same]) >>
  pop_assum mp_tac >> rewrite_tac[mem_bytes_at_split_padded] >> strip_tac >>
  `mem_bytes_at (D + k) (LENGTH bs) mm = TAKE (LENGTH bs) (word_to_bytes wd T)` by
    (pop_assum (SUBST1_TAC o SYM) >>
     simp[rich_listTheory.TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr `wd`, word_of_bytes_be_pad_right, GSYM byteTheory.word_to_bytes_be_def,
       TAKE_word_to_bytes_be_word_of_bytes_be]
QED

(* After a bytestring operand's MCOPY of its payload to D + k and the offset
   store at ob (outside the grown window), the window holds the old prefix
   followed by the payload. *)
Theorem concat_bytes_mem:
  !D k src bs ob x s.
    mem_bytes_at src (LENGTH bs) s.vs_memory = bs /\
    (D + (k + LENGTH bs) <= ob \/ ob + 32 <= D) ==>
    mem_bytes_at D (k + LENGTH bs)
      (mstore ob x (mcopy (D + k) src (LENGTH bs) s)).vs_memory =
    mem_bytes_at D k s.vs_memory ++ bs
Proof
  rpt strip_tac >>
  `mem_bytes_at D (k + LENGTH bs)
     (mstore ob x (mcopy (D + k) src (LENGTH bs) s)).vs_memory =
   mem_bytes_at D (k + LENGTH bs) (mcopy (D + k) src (LENGTH bs) s).vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >> rewrite_tac[mem_bytes_at_split_padded] >>
  simp[mcopy_mem_bytes_at_same, mcopy_mem_bytes_at_disjoint]
QED
