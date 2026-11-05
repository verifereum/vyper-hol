(* Counted memory-safe SHA256 suffixes. Semantic facts are reused from the
   task-permitted S1 overlay; all memory checks are proved here. *)
Theory bodyMemBiSha256Compose
Ancestors
  bodyMemBiSha256Suffix exprSimHash exprSimMemDefs allocaHistoryFragment
  fragGasSeqMem exprSimProps exprLoweringProps exprOperandVar exprSimWordArgs
  venomMemDefs compileEnv vyperTypeSystem

Theorem sha256_typed_suffix_mem_ok:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  expr_store_bound cx (expr_type e) v x s ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def]
      >- ( `n <= 32` by (fs[vyperValueTheory.evaluate_type_def] >> gvs[AllCaseEqs()]) >>
           drule_all hash_fixed_post_view >> strip_tac >>
           irule compile_sha256_bytesm_mem_ok >>
           simp[] >>
           reverse conj_tac >- (qexistsl [`n`,`op`,`w`,`x`] >> simp[]) >>
           drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >> strip_tac >>
           fs[stmt_state_rel_def] >>
           rpt gen_tac >> strip_tac
           >- (qpat_x_assum `!inst n base sz. _` (fn coh =>
                 qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _`
                   (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
                     [venomInstTheory.mk_inst_def]) coh)) >>
               disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
               gvs[wordsTheory.dimword_def]) >>
           qpat_x_assum `!inst n base sz. _` (fn coh =>
             qpat_assum `MEM (mk_inst (sm.cs_next_id + 2) ALLOCA _ _) _`
               (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
                 [venomInstTheory.mk_inst_def]) coh)) >>
           disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
           gvs[wordsTheory.dimword_def]) >>
      drule hash_dynamic_post_view >> simp[] >> strip_tac >>
      `b < dimword (:256)` by decide_tac >>
      `b + 32 + LENGTH l <= s.vs_alloca_next` by
        (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
         simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
         qspec_then `LENGTH l` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
         decide_tac) >>
      irule compile_sha256_bytes_mem_ok >>
      simp[] >>
      reverse conj_tac
      >- (qexistsl [`b`,`LENGTH l`,`op`,`x`] >> simp[] >> decide_tac) >>
      suspend "memory_capacity") >>
  drule hash_string_post_view >> simp[] >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `b + 32 + LENGTH s' <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
     qspec_then `LENGTH s'` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     decide_tac) >>
  irule compile_sha256_bytes_mem_ok >> simp[] >>
  reverse conj_tac
  >- (qexistsl [`b`,`LENGTH s'`,`op`,`x`] >> simp[] >> decide_tac) >>
  suspend "memory_capacity"
QED

Resume sha256_typed_suffix_mem_ok[memory_capacity]:
  markerLib.RESUME_TAC >>
  drule_all hash_sha256_memory_alloca_code >> strip_tac >>
  fs[stmt_state_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!inst n base sz. _` (fn coh =>
    qpat_assum `MEM (mk_inst (sm.cs_next_id + 2) ALLOCA _ _) _`
      (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
        [venomInstTheory.mk_inst_def]) coh)) >>
  disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
  gvs[wordsTheory.dimword_def]
QED

Finalise sha256_typed_suffix_mem_ok
