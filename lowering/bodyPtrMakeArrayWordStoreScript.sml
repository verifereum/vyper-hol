(* A clean scalar store initializes a word, without source-pointer coverage. *)
Theory bodyPtrMakeArrayWordStore
Ancestors
  wordLoadStorePtr bodyPtrMakeArrayCopyStep representationCleanPtr robustCopyTransportPtr
  valueEncodingProps valueEncodingProofs valueEncoding valueEncodingDefs bodyPtrDefs venomMemProofs pred_set list

Theorem mstore_raw_robust_word:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  tnf = step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn /\
  mem_agree_outside tnf.t_mem (mstore (w2n a) w s).vs_memory m ==>
  mem_word_at (w2n a) m = w
Proof
  strip_tac >>
  `tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (drule_all mstore_raw_ghost_frame >> simp[]) >>
  `mem_bytes_at (w2n a) 32 m =
   mem_bytes_at (w2n a) 32 (mstore (w2n a) w s).vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
     `w2n a + j NOTIN tnf.t_mem` by simp[] >>
     `mem_bytes_at (w2n a+j) 1 (mstore (w2n a) w s).vs_memory =
      mem_bytes_at (w2n a+j) 1 m` by
       (fs[mem_agree_outside_def] >> metis_tac[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `mem_word_at (w2n a) m =
   mem_word_at (w2n a) (mstore (w2n a) w s).vs_memory` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  metis_tac[mstore_mem_word_at_same]
QED

Theorem mstore_raw_robust_typed_word:
  lookup_var dst s = SOME a /\
  eval_operand value s = SOME (typed_val_to_w256 ty v) /\
  op_taint tn value = {} /\
  ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
   (?k. v = FlagV k) \/ (?n. v = DecimalV n) \/
   (?bs. v = BytesV bs /\
     (ty = BaseTV AddressT \/ ?k. ty = BaseTV (BytesT (Fixed k))))) /\
  tnf = step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) (typed_val_to_w256 ty v) s) tn ==>
  !m. mem_agree_outside tnf.t_mem
    (mstore (w2n a) (typed_val_to_w256 ty v) s).vs_memory m ==>
    val_in_memory ty v (w2n a) m
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `mem_word_at (w2n a) m = typed_val_to_w256 ty v` by
    (irule mstore_raw_robust_word >> metis_tac[]) >>
  gvs[val_in_memory_def, typed_val_to_w256_def] >>
  Cases_on `ty` >> simp[typed_val_to_w256_def] >>
  Cases_on `b` >> simp[typed_val_to_w256_def] >>
  Cases_on `b'` >> simp[typed_val_to_w256_def]
QED

Theorem mstore_raw_robust_frame:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  (!k. k IN op_taint tn value ==> k < 32) /\
  val_wf ty v /\
  (!i. p <= i /\ i < p + val_footprint ty v ==>
       ~(w2n a <= i /\ i < w2n a + 32)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory ty v p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_mem
    (mstore (w2n a) w s).vs_memory m ==>
    val_in_memory ty v p m
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) w s).vs_memory`,
    `tn.t_mem`,
    `(step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_mem`,
    `{i | w2n a <= i /\ i < w2n a + 32}`] >>
  simp[GSYM mem_agree_outside_def, wordLoadStorePtrTheory.mstore_memory_frame] >>
  rpt strip_tac >> irule mstore_raw_outside_taint >> simp[] >> decide_tac
QED

(* Counted-path endpoint used by aggregate prefix extension. *)
Theorem make_array_word_store_endpoint:
  ptr_covers G tn dst s 32 /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MSTORE [Var dst; value] []) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    Gf = G /\ sf = ((mstore (w2n a) w s) with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      sf.vs_memory s.vs_memory /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      mem_word_at (w2n a) m = w) /\
    (!ty v p. val_wf ty v /\
      (!i. p <= i /\ i < p + val_footprint ty v ==>
        ~(w2n a <= i /\ i < w2n a + 32)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ty v p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ty v p m)
Proof
  strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s)`,
    `step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn`,
    `(mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule mstore_raw_ptr_path >> simp[]) >>
  drule_all mstore_raw_ghost_frame >> strip_tac >>
  simp[wordLoadStorePtrTheory.mstore_memory_frame] >>
  conj_tac
  >- (rpt strip_tac >> drule_all mstore_raw_old_coverage >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_raw_robust_word >>
      qexistsl_tac [`dst`, `id`, `s`, `tn`] >> simp[] >>
      qexists_tac `value` >> simp[]) >>
  rpt strip_tac >> irule mstore_raw_robust_frame >> simp[] >>
  qexistsl_tac [`a`, `dst`, `id`, `s`, `tn`, `value`, `w`] >> simp[]
QED
