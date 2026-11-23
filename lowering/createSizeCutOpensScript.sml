(* A lower bound on the block openings of a compiler action. *)
Theory createSizeCutOpens
Ancestors
  createSizeCutCode externalEntryShape exprLowering exprCallBounds context
  emitHelper compileEnv vyperAST list pair pred_set

Theorem create_cut_code_weaken:
  create_cut_code exits a b /\ exits SUBSET more ==>
  create_cut_code more a b
Proof
  simp[create_cut_code_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem create_cut_code_widen_empty:
  create_cut_code {} a b ==> create_cut_code exits a b
Proof
  strip_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]
QED

(* A symbolic continuation keeps earlier states out of the remaining code. *)
Theorem create_cut_code_bind_all:
  create_cut_code exits a (SND (m a)) /\
  (!v s. create_cut_code exits s (SND (k v s))) ==>
  create_cut_code exits a (SND (comp_bind m k a))
Proof
  strip_tac >> irule create_cut_code_bind >> simp[]
QED

Theorem create_cut_code_bind_uniform:
  (!s. create_cut_code exits s (SND (m s))) /\
  (!v s. create_cut_code exits s (SND (k v s))) ==>
  create_cut_code exits a (SND (comp_bind m k a))
Proof
  strip_tac >> irule create_cut_code_bind_all >> simp[]
QED

Theorem create_cut_code_pair:
  create_cut_code exits a (SND p) /\
  create_cut_code exits (SND p) (SND (k (FST p) (SND p))) ==>
  create_cut_code exits a (SND (UNCURRY k p))
Proof
  simp[UNCURRY_VAR] >> metis_tac[create_cut_code_join]
QED

Theorem create_alloc_buffer_cut_code:
  create_cut_code exits a (SND (compile_alloc_buffer n a))
Proof
  rw[compile_alloc_buffer_def] >> irule create_cut_code_bind >>
  simp[create_cut_code_emit_op, create_cut_targets_def]
QED

Theorem create_cut_copy_memory:
  create_cut_code exits a (SND (compile_copy_memory dst src n a))
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, create_cut_code_emit_void,
                       create_cut_targets_def]
QED

Theorem create_cut_guarded_expr:
  (!ty e a. expr_size e + cenv_defaults_size ce < bound ==>
           create_cut_code {} a (SND (f ce ty e a))) ==>
  !ty e a. create_cut_code {} a (SND (expr_child_callback bound f ce ty e a))
Proof
  rpt strip_tac >>
  Cases_on `expr_size e + cenv_defaults_size ce < bound` >>
  simp[expr_child_callback_def, invalid_expr_call_def, LET_DEF, UNCURRY_VAR,
       create_cut_code_emit_inst, create_cut_targets_def]
QED

Theorem create_cut_opens_join:
  !b. (create_cut_code exits a b /\ opened1 SUBSET set (added_labels a b)) /\
  (create_cut_code exits b c /\ opened2 SUBSET set (added_labels b c)) ==>
  create_cut_code exits a c /\
  (opened1 UNION opened2) SUBSET set (added_labels a c)
Proof
  rpt strip_tac
  >- metis_tac[create_cut_code_join] >>
  `cs_extends a b /\ cs_extends b c` by fs[create_cut_code_def] >>
  drule_all added_labels_trans >> simp[SUBSET_DEF] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem create_cut_opens_prepend:
  !b. create_cut_code exits a b /\
  (create_cut_code exits b c /\ opened SUBSET set (added_labels b c)) ==>
  create_cut_code exits a c /\ opened SUBSET set (added_labels a c)
Proof
  mp_tac (Q.INST [`opened1` |-> `{}`, `opened2` |-> `opened`]
                 create_cut_opens_join) >> simp[]
QED

Theorem create_cut_opens_new_block:
  new_block l a = (x,b) ==>
  create_cut_code exits a b /\ {l} SUBSET set (added_labels a b)
Proof
  strip_tac >> conj_tac
  >- metis_tac[create_cut_code_new_block, SND] >>
  drule added_labels_new_block >> simp[]
QED

Theorem create_cut_opens_block:
  create_cut_code exits a (SND (new_block l a)) /\
  {l} SUBSET set (added_labels a (SND (new_block l a)))
Proof
  Cases_on `new_block l a` >> drule create_cut_opens_new_block >> simp[]
QED

Theorem create_cut_lower_value:
  (!ty e a. create_cut_code {} a (SND (f ce ty e a))) /\
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) ==>
  !ty e a. create_cut_code {} a (SND (lower_value f ce ty e a))
Proof
  rpt strip_tac >> simp[lower_value_def, Excl "expr_child_callback_def"] >>
  irule create_cut_code_bind >> simp[]
QED

Theorem create_cut_opens_close:
  (create_cut_code pending a b /\ opened SUBSET set (added_labels a b)) /\
  pending SUBSET (exits UNION opened) ==>
  create_cut_code exits a b
Proof
  strip_tac >> irule create_cut_code_close >>
  qexists_tac `pending` >> fs[SUBSET_DEF] >> metis_tac[]
QED

(* Composition rules for opaque actions interleaved with block openings. *)
Theorem create_cut_opens_bind:
  (create_cut_code exits a (SND (m a)) /\
    opened1 SUBSET set (added_labels a (SND (m a)))) /\
  (create_cut_code exits (SND (m a)) (SND (k (FST (m a)) (SND (m a)))) /\
    opened2 SUBSET set (added_labels (SND (m a))
                                       (SND (k (FST (m a)) (SND (m a)))))) ==>
  create_cut_code exits a (SND (comp_bind m k a)) /\
  (opened1 UNION opened2) SUBSET set (added_labels a (SND (comp_bind m k a)))
Proof
  Cases_on `m a` >>
  asm_rewrite_tac[comp_bind_def, pair_case_thm, FST, SND] >>
  strip_tac >> match_mp_tac create_cut_opens_join >> qexists_tac `r` >> simp[]
QED

Theorem create_cut_opens_bind_keep:
  (!s. create_cut_code exits s (SND (m s))) /\
  (!v s. create_cut_code exits s (SND (k v s)) /\
         opened SUBSET set (added_labels s (SND (k v s)))) ==>
  create_cut_code exits a (SND (comp_bind m k a)) /\
  opened SUBSET set (added_labels a (SND (comp_bind m k a)))
Proof
  strip_tac >>
  mp_tac (Q.INST [`opened1` |-> `{}`, `opened2` |-> `opened`]
                  create_cut_opens_bind) >> simp[]
QED

Theorem create_cut_emit_eq[local]:
  emit_inst opc ops outs a = (x,b) ==>
  !exits. (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
    create_cut_code exits a b
Proof
  metis_tac[create_cut_code_emit_inst, SND]
QED

Theorem create_cut_opaque_loop:
  emit_inst JMP [Label h_lbl] [] a = ((),a1) /\
  new_block h_lbl a1 = (old_head,a2) /\
  create_cut_code {} a2 a3 /\
  emit_inst JNZ [cond; Label x_lbl; Label b_lbl] [] a3 = ((),a4) /\
  new_block b_lbl a4 = (old_body,a5) /\
  create_cut_code {} a5 a6 /\
  emit_inst JMP [Label h_lbl] [] a6 = ((),a7) /\
  new_block x_lbl a7 = (old_exit,b) ==>
  create_cut_code {} a b
Proof
  strip_tac >>
  qabbrev_tac `pending = {h_lbl;b_lbl;x_lbl}` >>
  `create_cut_code pending a a1 /\ create_cut_code pending a6 a7` by
    (conj_tac
     >- (qpat_assum `emit_inst JMP _ [] a = _` (qspec_then `pending` mp_tac o MATCH_MP create_cut_emit_eq) >>
         simp[create_cut_targets_def, Abbr `pending`]) >>
     qpat_assum `emit_inst JMP _ [] a6 = _` (qspec_then `pending` mp_tac o MATCH_MP create_cut_emit_eq) >>
     simp[create_cut_targets_def, Abbr `pending`]) >>
  `create_cut_code pending a3 a4` by
    (qpat_assum `emit_inst JNZ _ [] a3 = _`
       (qspec_then `pending` mp_tac o MATCH_MP create_cut_emit_eq) >>
     simp[create_cut_targets_def, Abbr `pending`, DISJ_IMP_THM]) >>
  `create_cut_code pending a2 a3 /\ create_cut_code pending a5 a6` by
    (conj_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  `create_cut_code pending a1 a2 /\ {h_lbl} SUBSET set (added_labels a1 a2)` by
    metis_tac[create_cut_opens_new_block] >>
  `create_cut_code pending a4 a5 /\ {b_lbl} SUBSET set (added_labels a4 a5)` by
    metis_tac[create_cut_opens_new_block] >>
  `create_cut_code pending a7 b /\ {x_lbl} SUBSET set (added_labels a7 b)` by
    metis_tac[create_cut_opens_new_block] >>
  `create_cut_code pending a b /\
   ({h_lbl} UNION ({b_lbl} UNION {x_lbl})) SUBSET set (added_labels a b)` by
    (match_mp_tac create_cut_opens_prepend >> qexists_tac `a1` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_join >> qexists_tac `a2` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_prepend >> qexists_tac `a3` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_prepend >> qexists_tac `a4` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_join >> qexists_tac `a5` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_prepend >> qexists_tac `a6` >>
     (conj_tac >- simp[]) >>
     match_mp_tac create_cut_opens_prepend >> qexists_tac `a7` >> simp[]) >>
  irule create_cut_opens_close >>
  qexistsl_tac [`{h_lbl} UNION ({b_lbl} UNION {x_lbl})`, `pending`] >>
  simp[Abbr `pending`, SUBSET_DEF]
QED
