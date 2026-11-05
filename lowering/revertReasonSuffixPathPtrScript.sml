(* Composition of the checked ABI suffix. Semantic observations use ordinary
   run endpoints; subsequent pointer checks use counted endpoint cursors. *)
Theory revertReasonSuffixPathPtr
Ancestors
  revertReasonSuffixPtr revertReasonPrefixFramePtr fragGasSeqPtr
  mstoreOperandStep revertReasonLayout exprLoweringProps fragExec bodyPtrDefs revertReasonCopyPtr
  venomMemProps venomState venomInst venomExecSemantics words arithmetic list

Theorem revert_reason_size_cell_checks:
  (FLOOKUP s.vs_allocas (id+5) = NONE ==>
     s.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==>
     sz = 32 /\ a+32 < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst (id+5) ALLOCA [Lit 32w]
     [STRING #"%" (toString ((v:num)+4))]) s = OK sa /\
  run_inst_seq (TAKE 2 (revert_reason_suffix id v b p q)) s = OK t ==>
  ?Gf tnf c.
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (revert_reason_suffix id v b p q)) s Gf tnf /\
    lookup_var (STRING #"%" (toString ((v:num)+4))) t = SOME c /\
    ptr_covers Gf tnf (STRING #"%" (toString ((v:num)+4))) t 32 /\
    mload (w2n c) t = 32w /\
    (!i. w2n c <= i /\ i < w2n c+32 ==> i NOTIN tnf.t_mem) /\
    (!x C. x <> STRING #"%" (toString ((v:num)+4)) /\
       ptr_covers G tn x s C ==>
       lookup_var x t = lookup_var x s /\ ptr_covers Gf tnf x t C)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`id` |-> `id+5`, `n` |-> `32`,
    `out` |-> `STRING #"%" (toString ((v:num)+4))`, `value` |-> `32w`]
      alloca_store_literal_checks)) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `!a sz. _` kall_tac >>
  qpat_x_assum `FLOOKUP _ _ = NONE ==> _` kall_tac >>
  `step_inst_base (mk_inst (id+6) MSTORE
      [Var (STRING #"%" (toString ((v:num)+4))); Lit 32w] []) sa =
      OK (mstore (w2n a) 32w sa)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  `t = mstore (w2n a) 32w sa` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[NoAsms, revert_reason_suffix_def, run_inst_seq_def] >>
     asm_rewrite_tac[] >> simp[NoAsms] >>
     qpat_assum `step_inst_base (mk_inst _ MSTORE _ _) _ = _` SUBST1_TAC >>
     simp[NoAsms]) >>
  qexistsl_tac [`Gf`, `tnf`, `a`] >>
  conj_asm1_tac
  >- fs[revert_reason_suffix_def, ADD_ASSOC] >>
  conj_tac >- fs[lookup_var_def, mstore_def] >>
  conj_tac >- fs[ptr_covers_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- simp[mload_mstore_same] >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  irule inst_seq_ptr_live_pointer_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[revert_reason_suffix_def, mk_inst_def, is_terminator_def]
QED
