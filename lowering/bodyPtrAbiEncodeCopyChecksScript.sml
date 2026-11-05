(* Fixed-copy encoder checks include empty windows without allocation. *)
Theory bodyPtrAbiEncodeCopyChecks
Ancestors
  bodyPtrAbiEncodePrimitive abiEncoderLeaves emitHelperProps
  fragExecPtr typedCopyPtr fragGasSeqPtr fragGasPathPtr
  venomExecSemantics venomInst venomState ptrDiscipline words

Theorem abi_encode_copy_emitted_checks:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy sz) st = (out,st') /\
  sz < dimword (:256) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx /\
  (0 < sz ==> ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz) ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    Gf = G /\ tnf.t_var = tn.t_var /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + sz}) UNION
      {w2n b + i | i < sz /\ w2n a + i IN tn.t_mem}
Proof
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] []) s` by
    (Cases_on `sz = 0`
     >- (simp[] >> irule ptr_inst_ok_mcopy_zero >> simp[eval_operand_def] >> metis_tac[]) >>
     irule ptr_inst_ok_mcopy >> simp[w2n_n2w]) >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a /\
   eval_operand (Lit (n2w sz)) s = SOME (n2w sz:bytes32)` by simp[eval_operand_def] >>
  `step_prov PG G (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] [])
       (mcopy (w2n b) (w2n a) (w2n (n2w sz:bytes32)) s) = G /\
   (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] []) s
       (mcopy (w2n b) (w2n a) (w2n (n2w sz:bytes32)) s) tn).t_var = tn.t_var /\
   (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] []) s
       (mcopy (w2n b) (w2n a) (w2n (n2w sz:bytes32)) s) tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] []) s
       (mcopy (w2n b) (w2n a) (w2n (n2w sz:bytes32)) s) tn).t_trans = tn.t_trans /\
   (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;Var src;Lit (n2w sz)] []) s
       (mcopy (w2n b) (w2n a) (w2n (n2w sz:bytes32)) s) tn).t_mem =
     (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n (n2w sz:bytes32)}) UNION
       {w2n b+i | i < w2n (n2w sz:bytes32) /\ w2n a+i IN tn.t_mem}` by
    (irule mcopy_operand_ghost_frame >> simp[eval_operand_def]) >>
  fs[w2n_n2w] >>
  simp[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
  asm_rewrite_tac[GSYM mk_inst_def] >> gvs[]
QED

Theorem abi_encode_copy_emitted_clean_checks:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy sz) st = (out,st') /\
  sz < dimword (:256) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx /\
  (0 < sz ==> ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz) /\
  (!i. w2n a <= i /\ i < w2n a + sz ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    Gf = G /\ tnf.t_var = tn.t_var /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + sz}
Proof
  strip_tac >> drule_all abi_encode_copy_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[] >>
  `{w2n b+i | i < sz /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[pred_setTheory.EXTENSION] >> rpt strip_tac >>
     first_x_assum (qspec_then `w2n a+i` mp_tac) >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem abi_encode_copy_checked_ptr_path:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy sz) st = (out,st') /\
  eval_operand (Var src) s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx /\
  (0 < sz ==> ptr_covers G tn src s sz /\ ptr_covers G tn dst s sz) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
      Gf tnf (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    eval_operand out t = SOME (n2w sz) /\
    mem_bytes_at db sz t.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    fresh_vars_wrt limit_st t /\ Gf = G /\ tnf.t_var = tn.t_var /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_mem = (tn.t_mem DIFF {i | db <= i /\ i < db + sz}) UNION
      {db+i | i < sz /\ sb+i IN tn.t_mem}
Proof
  strip_tac >>
  `lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db)` by
    fs[eval_operand_def] >>
  drule_all abi_encode_copy_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all abi_encode_copy_reentry_ptr_path >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[w2n_n2w]
QED
