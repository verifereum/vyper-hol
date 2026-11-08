Theory abiDecodePtrBytesTailWindow
Ancestors
  abiDecodePtrBytesTail abiDecodePtrMemberFrame abiEncoderRounding
  vyperTypeABI contractABI bodyPtrDefs ptrDiscipline emitHelperProps
  venomExecSemantics venomState compileEnv context words arithmetic

Theorem abi_decode_bytes_runtime_tail_windows:
  abi_decode_bytes_runtime_tail (Var dst) (Var ar) cnt sa = ((),sb) /\
  abi_decode_ptr_window G tn s src (n2w b) h /\
  abi_decode_ptr_window G tn s ar (n2w (b+p)) (32+c) /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  eval_operand cnt s = SOME (n2w c) /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa ar /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  c <= n /\ p+32+c <= h /\ n+31 < dimword(:256) /\
  32+contractABI$ceil32 n <= cap /\ d+cap < dimword(:256) /\
  b+h < dimword(:256) /\ (b+h <= d \/ d+cap <= b) /\
  fresh_vars_wrt sa s /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    abi_decode_ptr_window Gf tnf t src (n2w b) h /\
    abi_decode_ptr_window Gf tnf t dst (n2w d) (32+contractABI$ceil32 c) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!i. ~(d <= i /\ i < d+32+contractABI$ceil32 c) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `contractABI$ceil32 c <= contractABI$ceil32 n` by
    (irule ceil32_mono >> first_assum ACCEPT_TAC) >>
  `c+31 < dimword(:256) /\ 32+c < dimword(:256) /\
   32+32*((c+31) DIV 32) <= cap /\ b+p < dimword(:256)` by
    (fs[contractABITheory.ceil32_def] >> decide_tac) >>
  SUBGOAL_THEN ``b+p+32+c <= d \/ d+cap <= b+p`` assume_tac
    >- decide_tac >>
  drule_all abi_decode_bytes_runtime_tail_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  suspend "windows"
QED

Resume abi_decode_bytes_runtime_tail_windows[windows]:
  `b < dimword(:256) /\ d < dimword(:256) /\
   32+contractABI$ceil32 c <= cap` by decide_tac >>
  `!i. b <= i /\ i < b+h ==>
       ~(d <= i /\ i < d+32+32*((c+31) DIV 32))` by
    (fs[contractABITheory.ceil32_def] >> decide_tac) >>
  `abi_decode_ptr_window Gf tnf t src (n2w b) h` by
    (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[]) >>
  `lookup_var dst t = SOME (n2w d) /\ ptr_covers Gf tnf dst t cap` by
    (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> conj_tac >- simp[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `abi_decode_ptr_window Gf tnf t dst (n2w d) (32+contractABI$ceil32 c)` by
    (simp[abi_decode_ptr_window_def] >> conj_tac >-
       (qpat_assum `ptr_covers Gf tnf dst t cap` mp_tac >>
        rewrite_tac[ptr_covers_def] >> strip_tac >> simp[]) >>
     simp[contractABITheory.ceil32_def]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[contractABITheory.ceil32_def]
QED

Finalise abi_decode_bytes_runtime_tail_windows
