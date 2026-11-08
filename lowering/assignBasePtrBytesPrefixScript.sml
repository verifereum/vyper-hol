(* The actual straight-line bytestring length prefix, for counted execution. *)
Theory assignBasePtrBytesPrefix
Ancestors wordLoadStorePtr context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomInst words list rich_list typedCopyPtr fragGasSeqPtr instSeqComposePtr
  venomExecSemantics venomInstProofs venomState ptrDiscipline ptrSafeRun
  finite_map fragExec ghostPcTransportPtr instIdxIndep exprSimBufferStore

Theorem assign_base_bytes_prefix_code:
  !src out sa sb.
    compile_bytestring_copy_len src sa = (out,sb) ==>
    ?x y z r.
      out = Var r /\
      emitted_insts sa sb =
        [mk_inst sa.cs_next_id MLOAD [src] [x];
         mk_inst (sa.cs_next_id+1) ADD [Var x; Lit 31w] [y];
         mk_inst (sa.cs_next_id+2) AND [Var y; Lit (i2w (-32))] [z];
         mk_inst (sa.cs_next_id+3) ADD [Var z; Lit 32w] [r]] /\
      (!p. not_fresh_at sa p ==> p <> x /\ p <> y /\ p <> z /\ p <> r) /\
      ALL_DISTINCT [x;y;z;r]
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emit_op_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, DROP_APPEND1] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem assign_base_bytes_mload_seq:
  !D ctx fn PG G tn s id src out a.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?G' tn' u.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id MLOAD [Var src] [out]] (s with vs_inst_idx := k) G' tn') /\
      run_inst_seq [mk_inst id MLOAD [Var src] [out]] s = OK u /\
      u = update_var out (mload (w2n a) s) s /\
      op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  qabbrev_tac `u = update_var out (mload (w2n a) s) s` >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s = OK u` by
    (simp[Abbr `u`] >> irule step_MLOAD >> simp[eval_operand_def]) >>
  qexistsl_tac
    [`step_prov PG G (mk_inst id MLOAD [Var src] [out]) u`,
     `step_taint (mk_inst id MLOAD [Var src] [out]) s u tn`, `u`] >>
  `op_taint (step_taint (mk_inst id MLOAD [Var src] [out]) s u tn)
      (Var out) = {} /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s u tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s u tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s u tn).t_trans = tn.t_trans` by
    (simp[Abbr `u`] >> irule mload_ghost_clean >> simp[eval_operand_def]) >>
  simp[inst_seq_ptr_def, run_inst_seq_def, Abbr `u`,
       step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >-
    (gen_tac >>
     `step_inst_base (mk_inst id MLOAD [Var src] [out])
        (s with vs_inst_idx := k) =
          OK (update_var out (mload (w2n a) s) s with vs_inst_idx := k)` by
       (simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
             exec_result_map_def] >> fs[mk_inst_def]) >>
     simp[] >> irule ptr_inst_ok_mload >> simp[]) >>
  simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  simp[step_taint_def, set_var_taint_def, op_taint_def, FLOOKUP_UPDATE,
       imm_taint_def, mk_inst_def]
QED

Theorem assign_base_bytes_binop_seq:
  !D ctx fn PG G tn s id opc left right out a b f.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    eval_operands [left;right] s = SOME [a;b] /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    op_prov G left = NONE /\ op_prov G right = NONE /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn' u.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id opc [left;right] [out]] (s with vs_inst_idx := k) G' tn') /\
      run_inst_seq [mk_inst id opc [left;right] [out]] s = OK u /\
      u = update_var out (f a b) s /\
      op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_operands _ _ = _`
    (strip_assume_tac o SRULE [eval_operands_def, AllCaseEqs()]) >>
  qabbrev_tac `u = update_var out (f a b) s` >>
  `step_inst_base (mk_inst id opc [left;right] [out]) s = OK u` by
    (gvs[Abbr `u`] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def]) >>
  qexistsl_tac
    [`step_prov PG G (mk_inst id opc [left;right] [out]) u`,
     `step_taint (mk_inst id opc [left;right] [out]) s u tn`, `u`] >>
  `op_taint (step_taint (mk_inst id opc [left;right] [out]) s u tn)
      (Var out) = {} /\
   (step_taint (mk_inst id opc [left;right] [out]) s u tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst id opc [left;right] [out]) s u tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id opc [left;right] [out]) s u tn).t_trans = tn.t_trans /\
   (!p. p <> out ==>
     FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out]) u) p = FLOOKUP G p /\
     op_taint (step_taint (mk_inst id opc [left;right] [out]) s u tn) (Var p) =
       op_taint tn (Var p))` by
    (simp[Abbr `u`] >> irule copy_len_binop_ghost_frame >> metis_tac[]) >>
  `!k. ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id opc [left;right] [out]) (s with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >> simp[] >> metis_tac[]) >>
  `!k. step_inst_base (mk_inst id opc [left;right] [out])
     (s with vs_inst_idx := k) = OK (u with vs_inst_idx := k)` by
    (gen_tac >> gvs[] >>
     simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
          exec_result_map_def] >> fs[mk_inst_def]) >>
  simp[inst_seq_ptr_def, run_inst_seq_def, Abbr `u`] >>
  gvs[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  simp[step_taint_def, set_var_taint_def, imm_taint_def]
QED


(* A continuation consumes one chosen endpoint, rather than independently
   choosing a run and a ghost.  The observations are the singleton boundary. *)
Theorem assign_base_bytes_binop_cons:
  !D ctx fn PG G tn s id opc left right out a b f code Q.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    eval_operands [left;right] s = SOME [a;b] /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    op_prov G left = NONE /\ op_prov G right = NONE /\
    ~ctx_has_dalloca ctx /\
    (!G1 tn1.
      op_taint tn1 (Var out) = {} /\ op_prov G1 (Var out) = NONE /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!p. p <> out ==> FLOOKUP G1 p = FLOOKUP G p /\
        op_taint tn1 (Var p) = op_taint tn (Var p)) ==>
      ?G2 tn2.
        (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 code
          (update_var out (f a b) s with vs_inst_idx := k) G2 tn2) /\
        Q G2 tn2) ==>
    ?G2 tn2.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        (mk_inst id opc [left;right] [out]::code)
        (s with vs_inst_idx := k) G2 tn2) /\ Q G2 tn2
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_base_bytes_binop_seq >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`] >> simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    [mk_inst id opc [left;right] [out]]` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  gen_tac >>
  qspec_then `0`
    (qspec_then `[mk_inst id opc [left;right] [out]]` mp_tac)
    (Q.GEN `lo` inst_seq_ptr_append) >>
  simp[] >> disch_then irule >>
  qexistsl_tac [`G'`, `u with vs_inst_idx := k`, `tn'`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem assign_base_bytes_mload_cons:
  !D ctx fn PG G tn s id src out a code Q.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    (!G1 tn1.
      op_taint tn1 (Var out) = {} /\ op_prov G1 (Var out) = NONE /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!p. p <> out ==> FLOOKUP G1 p = FLOOKUP G p /\
        op_taint tn1 (Var p) = op_taint tn (Var p)) ==>
      ?G2 tn2.
        (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 code
          (update_var out (mload (w2n a) s) s with vs_inst_idx := k) G2 tn2) /\
        Q G2 tn2) ==>
    ?G2 tn2.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        (mk_inst id MLOAD [Var src] [out]::code)
        (s with vs_inst_idx := k) G2 tn2) /\ Q G2 tn2
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_base_bytes_mload_seq >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`] >> simp[] >> gen_tac >>
  qspec_then `0`
    (qspec_then `[mk_inst id MLOAD [Var src] [out]]` mp_tac)
    (Q.GEN `lo` inst_seq_ptr_append) >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  qexistsl_tac [`G'`, `u with vs_inst_idx := k`, `tn'`] >>
  fs[run_inst_seq_inst_idx, exec_result_map_def, mk_inst_def, is_terminator_def]
QED

Theorem assign_base_bytes_prefix_checked:
  !D ctx fn PG G tn s id src x y z r a.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\ ALL_DISTINCT [x;y;z;r] /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?G' tn'.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id MLOAD [Var src] [x];
         mk_inst (id+1) ADD [Var x; Lit 31w] [y];
         mk_inst (id+2) AND [Var y; Lit (i2w (-32))] [z];
         mk_inst (id+3) ADD [Var z; Lit 32w] [r]]
        (s with vs_inst_idx := k) G' tn') /\
      op_taint tn' (Var r) = {} /\ op_prov G' (Var r) = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. ~MEM p [x;y;z;r] ==> FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `!t w. op_taint t (Lit w) = {}` by simp[op_taint_def] >>
  ho_match_mp_tac assign_base_bytes_mload_cons >> simp[] >>
  rpt strip_tac >>
  ho_match_mp_tac assign_base_bytes_binop_cons >>
  simp[eval_operands_def, eval_operand_update_var, eval_operand_lit] >>
  rpt strip_tac >>
  ho_match_mp_tac assign_base_bytes_binop_cons >>
  simp[eval_operands_def, eval_operand_update_var, eval_operand_lit] >>
  rpt strip_tac >>
  ho_match_mp_tac assign_base_bytes_binop_cons >>
  simp[eval_operands_def, eval_operand_update_var, eval_operand_lit] >>
  rpt strip_tac >>
  simp[inst_seq_ptr_def] >> metis_tac[]
QED

Theorem assign_base_bytes_prefix_counted:
  !D ctx fn PG G tn s sa sb src out a len bb.
    compile_bytestring_copy_len (Var src) sa = (out,sb) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\ mload (w2n a) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?G' tn' q.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (q with vs_inst_idx := s.vs_inst_idx + 4)) /\
      eval_operand out q = SOME (n2w (32 + 32 * word_size len)) /\
      op_taint tn' out = {} /\ op_prov G' out = NONE /\
      (q with vs_vars := s.vs_vars) = s /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p q = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all buffer_copy_len_run >> strip_tac >>
  drule assign_base_bytes_prefix_code >> strip_tac >>
  drule_all assign_base_bytes_prefix_checked >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `sa.cs_next_id`] strip_assume_tac) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`, `q`] >>
  gvs[mk_inst_def] >> rpt strip_tac >>
  qpat_x_assum `!p. ~MEM p _ ==> _` irule >>
  simp[] >> metis_tac[]
QED
