(* Covered bytes prefixes and the dynamic RawLog suffix. *)
Theory rawLogPtrDynamic
Ancestors
  rawLogPtrInst bodyPtrHashBuiltinsKeccakBytesRun
  typedCopyPtr bodyPtrDefs fragGasSeqPtr ptrDiscipline venomState venomInst
  venomExecSemantics words finite_map pred_set contextCodegenRel codegenRel
  valueEncodingProps exprSimHash list context compileEnv emitHelper
  exprLoweringProps rich_list ASCIInumbers emitHelperProps
  exprSimRawLog instSeqComposePtr ghostPcTransportPtr instIdxIndep

(* The common length/payload-address prefix does not depend on its consumer. *)
Theorem bytes_mload_add_inst_seq_ptr:
  !D ctx fn PG G tn s il ia x l p b base cap n.
    ALL_DISTINCT [x;l;p] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32 <= base+cap /\
    b+32 < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst il MLOAD [Var x] [l]; mk_inst ia ADD [Var x;Lit 32w] [p]] s
      (DRESTRICT G (COMPL {l}) |+ (p,(base,cap)))
      (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `ptr_covers G tn x s 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `mload b s = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s = OK (update_var l (n2w n) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume bytes_mload_add_inst_seq_ptr[add]:
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s1 =
    OK (update_var p (n2w b + 32w) s1)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[inst_seq_ptr_def, hash_add_ghost, Abbr `G1`, Abbr `tn1`] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  gvs[ALL_DISTINCT]
QED

Finalise bytes_mload_add_inst_seq_ptr

Theorem bytes_mload_add_emitted_ptr:
  !D ctx fn PG G tn s x sa len_op sl data_op sb b base cap n.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x; Lit 32w] sl = (data_op,sb) /\
  not_fresh_at sa x /\ eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32 <= base+cap /\
  b+32 < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    op_taint tn' len_op = {} /\ op_prov G' len_op = NONE /\
    op_taint tn' data_op = {} /\ op_prov G' data_op = SOME (base,cap) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `l = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `p = STRING #"%" (toString (sa.cs_next_var+1))` >>
  `ALL_DISTINCT [x;l;p]` by
    (gvs[ALL_DISTINCT, Abbr `l`, Abbr `p`, not_fresh_at_def, toString_inj] >>
     metis_tac[]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qexistsl_tac [`DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap))`,
    `tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})`] >>
  conj_tac
  >- (simp[emitted_insts_def] >>
      CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
      simp[DROP_LENGTH_APPEND] >>
      irule bytes_mload_add_inst_seq_ptr >> simp[] >>
      qexistsl_tac [`b`, `n`] >> simp[]) >>
  fs[ALL_DISTINCT] >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `z <> l /\ z <> p` by
    (gvs[Abbr `l`, Abbr `p`, not_fresh_at_def] >> metis_tac[]) >>
  simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem raw_log_dynamic_inst_seq_ptr:
  !D ctx fn PG G tn s x sa len_op sl ptr_op sp u sb b root cap n ops vals.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x; Lit 32w] sl = (ptr_op,sp) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] sp = (u,sb) /\
  not_fresh_at sa x /\ eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (root,cap) /\ root <= b /\ b+32+n <= root+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\
  op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ LENGTH ops < dimword (:256) /\
  eval_operands ops s = SOME vals /\
  EVERY (\op. !z. op = Var z ==> not_fresh_at sa z) ops /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  ?G' tn' t.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
    (?mid. t = mid with vs_logs := t.vs_logs /\
      (mid with vs_vars := s.vs_vars) = s /\
      (!z. not_fresh_at sa z ==> lookup_var z mid = lookup_var z s)) /\
    t.vs_memory = s.vs_memory /\
    t.vs_logs = s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address; topics := vals;
          data := TAKE n (DROP (b+32) s.vs_memory ++ REPLICATE n 0w) |>]
Proof
  rpt gen_tac >> strip_tac >>
  `b+32 <= root+cap /\ b < dimword (:256)` by decide_tac >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. b <= i /\ i < b+32+n ==> _` irule >> decide_tac) >>
  drule_all bytes_mload_add_emitted_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sp) s = OK mid` >>
  `eval_operands ops mid = SOME vals` by
    (drule_all raw_log_operands_readonly >> simp[]) >>
  `mid.vs_memory = s.vs_memory /\ mid.vs_call_ctx = s.vs_call_ctx /\
   mid.vs_logs = s.vs_logs` by
    (qpat_x_assum `(mid with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `EVERY (\op. op_taint tn' op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `op_taint tn' op = op_taint tn op` by
       (Cases_on `op` >> simp[op_taint_def] >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "log"
QED

Resume raw_log_dynamic_inst_seq_ptr[log]:
  qabbrev_tac `logs = s.vs_logs ++
    [<| logger := w2w s.vs_call_ctx.cc_address; topics := vals;
        data := TAKE n (DROP (b+32) s.vs_memory ++ REPLICATE n 0w) |>]` >>
  `step_inst_base (mk_inst sp.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) mid =
      OK (mid with vs_logs := logs)` by
    (mp_tac (Q.GENL [`off`, `len`, `topics`] (Q.INST [`inst` |-> `mk_inst sp.cs_next_id LOG
       (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []`,
       `sz` |-> `len_op`, `pop` |-> `ptr_op`, `s` |-> `mid`]
       raw_log_core_step)) >>
     simp[mk_inst_def, Abbr `logs`]) >>
  `emitted_insts sa sb = emitted_insts sa sp ++
    [mk_inst sp.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     qpat_x_assum `sp.cs_current_insts = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >>
     pure_asm_rewrite_tac[] >>
     simp[NoAsms, DROP_APPEND, DROP_LENGTH_APPEND] >>
     `LENGTH sa.cs_current_insts -
       (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sp)) = 0` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[NoAsms]) >>
  qabbrev_tac `li = mk_inst sp.cs_next_id LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []` >>
  `~is_terminator li.inst_opcode` by
    simp[Abbr `li`, mk_inst_def, is_terminator_def] >>
  `!k. inst_seq_ptr D 0 ctx fn PG G' tn'
    [mk_inst sp.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []]
    (mid with vs_inst_idx := k) G' tn'` by
    (gen_tac >>
     `step_inst_base li (mid with vs_inst_idx := k) =
       OK ((mid with vs_logs := logs) with vs_inst_idx := k)` by
       (drule step_inst_inst_idx_indep >>
        disch_then (qspecl_then [`mid`, `k`] mp_tac) >>
        qpat_assum `step_inst_base li mid = _` (fn th => rewrite_tac[th]) >>
        simp[exec_result_map_def]) >>
     pure_rewrite_tac[Once inst_seq_ptr_def] >>
     conj_tac >- suspend "check" >>
     qpat_assum `step_inst_base li (mid with vs_inst_idx := k) = _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[inst_seq_ptr_def, Abbr `li`, log_ghost]) >>
  qexistsl_tac [`G'`, `tn'`, `mid with vs_logs := logs`] >> simp[] >>
  conj_tac >- (irule inst_seq_ptr_append >>
    conj_tac >- suspend "nonterm" >>
    qexistsl_tac [`G'`, `mid`, `tn'`] >> simp[Abbr `li`]) >>
  drule run_inst_seq_append >> disch_then (qspec_then `[li]` mp_tac) >>
  simp[run_inst_seq_def] >> strip_tac >> qexists_tac `mid` >> simp[]
QED

Resume raw_log_dynamic_inst_seq_ptr[nonterm]:
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_APPEND,
    mk_inst_def, is_terminator_def] >>
  `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0`
    by decide_tac >> simp[is_terminator_def]
QED

Resume raw_log_dynamic_inst_seq_ptr[check]:
  irule log_inst_ok >> fs[Abbr `li`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `step_inst_base _ (mid with vs_inst_idx := k) = _` mp_tac >>
      simp[] >> strip_tac >>
      qexists_tac `mid with <|vs_inst_idx := k; vs_logs := logs|>` >> simp[]) >>
  strip_tac >> Cases_on `ptr_op` >> fs[op_prov_def] >>
  qexistsl_tac [`root`, `cap`] >> simp[] >> decide_tac
QED

Finalise raw_log_dynamic_inst_seq_ptr
