(* Shared dynamic hash input preparation, before the allocated SHA tail. *)
Theory bodyPtrHashBuiltinsShaPrefix
Ancestors wordLoadStorePtr bodyPtrHashBuiltinsKeccakBytesRun fragGasSeqPtr ptrDiscipline
  venomState venomInst venomExecSemantics words finite_map pred_set
  typedCopyPtr typedCopyLoopHeaderPtr exprSimHash list bodyPtrDefs valueEncodingProps
  emitHelper emitHelperProps compileEnv exprLoweringProps ASCIInumbers rich_list arithmetic
  bodyPtrHashBuiltinsGhostFrame exprSimProps

Theorem hash_bytes_prepare_inst_seq:
  !D ctx fn PG G tn s il ia x l p b base cap n.
  ALL_DISTINCT [x;l;p] /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst il MLOAD [Var x] [l];mk_inst ia ADD [Var x;Lit 32w] [p]] s
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
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume hash_bytes_prepare_inst_seq[add]:
  `step_prov PG G (mk_inst il MLOAD [Var x] [l]) (update_var l (n2w n) s) = G1` by
    simp[Abbr `G1`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s1 =
    OK (update_var p (n2w b+32w) s1)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[inst_seq_ptr_def, hash_add_ghost, Abbr `tn1`, Abbr `G1`]
QED
Finalise hash_bytes_prepare_inst_seq

Theorem hash_bytes_prepare_emission:
  !x sa len_op sl data_op sm.
  emit_op MLOAD [x] sa = (len_op,sl) /\
  emit_op ADD [x;Lit 32w] sl = (data_op,sm) ==>
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id MLOAD [x] [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) ADD [x;Lit 32w]
       [STRING #"%" (toString (sa.cs_next_var+1))]] /\
  len_op = Var (STRING #"%" (toString sa.cs_next_var)) /\
  data_op = Var (STRING #"%" (toString (sa.cs_next_var+1))) /\
  (!z. not_fresh_at sa z ==>
     z <> STRING #"%" (toString sa.cs_next_var) /\
     z <> STRING #"%" (toString (sa.cs_next_var+1)))
Proof
  rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
    not_fresh_at_def, toString_inj] >> decide_tac
QED

Theorem hash_bytes_prepare_counted:
  !D ctx fn PG G tn s t bb x sa len_op sl data_op sm b base cap n.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x;Lit 32w] sl = (data_op,sm) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  ?G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1
    (OK (t with vs_inst_idx := s.vs_inst_idx+2)) /\
  G1 = DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var)}) |+
    (STRING #"%" (toString (sa.cs_next_var+1)),(base,cap)) /\
  tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}) |+
    (STRING #"%" (toString (sa.cs_next_var+1)),{})
Proof
  rpt gen_tac >> strip_tac >> drule_all hash_bytes_prepare_emission >> strip_tac >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var)}) |+
    (STRING #"%" (toString (sa.cs_next_var+1)),(rootbase,cap))` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}) |+
    (STRING #"%" (toString (sa.cs_next_var+1)),{})` >>
  qexistsl_tac [`G1`, `tn1`] >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm) s G1 tn1` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule hash_bytes_prepare_inst_seq >>
     simp[ALL_DISTINCT, toString_inj] >>
     qexistsl_tac [`b`, `n`] >> simp[] >> decide_tac) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sm)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem hash_bytes_prepare_frame:
  !D ctx fn PG G tn s bb x sa len_op sl data_op sm b base cap n d cenv cx es.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x;Lit 32w] sl = (data_op,sm) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) ==>
  ?t G1 tn1 p.
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1
    (OK (t with vs_inst_idx := s.vs_inst_idx+2)) /\
  (t with vs_vars := s.vs_vars) = s /\
  stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es G1 tn1 t /\
  ghost_kept cenv es sa G tn s G1 tn1 /\ data_op = Var p /\
  eval_operand data_op t = SOME (n2w (b+32)) /\ eval_operand len_op t = SOME (n2w n) /\
  ptr_covers G1 tn1 p t n /\ op_taint tn1 len_op = {} /\
  (!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn1.t_mem) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
  (!z. len_op = Var z \/ data_op = Var z ==> not_fresh_at sm z) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+2 /\ sm.cs_next_id = sa.cs_next_id+2
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all hash_data_prefix_run >> strip_tac >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all hash_bytes_prepare_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  `!z. not_fresh_at sa z ==> FLOOKUP G1 z = FLOOKUP G z /\
     op_taint tn1 (Var z) = op_taint tn (Var z)` by
    (rpt strip_tac >> gvs[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `ghost_inv d cenv cx es G1 tn1 t` by
    (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s G1 tn1` by
    (irule hash_ghost_kept_frame >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  suspend "coverage"
QED

Resume hash_bytes_prepare_frame[coverage]:
  `not_fresh_at sm (STRING #"%" (toString sa.cs_next_var)) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+1)))` by
    (qpat_x_assum `!z. len_op = Var z \/ data_op = Var z ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G1`, `tn1`, `STRING #"%" (toString (sa.cs_next_var+1))`] >>
  simp[] >>
  conj_tac >-
    (simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, toString_inj] >>
     qexists_tac `n2w (b+32)` >>
     gvs[eval_operand_def] >> decide_tac) >>
  conj_tac >- simp[op_taint_def, FLOOKUP_UPDATE, toString_inj] >>
  rpt strip_tac >> gvs[]
QED
Finalise hash_bytes_prepare_frame

Theorem hash_readonly_input_window:
  (t with vs_vars := s.vs_vars) = s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sa.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a /\ a+n <= b+k)) ==>
  (n = 0 \/
   (?aid b k. FLOOKUP t.vs_allocas aid = SOME (b,k) /\
      aid < sb.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes t name b k /\
      b <= a /\ a+n <= b+k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(t with vs_vars := _) = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_allocas`) >> simp[]) >>
  qpat_x_assum `n = 0 \/ _` strip_assume_tac >- simp[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`aid`, `b`, `k`] >> simp[] >> decide_tac) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`name`, `b`, `k`] >> simp[] >>
  irule local_region_frame_fwd >> qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]
QED
