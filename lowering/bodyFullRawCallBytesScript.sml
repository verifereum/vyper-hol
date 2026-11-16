Theory bodyFullRawCallBytes
Ancestors
  exprSimRawCall fragGasSeqPtr wordLoadStorePtr bodyFullGhostFrame
  rawCallBufferPtr representationCleanPtr builtinSimple emitHelper compileEnv
  venomState venomInst fragExec exprLoweringProps list
Libs
  monadsyntax

Theorem raw_call_bytes_success_full_path:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w n)];
      capped <- compile_select cmp len (Lit (n2w n));
      emit_void MSTORE [Var p;capped]; return (Var p) od) sa = (result,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  0 < n /\ n < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  n <= rounded /\ ((n+31) DIV 32)*32 <= rounded /\
  lookup_var p s = SOME (n2w b) /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+rounded) /\
  lo <= b /\ b+32+rounded < dimword (:256) /\
  b+32+rounded <= s.vs_alloca_next /\
  mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf.
    result = Var p /\
    (!D explicit.
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    lookup_var p t = SOME (n2w b) /\
    ptr_covers Gf tf p t (32+rounded) /\
    raw_call_finish_view t = raw_call_finish_view
      (mstore b (n2w (MIN (LENGTH s.vs_returndata) n)) s) /\
    tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) b mem) /\
    (!D d cenv cx es.
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
      (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
      (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
      (!name lb k. local_region cenv es.scopes s name lb k ==>
        lb+k <= b \/ b+32 <= lb) ==>
      ghost_inv_at D lo d cenv cx es Gf tf
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      ghost_kept_at lo cenv es sa G tn s Gf tf)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME (n2w b)` by simp[eval_operand_def] >>
  drule raw_call_success_run_aged >> simp[] >>
  disch_then (qspecl_then [`s`, `n2w b`] mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `a0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `a1 = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `a2 = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `a3 = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `a4 = STRING #"%" (toString (sa.cs_next_var+4))` >>
  qmatch_asmsub_abbrev_tac `fn_has_code sa sc func` >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[emitted_insts_def, Abbr `sc`] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  strip_tac >>
  `ALL_DISTINCT [a0;a1;a2;a3;a4]` by
    simp[Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`, Abbr `a4`,
         builtinIntClampTheory.fresh_var_name_eq] >>
  `!x. not_fresh_at sa x ==> ~MEM x [a0;a1;a2;a3;a4]` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def,
          Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`, Abbr `a4`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  `p <> a0 /\ p <> a1 /\ p <> a2 /\ p <> a3 /\ p <> a4` by metis_tac[MEM] >>
  fs[ALL_DISTINCT, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `mstore b capword u = t` >>
  `capword = n2w (MIN (LENGTH s.vs_returndata) n)` by
    (simp[Abbr `capword`] >> Cases_on `LENGTH s.vs_returndata < n` >>
     simp[bool_to_word_def, arithmeticTheory.MIN_DEF] >>
     wordsLib.WORD_DECIDE_TAC) >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {a0;a1;a2;a3;a4})` >>
  qabbrev_tac `tp = tn with t_var :=
    tn.t_var |+ (a0,{}) |+ (a1,{}) |+ (a2,{}) |+ (a3,{}) |+ (a4,{})` >>
  qabbrev_tac `tf = tp with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[Abbr `u`, Abbr `Gf`, Abbr `tp`, lookup_var_def,
       ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sc) s Gf tf` by
    suspend "checks" >>
  qexistsl_tac [`Gf`, `tf`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "halted" >>
  conj_tac >- suspend "block" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "allocas" >>
  conj_tac >- suspend "next" >>
  conj_tac >- suspend "lookup" >>
  conj_tac >- suspend "covers" >>
  conj_tac >- suspend "memtaint" >>
  conj_tac >- suspend "stor" >>
  conj_tac >- suspend "trans" >>
  conj_tac >- suspend "imm" >>
  conj_tac >- suspend "old" >>
  conj_tac >- suspend "robust" >>
  suspend "frame"
QED

Resume raw_call_bytes_success_full_path[checks]:
  FAIL_TAC "checks"
QED

Resume raw_call_bytes_success_full_path[path]: cheat QED
Resume raw_call_bytes_success_full_path[halted]: cheat QED
Resume raw_call_bytes_success_full_path[block]: cheat QED
Resume raw_call_bytes_success_full_path[history]: cheat QED
Resume raw_call_bytes_success_full_path[allocas]: cheat QED
Resume raw_call_bytes_success_full_path[next]: cheat QED
Resume raw_call_bytes_success_full_path[lookup]: cheat QED
Resume raw_call_bytes_success_full_path[covers]: cheat QED
Resume raw_call_bytes_success_full_path[memtaint]: cheat QED
Resume raw_call_bytes_success_full_path[stor]: cheat QED
Resume raw_call_bytes_success_full_path[trans]: cheat QED
Resume raw_call_bytes_success_full_path[imm]: cheat QED
Resume raw_call_bytes_success_full_path[old]: cheat QED
Resume raw_call_bytes_success_full_path[robust]: cheat QED
Resume raw_call_bytes_success_full_path[frame]: cheat QED

Finalise raw_call_bytes_success_full_path
(* suffix *)
QED
