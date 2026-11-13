(* Account-read and copy boundaries at the state after address evaluation. *)
Theory exprSimSliceExtcode
Ancestors
  loweringStateRelDefs valueEncodingDefs
  exprSimSliceBounds exprSimSliceData exprSimAccounts accountsRelProps
  builtinBytes emitHelperProps exprLoweringProps fragExec compileEnv context
  venomExecSemantics venomInst venomState vyperTypeInvariants
  vfmState vyperValue valueEncoding words arithmetic list rich_list

Theorem slice_extcode_account:
  accounts_agree H cx acc s.vs_accounts /\ accounts_well_typed acc /\
  LENGTH bs = 20 ==>
  (lookup_account
    (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) s.vs_accounts).code =
    (lookup_account (word_of_bytes_be bs) acc).code /\
  LENGTH (lookup_account (word_of_bytes_be bs) acc).code <= 24576
Proof
  strip_tac >> drule address_word_w2w >> strip_tac >> simp[] >>
  conj_tac
  >- (drule accounts_agree_lookup >> simp[]) >>
  fs[accounts_well_typed_def, account_well_typed_def]
QED

Theorem slice_extcodesize_step:
  eval_operand addr s = SOME a ==>
  step_inst_base (mk_inst iid EXTCODESIZE [addr] [out]) s =
    OK (update_var out
      (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]
QED

Theorem slice_extcodecopy_step:
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME d /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  w2n b + w2n n <= LENGTH (lookup_account (w2w a) s.vs_accounts).code ==>
  step_inst_base (mk_inst iid EXTCODECOPY [addr; dst; start; len] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n b) (lookup_account (w2w a) s.vs_accounts).code)) s)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  irule rich_listTheory.TAKE_APPEND1 >> simp[]
QED

Theorem slice_extcode_decompose:
  compile_slice_extcode addr start len sz sa = (r,sb) ==>
  ?sc sd se sf src_len dst.
    emit_op EXTCODESIZE [addr] sa = (src_len,sc) /\
    compile_assert_slice_bounds start len src_len sc = ((),sd) /\
    compile_slice_out_buf sz sd = ((r,dst),se) /\
    emit_void EXTCODECOPY [addr;dst;start;len] se = ((),sf) /\
    emit_void MSTORE [r;len] sf = ((),sb)
Proof
  simp[compile_slice_extcode_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> metis_tac[pairTheory.PAIR]
QED

Theorem slice_extcode_copy_store_run:
  emit_void EXTCODECOPY [addr;dst;start;len] sa = ((),sm) /\
  emit_void MSTORE [out;len] sm = ((),sb) /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME d /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\
  w2n b + w2n n <= LENGTH (lookup_account (w2w a) s.vs_accounts).code ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n p) n
      (write_memory_with_expansion (w2n d)
       (TAKE (w2n n) (DROP (w2n b) (lookup_account (w2w a) s.vs_accounts).code)) s))
Proof
  strip_tac >>
  `TAKE (w2n n) (DROP (w2n b) (lookup_account (w2w a) s.vs_accounts).code ++
     REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n b) (lookup_account (w2w a) s.vs_accounts).code)` by
    (irule rich_listTheory.TAKE_APPEND1 >> simp[] ) >>
  qpat_x_assum `emit_void EXTCODECOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2, run_inst_seq_def] >>
  drule_all slice_extcodecopy_step >> disch_then (qspec_then `sa.cs_next_id` SUBST1_TAC) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       write_memory_with_expansion_def] >>
  Cases_on `out` >> Cases_on `len` >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem slice_extcodesize_run:
  emit_op EXTCODESIZE [addr] sa = (sz,sb) /\
  eval_operand addr s = SOME a ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand sz t =
      SOME (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
       eval_operand_def, lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
                       not_fresh_at_def]
QED

Theorem slice_extcodesize_fresh:
 emit_op EXTCODESIZE [addr] sa = (sz,sc) ==>
 (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
 (!x. sz = Var x ==> not_fresh_at sc x)
Proof
 strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
 fs[not_fresh_at_def] >> metis_tac[DECIDE ``a < b ==> a < b+1``]
QED

Theorem slice_extcode_out_buf_insts[local]:
  compile_slice_out_buf sz sa = ((out,data),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 2 /\ sb.cs_next_id = sa.cs_next_id + 2 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ADD [out; Lit 32w]
       [STRING #"%" (toString (sa.cs_next_var + 1))]]
Proof
  simp[compile_slice_out_buf_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem slice_extcode_shape:
 compile_slice_extcode addr start len sz sa = (r,sb) ==>
 ?sc sd se sf src_len dst.
   emit_op EXTCODESIZE [addr] sa = (src_len,sc) /\
   compile_assert_slice_bounds start len src_len sc = ((),sd) /\
   compile_slice_out_buf sz sd = ((r,dst),se) /\
   emit_void EXTCODECOPY [addr;dst;start;len] se = ((),sf) /\
   emit_void MSTORE [r;len] sf = ((),sb) /\
   sd.cs_next_var = sa.cs_next_var + 6 /\ sd.cs_next_id = sa.cs_next_id + 7 /\
   se.cs_next_var = sd.cs_next_var + 2 /\ se.cs_next_id = sd.cs_next_id + 2 /\
   sb.cs_next_var = se.cs_next_var /\ sb.cs_next_id = se.cs_next_id + 2 /\
   sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
   se.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd se /\
   sb.cs_current_insts = se.cs_current_insts ++ emitted_insts se sb /\
   emitted_insts sa sd = emitted_insts sa sc ++ emitted_insts sc sd /\
   emitted_insts sd se =
     [mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sd.cs_next_var)];
      mk_inst (sd.cs_next_id + 1) ADD [r; Lit 32w]
        [STRING #"%" (toString (sd.cs_next_var + 1))]] /\
   emitted_insts sa sb =
     emitted_insts sa sd ++ (emitted_insts sd se ++ emitted_insts se sb)
Proof
 strip_tac >> drule slice_extcode_decompose >> strip_tac >>
 qexistsl_tac [`sc`,`sd`,`se`,`sf`,`src_len`,`dst`] >> simp[] >>
 drule emitted_insts_emit_op >> strip_tac >>
 drule slice_bounds_shape >> strip_tac >>
 drule slice_extcode_out_buf_insts >> strip_tac >>
 imp_res_tac emitted_insts_emit_void >>
 `emitted_insts sa sd = emitted_insts sa sc ++ emitted_insts sc sd` by
   (irule emitted_insts_append >> simp[]) >>
 `emitted_insts se sb = emitted_insts se sf ++ emitted_insts sf sb` by
   (irule emitted_insts_append >> simp[]) >>
 `sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd` by
   simp[] >>
 `sb.cs_current_insts = se.cs_current_insts ++ emitted_insts se sb` by
   simp[] >>
 `emitted_insts sd sb = emitted_insts sd se ++ emitted_insts se sb` by
   (irule emitted_insts_append >> simp[]) >>
 `emitted_insts sa sb = emitted_insts sa sd ++ emitted_insts sd sb` by
   (irule emitted_insts_append >> simp[] >>
    qpat_x_assum `emitted_insts sd sb = _` (fn th => rewrite_tac[th]) >>
    simp[]) >>
 simp[]
QED

Theorem slice_extcode_prefix_run:
 emit_op EXTCODESIZE [addr] sa = (sz,sc) /\
 compile_assert_slice_bounds start len sz sc = ((),sd) /\
 eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
 eval_operand len s = SOME n /\
 (!x. MEM (Var x) [addr;start;len] ==> not_fresh_at sa x) /\
 LENGTH (lookup_account (w2w a) s.vs_accounts).code < dimword (:256) ==>
 if LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n then
   ?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sd) s = Abort Revert_abort u
 else ?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sd) s = OK u /\
   u = s with vs_vars := u.vs_vars /\
   (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
   (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
         eval_operand op u = eval_operand op s)
Proof
 strip_tac >>
 drule_all slice_extcodesize_run >> strip_tac >>
 drule slice_extcodesize_fresh >> strip_tac >>
 `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
       eval_operand op t = eval_operand op s` by
   (Cases >> simp[eval_operand_def] >>
    qpat_x_assum `t = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `eval_operand start t = SOME b /\ eval_operand len t = SOME n` by
   metis_tac[MEM] >>
 `!x. start = Var x ==> not_fresh_at sc x` by metis_tac[MEM] >>
 `!x. len = Var x ==> not_fresh_at sc x` by metis_tac[MEM] >>
 `(((b:bytes32) + (n:bytes32) <+ b \/
     n2w (LENGTH (lookup_account (w2w (a:bytes32)) s.vs_accounts).code) <+ b + n) <=>
    LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n)` by
   (mp_tac (Q.SPECL [`dimword (:256)`,`w2n (b:bytes32)`,`w2n (n:bytes32)`,
      `LENGTH (lookup_account (w2w (a:bytes32)) s.vs_accounts).code`] exprSimSliceBoundsTheory.slice_bounds_mod) >>
    simp[WORD_LO, word_add_def, w2n_n2w, w2n_lt] >> decide_tac) >>
 drule_all slice_bounds_run_frame >>
 qpat_x_assum `(_ \/ _) <=> _` (fn th => pure_rewrite_tac[th]) >>
 Cases_on `LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n` >>
 simp[] >> strip_tac >>
 qpat_assum `run_inst_seq (emitted_insts sa sc) s = OK t`
   (mp_then Any (fn th => once_rewrite_tac[th]) run_inst_seq_append)
 >- metis_tac[] >>
 qexists_tac `t'` >> simp[] >>
 `t' = s with vs_vars := t'.vs_vars` by
   (qpat_x_assum `t' = t with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >>
    qpat_x_assum `t = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `!x. not_fresh_at sa x ==> lookup_var x t' = lookup_var x s` by
   (rpt strip_tac >>
    `not_fresh_at sc x` by metis_tac[] >>
    fs[lookup_var_def]) >>
 simp[] >> Cases >> simp[eval_operand_def] >>
 qpat_x_assum `t' = s with vs_vars := _`
   (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem slice_extcode_tail_run:
  emit_void EXTCODECOPY [addr;dst;start;len] sa = ((),sm) /\
  emit_void MSTORE [out;len] sm = ((),sb) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  eval_operand dst s = SOME d /\
  w2n b + w2n n <= LENGTH (lookup_account (w2w a) s.vs_accounts).code ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p) n
        (write_memory_with_expansion (w2n d)
          (TAKE (w2n n) (DROP (w2n b)
            (lookup_account (w2w a) s.vs_accounts).code)) s)).vs_memory /\
    (t with <| vs_memory := s.vs_memory; vs_vars := s.vs_vars |>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand out t = SOME p
Proof
 strip_tac >> drule_all slice_extcode_copy_store_run >> strip_tac >>
 qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sa sb) s = OK v` >>
 qexists_tac `v` >> simp[] >> rpt conj_tac
 >- ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
      [Abbr `v`, mstore_def, write_memory_with_expansion_def]
 >- simp[Abbr `v`, mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
 qpat_x_assum `eval_operand out s = SOME p` mp_tac >>
 Cases_on `out` >>
 ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
   [Abbr `v`, mstore_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

Theorem slice_extcode_tail_frame:
  emit_void EXTCODECOPY [addr;dst;start;len] sa = ((),sm) /\
  emit_void MSTORE [out;len] sm = ((),sb) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  eval_operand dst s = SOME (p + 32w) /\
  (!x. MEM (Var x) [addr;start;len;out;dst] ==> not_fresh_at sa x) /\
  w2n b + w2n n <= LENGTH (lookup_account (w2w a) s.vs_accounts).code /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es es sbase s t /\
    eval_operand out t = SOME p /\
    FLOOKUP t.vs_allocas aid = SOME (w2n p,cap) /\
    t.vs_memory = (mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n b) (lookup_account (w2w a) s.vs_accounts).code)) s)).vs_memory /\
    (!nm off sz. local_region cenv es.scopes t nm off sz ==>
      regions_disjoint (w2n p) cap off sz)
Proof
 strip_tac >> drule_all slice_extcode_tail_run >> simp[] >> strip_tac >>
 `w2n (p + 32w) = w2n p + 32` by
   (simp[word_add_def, w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
 qmatch_asmsub_abbrev_tac `t.vs_memory = w.vs_memory` >>
 `LENGTH (TAKE (w2n n) (DROP (w2n b)
    (lookup_account (w2w a) s.vs_accounts).code)) = w2n n` by
   (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
 `stmt_state_rel H ctx func cenv cx es w /\ wb_frame cenv es es sbase s w` by
   (simp[Abbr `w`] >>
    qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ bytes s` >>
    `n = n2w (LENGTH bytes)` by simp[Abbr `bytes`] >>
    pop_assum (fn th => once_rewrite_tac[th]) >>
    irule (SIMP_RULE std_ss [LET_THM] slice_allocated_bytes_write_frame) >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`inst`,`cap`] >> simp[] >> metis_tac[]) >>
 `w.vs_vars = s.vs_vars /\ w.vs_allocas = s.vs_allocas` by
   ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
     [Abbr `w`, mstore_def, write_memory_with_expansion_def] >>
 `t = w with vs_vars := t.vs_vars` by
   (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
    simp[venom_state_component_equality] >> strip_tac >>
    ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
      [Abbr `w`, mstore_def, write_memory_with_expansion_def,
       venom_state_component_equality]) >>
 `stmt_state_rel H ctx func cenv cx es t` by
   (qpat_assum `t = w with vs_vars := _` SUBST1_TAC >>
    irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
    rpt strip_tac >> fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
 `wb_frame cenv es es sbase s t` by
   (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
    goal_assum (drule_at Any) >> qexists_tac `sa` >> simp[] >>
    conj_tac >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
    qpat_assum `t = w with vs_vars := _` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
 `FLOOKUP t.vs_allocas aid = SOME (w2n p,cap)` by
   (qpat_assum `t = w with vs_vars := _` SUBST1_TAC >> simp[]) >>
 qexists_tac `t` >> simp[] >> conj_tac
 >- (qpat_x_assum `t.vs_memory = w.vs_memory` (fn th => pure_rewrite_tac[th]) >>
     simp[Abbr `w`]) >>
 rpt strip_tac >>
 `local_region cenv es.scopes s nm off sz` by
   (irule exprSimPropsTheory.local_region_frame >>
    conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
    qexistsl_tac [`sa`,`es.scopes`,`t`] >> simp[] >> metis_tac[]) >>
 metis_tac[]

QED

Theorem slice_extcode_tail_vv_post:
  emit_void EXTCODECOPY [addr;dst;start;len] sa = ((),sm) /\
  emit_void MSTORE [out;len] sm = ((),sb) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  eval_operand dst s = SOME (p + 32w) /\
  (!x. MEM (Var x) [addr;start;len;out;dst] ==> not_fresh_at sa x) /\
  w2n b + w2n n <= LENGTH (lookup_account (w2w a) s.vs_accounts).code /\
  stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
  local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic max_len)) /\ w2n n <= max_len /\
  aid < sb.cs_next_id ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    !k. vv_post H ctx func cenv cx e es sbase sb s es
      (Value (BytesV (TAKE (w2n n) (DROP (w2n b)
        (lookup_account (w2w a) s.vs_accounts).code))))
      (LocatedValue (expr_type e) (mk_ptr out LocMemory)) (t with vs_inst_idx := k)
Proof
  strip_tac >> drule_all slice_extcode_tail_frame >> strip_tac >>
  `LENGTH (TAKE (w2n n) (DROP (w2n b)
      (lookup_account (w2w a) s.vs_accounts).code)) = w2n n` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `val_in_memory (BaseTV (BytesT (Dynamic max_len)))
      (BytesV (TAKE (w2n n) (DROP (w2n b)
        (lookup_account (w2w a) s.vs_accounts).code))) (w2n p) t.vs_memory` by
    (qpat_x_assum `t.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     metis_tac[exprSimCalldataSliceTheory.bytes_buffer_write_encoding, n2w_w2n]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `pure_frame cenv func es sbase s t` by
    (match_mp_tac (Q.SPECL [`cenv`, `func`, `es`, `sbase`, `s`, `t`, `inst`,
                            `w2n (p:bytes32)`, `cap`,
                            `TAKE (w2n (n:bytes32)) (DROP (w2n (b:bytes32))
                               (lookup_account (w2w (a:bytes32)) s.vs_accounts).code)`]
                     slice_allocated_bytes_pure_frame) >>
     qpat_assum `LENGTH _ = w2n n`
       (fn th => rewrite_tac[th, wordsTheory.n2w_w2n]) >>
     qpat_assum `inst.inst_id = aid` (fn th => rewrite_tac[th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >> gen_tac >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, mk_ptr_def,
       stmt_state_rel_inst_idx,
       evaluate_type_def, is_word_type_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      qspec_then `max_len` mp_tac exprSimPropsTheory.le_word_size_mul >> decide_tac) >>
  disj1_tac >> qexistsl_tac [`aid`,`w2n p`,`cap`] >>
  simp[loweringPostsTheory.val_footprint_def] >>
  fs[regions_disjoint_def]

QED
