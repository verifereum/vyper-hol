(* Counted memory safety of a string literal reason: the literal's buffer
   (compile_bytelike_literal) runs memory-safe, and leaves a pointer whose
   length word and rounded payload lie in the buffer's region. *)
Theory stmtReasonLitMemory
Ancestors
  stmtReasonMemory fragExecMem instMemFrontier exprLowering context
  emitHelper emitHelperProps exprLoweringProps compileEnv freshWrites
  venomMemDefs venomMemProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem mk_inst_opcode[local,simp]:
  (mk_inst id op ops outs).inst_opcode = op
Proof
  simp[mk_inst_def]
QED

Theorem w2n_add_n2w[local]:
  !p off. p + off < dimword (:256) ==>
    w2n (n2w p + n2w off : bytes32) = p + off
Proof
  rpt strip_tac >> simp_tac std_ss [word_add_n2w, w2n_n2w] >>
  irule LESS_MOD >> first_assum ACCEPT_TAC
QED

Theorem chunk_state_eqs[local,simp]:
  (update_var x w s).vs_allocas = s.vs_allocas /\
  (update_var x w s).vs_alloca_next = s.vs_alloca_next /\
  (update_var x w s).vs_labels = s.vs_labels /\
  (update_var x w s).vs_current_bb = s.vs_current_bb /\
  (update_var x w s).vs_inst_idx = s.vs_inst_idx /\
  (update_var x w s).vs_halted = s.vs_halted /\
  (mstore a v s).vs_allocas = s.vs_allocas /\
  (mstore a v s).vs_alloca_next = s.vs_alloca_next /\
  (mstore a v s).vs_labels = s.vs_labels /\
  (mstore a v s).vs_current_bb = s.vs_current_bb /\
  (mstore a v s).vs_inst_idx = s.vs_inst_idx /\
  (mstore a v s).vs_halted = s.vs_halted /\
  mload b (update_var x w s) = mload b s
Proof
  simp[update_var_def, mstore_def, mload_def]
QED

(* One chunk: the ADD of its address and the MSTORE of its word. *)
Theorem chunk_head_run_mem[local]:
  !pop off value sa dst sm sb s p.
    emit_op ADD [pop; Lit (n2w off)] sa = (dst, sm) /\
    emit_void MSTORE [dst; Lit value] sm = ((), sb) /\
    (!x. pop = Var x ==> not_fresh_at sa x) /\
    eval_operand pop s = SOME (n2w p) /\
    p + off + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    sb.cs_next_id = sa.cs_next_id + 2 /\
    EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MSTORE)
      (emitted_insts sa sb) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (mstore (p + off) value
            (update_var (STRING #"%" (toString sa.cs_next_var))
               (n2w p + n2w off) s))
Proof
  rpt gen_tac >> strip_tac >>
  `p + off < dimword (:256)` by decide_tac >>
  `eval_operand pop
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p + n2w off)
        s) = SOME (n2w p)` by
    (Cases_on `pop` >> fs[eval_operand_def, lookup_var_update_var] >>
     fs[update_var_def] >>
     rw[] >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1] >>
  simp[run_inst_seq_def, run_inst_seq_mem_ok_def, step_add_eq,
       step_mstore_eq, eval_operand_def, lookup_var_update_var,
       below_frontier_MSTORE, below_frontier_no_ranges,
       dload_mk_inst_other, w2n_add_n2w]
QED

(* The literal's chunks, stored from off on: each word lies below the
   frontier, and memory before off is untouched. *)
Theorem store_chunks_run_mem:
  !pop bs off sa sb s p.
    compile_store_byte_chunks pop bs off sa = ((), sb) /\
    (!x. pop = Var x ==> not_fresh_at sa x) /\
    eval_operand pop s = SOME (n2w p) /\
    s.vs_alloca_next < dimword (:256) /\
    (!k. 32 * k < LENGTH bs ==> p + off + 32 * k + 32 <= s.vs_alloca_next) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MSTORE)
      (emitted_insts sa sb) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_allocas = s.vs_allocas /\
        t.vs_alloca_next = s.vs_alloca_next /\
        t.vs_labels = s.vs_labels /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!a. a + 32 <= p + off ==> mload a t = mload a s)
Proof
  ntac 2 gen_tac >> completeInduct_on `LENGTH bs` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `v = LENGTH bs` SUBST_ALL_TAC >>
  Cases_on `bs`
  >- (gvs[compile_store_byte_chunks_def, comp_return_def,
          emitted_insts_def, same_blocks_def, run_inst_seq_def,
          run_inst_seq_mem_ok_def]) >>
  rename1 `compile_store_byte_chunks pop (h::bs) off sa = ((), sb)` >>
  `p + off + 32 <= s.vs_alloca_next /\
   !k. 32 * k < LENGTH (DROP 31 bs) ==>
       p + (off + 32) + 32 * k + 32 <= s.vs_alloca_next` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
     fs[LENGTH_DROP, ADD1, LEFT_ADD_DISTRIB]) >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_byte_chunks_def, comp_bind_def,
       comp_ignore_bind_def, LET_THM] >>
  Cases_on `emit_op ADD [pop; Lit (n2w off)] sa` >>
  rename1 `emit_op ADD _ sa = (dst, sm)` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >>
  qmatch_asmsub_abbrev_tac `emit_void MSTORE [_; Lit wd] sm` >>
  drule_all chunk_head_run_mem >> strip_tac >>
  qabbrev_tac `t0 = mstore (p + off) wd
    (update_var (STRING #"%" (toString sa.cs_next_var))
       (n2w p + n2w off) s)` >>
  `!x. not_fresh_at sa x ==> lookup_var x t0 = lookup_var x s` by
    (rpt strip_tac >> simp[Abbr `t0`, lookup_var_update_var] >>
     rw[] >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  `(!x. pop = Var x ==> not_fresh_at sh x) /\
   eval_operand pop t0 = SOME (n2w p)` by
    (conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     Cases_on `pop` >> gvs[eval_operand_def] >>
     simp[Abbr `t0`, lookup_var_def, mstore_def, update_var_def]) >>
  `t0.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `t0`] >>
  last_x_assum (qspec_then `LENGTH (DROP 31 bs)` mp_tac) >>
  impl_tac >- simp[LENGTH_DROP] >>
  disch_then (qspec_then `DROP 31 bs` mp_tac) >> simp[] >>
  disch_then drule >>
  disch_then (qspecl_then [`t0`, `p`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
      fs[LENGTH_DROP]) >>
  strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[]) >>
  qexists `t` >>
  conj_tac
  >- (qpat_x_assum `run_inst_seq (emitted_insts sa sh) s = OK t0`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  simp[Abbr `t0`] >>
  rpt strip_tac
  >- (`not_fresh_at sh x` by
        (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      simp[]) >>
  `a + 32 <= p + (off + 32)` by decide_tac >>
  simp[mload_mstore_apart]
QED

Theorem chunk_in_round[local]:
  !k n. 32 * k < n ==> 32 * k + 32 <= ((n + 31) DIV 32) * 32
Proof
  rpt strip_tac >>
  `k + 1 <= (n + 31) DIV 32` by simp[X_LE_DIV] >>
  decide_tac
QED

(* An ALLOCA's region change keeps the alloca invariant: the site's region
   is the one it held, or a fresh one at the old frontier. *)
Theorem alloca_fields_inv:
  !s A N id B n.
    FLOOKUP A id = SOME (B, n) /\
    (!a. a <> id ==> FLOOKUP A a = FLOOKUP s.vs_allocas a) /\
    B + n <= N /\ s.vs_alloca_next <= N /\
    (FLOOKUP s.vs_allocas id = NONE ==> B = s.vs_alloca_next) /\
    (!x. FLOOKUP s.vs_allocas id = SOME x ==> FST x = B /\ SND x = n) /\
    alloca_next_valid s ==>
    alloca_next_valid (s with <| vs_allocas := A; vs_alloca_next := N |>) /\
    (allocas_non_overlapping s ==>
     allocas_non_overlapping
       (s with <| vs_allocas := A; vs_alloca_next := N |>))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[alloca_next_valid_def] >> rpt gen_tac >>
      Cases_on `aid = id` >> simp[] >> strip_tac >>
      fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
  simp[allocas_non_overlapping_def] >> strip_tac >> rpt gen_tac >>
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (`B = s.vs_alloca_next` by simp[] >>
      Cases_on `a1 = id` >> Cases_on `a2 = id` >> gvs[] >>
      fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME x` >> PairCases_on `x` >>
  `x0 = B /\ x1 = n` by
    (first_x_assum (qspec_then `(x0, x1)` mp_tac) >> simp[]) >>
  gvs[] >>
  `FLOOKUP A a1 = FLOOKUP s.vs_allocas a1 /\
   FLOOKUP A a2 = FLOOKUP s.vs_allocas a2` by
    (Cases_on `a1 = id` >> Cases_on `a2 = id` >> gvs[]) >>
  fs[allocas_non_overlapping_def] >> metis_tac[]
QED

(* The literal's buffer: its ALLOCA, the length word at its base, and the
   chunks after it.  The buffer is the site's region, of the rounded size of
   the literal's type, so the length word and the rounded payload lie in it. *)
Theorem bytelike_literal_run_mem:
  !ctx func bs ml sa buf sb s.
    compile_bytelike_literal bs ml sa = (buf, sb) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
           [Lit (n2w (32 + ((ml + 31) DIV 32) * 32))]
           [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    LENGTH bs <= ml /\ 32 + ((ml + 31) DIV 32) * 32 < dimword (:256) /\
    alloca_room ctx func s /\ alloca_next_valid s /\
    (!x. FLOOKUP s.vs_allocas sa.cs_next_id = SOME x ==>
         SND x = 32 + ((ml + 31) DIV 32) * 32) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var < sb.cs_next_var /\
    sa.cs_next_id < sb.cs_next_id /\
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
               i.inst_opcode = MSTORE) (emitted_insts sa sb) /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    ?t B. run_inst_seq (emitted_insts sa sb) s = OK t /\
      lookup_var (STRING #"%" (toString sa.cs_next_var)) t = SOME (n2w B) /\
      mload B t = n2w (LENGTH bs) /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (B, 32 + ((ml + 31) DIV 32) * 32) /\
      (!a. a <> sa.cs_next_id ==>
           FLOOKUP t.vs_allocas a = FLOOKUP s.vs_allocas a) /\
      B + 32 + ((ml + 31) DIV 32) * 32 <= t.vs_alloca_next /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (FLOOKUP s.vs_allocas sa.cs_next_id = NONE ==> B = s.vs_alloca_next) /\
      (!x. FLOOKUP s.vs_allocas sa.cs_next_id = SOME x ==> B = FST x) /\
      alloca_room ctx func t /\ alloca_next_valid t /\
      (allocas_non_overlapping s ==> allocas_non_overlapping t) /\
      t.vs_labels = s.vs_labels /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `Z = 32 + ((ml + 31) DIV 32) * 32` >>
  qabbrev_tac `x0 = STRING #"%" (toString sa.cs_next_var)` >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp[compile_bytelike_literal_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `compile_store_byte_chunks _ bs 32 _ = (u, sb)` >> Cases_on `u` >>
  simp_tac std_ss [] >>
  qmatch_asmsub_abbrev_tac `compile_store_byte_chunks _ bs 32 sh = _` >>
  `sh.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w Z)] [x0];
      mk_inst (sa.cs_next_id + 1) MSTORE [Var x0; Lit (n2w (LENGTH bs))] []] /\
   same_blocks sa sh /\ sh.cs_next_var = sa.cs_next_var + 1 /\
   sh.cs_next_id = sa.cs_next_id + 2` by
    simp[Abbr `sh`, same_blocks_def] >>
  `!x. Var x0 = Var x ==> not_fresh_at sh x` by
    (simp[not_fresh_at_def, Abbr `x0`] >> rpt strip_tac >>
     fs[ASCIInumbersTheory.toString_11]) >>
  (* the ALLOCA *)
  qspecl_then [`ctx`, `func`, `sa.cs_next_id`, `Z`, `x0`, `s`]
    mp_tac alloca_step_props >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      `SND (b, m) = Z` by metis_tac[] >>
      fs[alloca_next_valid_def] >> res_tac >> fs[]) >>
  strip_tac >>
  qabbrev_tac `sa0 = s with <| vs_allocas := A; vs_alloca_next := N |>` >>
  `sa0.vs_allocas = A /\ sa0.vs_alloca_next = N` by simp[Abbr `sa0`] >>
  `alloca_room ctx func (update_var x0 (n2w B) sa0)` by
    (irule room_by_fields >> qexists `sa0` >> simp[]) >>
  `N < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `B < dimword (:256) /\ B + 32 <= N` by
    (qunabbrev_tac `Z` >> decide_tac) >>
  `w2n (n2w B : bytes32) = B` by metis_tac[w2n_n2w, LESS_MOD] >>
  qabbrev_tac `s2 = mstore B (n2w (LENGTH bs)) (update_var x0 (n2w B) sa0)` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) MSTORE
      [Var x0; Lit (n2w (LENGTH bs))] []) (update_var x0 (n2w B) sa0) =
   OK s2` by
    (qunabbrev_tac `s2` >>
     asm_simp_tac (srw_ss())
       [step_mstore_eq, eval_operand_def, lookup_var_update_var]) >>
  `s2.vs_allocas = A /\ s2.vs_alloca_next = N /\
   eval_operand (Var x0) s2 = SOME (n2w B)` by
    simp[Abbr `s2`, eval_operand_def, lookup_var_def, mstore_def,
         update_var_def, FLOOKUP_UPDATE] >>
  (* the chunks *)
  qspecl_then [`Var x0`, `bs`, `32`, `sh`, `sb`, `s2`, `B`] mp_tac
    store_chunks_run_mem >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `32 * k < ml` by decide_tac >>
      drule chunk_in_round >> qunabbrev_tac `Z` >> decide_tac) >>
  strip_tac >>
  `emitted_insts sa sh =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w Z)] [x0];
      mk_inst (sa.cs_next_id + 1) MSTORE [Var x0; Lit (n2w (LENGTH bs))] []]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s /\
   run_inst_seq (emitted_insts sa sb) s = OK t` by
    (asm_simp_tac std_ss [APPEND, run_inst_seq_def,
                          run_inst_seq_mem_ok_def] >>
     asm_simp_tac (std_ss ++ simpLib.type_ssfrag ``:exec_result``) [] >>
     asm_simp_tac (srw_ss())
       [below_frontier_MSTORE, below_frontier_no_ranges,
        dload_mk_inst_other, eval_operand_def, lookup_var_update_var]) >>
  `alloca_next_valid sa0 /\
   (allocas_non_overlapping s ==> allocas_non_overlapping sa0)` by
    (qunabbrev_tac `sa0` >>
     qspecl_then [`s`, `A`, `N`, `sa.cs_next_id`, `B`, `Z`] mp_tac
       alloca_fields_inv >>
     impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >>
     simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac >- simp[] >>
  conj_tac
  >- (asm_simp_tac (srw_ss()) [] >>
      qpat_x_assum `EVERY _ (emitted_insts sh sb)` mp_tac >>
      match_mp_tac MONO_EVERY >> simp[] >> rpt strip_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`t`, `B`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt conj_tac
  >- (`not_fresh_at sh x0` by simp[] >> simp[] >>
      simp[Abbr `s2`, lookup_var_def, mstore_def, update_var_def,
           FLOOKUP_UPDATE])
  >- (first_assum (qspec_then `B` mp_tac) >>
      simp[Abbr `s2`, mload_mstore_same])
  >- simp[]
  >- simp[]
  >- (qunabbrev_tac `Z` >> decide_tac)
  >- decide_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (irule room_by_fields >> qexists `s2` >> simp[] >>
      irule room_by_fields >> qexists `update_var x0 (n2w B) sa0` >>
      simp[Abbr `s2`])
  >- (fs[alloca_next_valid_def] >> metis_tac[])
  >- (strip_tac >> fs[allocas_non_overlapping_def] >>
      qpat_x_assum `_ ==> !a1 a2 b1 sz1 b2 sz2. _` mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `sa0.vs_allocas = A` (fn th => simp[th]))
  >- simp[Abbr `s2`, Abbr `sa0`]
  >- simp[Abbr `s2`, Abbr `sa0`]
  >- simp[Abbr `s2`, Abbr `sa0`]
  >- simp[Abbr `s2`, Abbr `sa0`] >>
  rpt strip_tac >>
  `not_fresh_at sh x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `x <> x0` by
    (fs[not_fresh_at_def, Abbr `x0`] >> first_x_assum irule >> simp[]) >>
  simp[Abbr `s2`, Abbr `sa0`, lookup_var_def, mstore_def, update_var_def,
       FLOOKUP_UPDATE]
QED
