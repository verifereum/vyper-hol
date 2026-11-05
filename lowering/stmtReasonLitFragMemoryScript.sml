(* Counted memory-safe raise and assert with a string literal reason: the
   literal's buffer (stmtReasonLitMemory) feeds the reason encoder
   (stmtReasonMemory), which runs to its REVERT below the frontier. *)
Theory stmtReasonLitFragMemory
Ancestors
  stmtReasonLitMemory stmtReasonMemory stmtSimDefs stmtSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasContext fragGasMode gasCount
  fragGasPathMem stmtLowering compileEnv emitHelper emitHelperProps
  loweringSlice exprLoweringProps exprLowering context vyperInterpreter
  vyperState vyperValue vyperValueOperation vyperAST venomInst venomState venomExecSemantics venomMemDefs
  fragExec fragExecMem instMemFrontier freshWrites
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

(* Code emitted into the current block lies, from the point where st left
   off, in the function's block, and among its instructions. *)
Theorem fn_has_code_code:
  !sa sb func code.
    fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ code ==>
    ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX code (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
         !i. MEM i code ==> MEM i (fn_insts func)
Proof
  rw[fn_has_code_def] >> qexists `bb` >> gvs[IS_PREFIX_APPEND] >>
  simp[DROP_APPEND1, DROP_LENGTH_NIL] >> rpt strip_tac >>
  irule lookup_block_fn_insts >> qexistsl [`bb`, `sa.cs_current_bb`] >>
  simp[]
QED

Theorem store_chunks_shape[local]:
  !pop bs off sa u sb.
    compile_store_byte_chunks pop bs off sa = (u, sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?rest. sb.cs_current_insts = sa.cs_current_insts ++ rest
Proof
  ntac 2 gen_tac >> completeInduct_on `LENGTH bs` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `v = LENGTH bs` SUBST_ALL_TAC >>
  Cases_on `bs`
  >- gvs[compile_store_byte_chunks_def, comp_return_def, same_blocks_def] >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_byte_chunks_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def, LET_THM] >>
  strip_tac >>
  last_x_assum (qspec_then `LENGTH (DROP 31 t)` mp_tac) >>
  impl_tac >- simp[LENGTH_DROP] >>
  disch_then (qspec_then `DROP 31 t` mp_tac) >> simp[] >>
  disch_then drule >> strip_tac >> fs[same_blocks_def] >>
  metis_tac[APPEND_ASSOC]
QED

(* The literal's buffer starts with its ALLOCA. *)
Theorem bytelike_literal_shape:
  !bs ml sa buf sb.
    compile_bytelike_literal bs ml sa = (buf, sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
    sa.cs_next_var < sb.cs_next_var /\ sa.cs_next_id < sb.cs_next_id /\
    ?rest. sb.cs_current_insts = sa.cs_current_insts ++
      mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + ((ml + 31) DIV 32) * 32))]
        [STRING #"%" (toString sa.cs_next_var)] :: rest
Proof
  rpt gen_tac >>
  simp[compile_bytelike_literal_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule store_chunks_shape >> strip_tac >> fs[same_blocks_def] >>
  qexists `mk_inst (sa.cs_next_id + 1) MSTORE
     [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w (LENGTH bs))] []
     :: rest` >> simp[]
QED

(* A site's region has the size its ALLOCA asks for. *)
Theorem state_rel_site_size:
  !ctx func cenv cx es s id n outs.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] outs) (fn_insts func) /\
    n < dimword (:256) ==>
    !x. FLOOKUP s.vs_allocas id = SOME x ==> SND x = n
Proof
  rpt strip_tac >> PairCases_on `x` >> fs[stmt_state_rel_def] >>
  first_x_assum (qspecl_then [`mk_inst id ALLOCA [Lit (n2w n)] outs`,
                              `n2w n`, `x0`, `x1`] mp_tac) >>
  simp[mk_inst_def]
QED

(* A site other than the literal's keeps its region through the literal's
   code, of the size its ALLOCA asks for. *)
Theorem other_site_size[local]:
  !ctx func cenv cx es s0 t1 b id n outs.
    stmt_state_rel ctx func cenv cx es s0 /\
    (!a. a <> b ==> FLOOKUP t1.vs_allocas a = FLOOKUP s0.vs_allocas a) /\
    b < id /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] outs) (fn_insts func) /\
    n < dimword (:256) ==>
    !x. FLOOKUP t1.vs_allocas id = SOME x ==>
        SND x = n /\ FLOOKUP s0.vs_allocas id = SOME x
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `id <> b` by decide_tac >>
  `FLOOKUP s0.vs_allocas id = SOME x` by metis_tac[] >>
  drule_all state_rel_site_size >> metis_tac[]
QED

Theorem alloca_add_mstore_opcodes[local]:
  !l. EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
                 i.inst_opcode = MSTORE) l ==>
      EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                 (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT)) l
Proof
  Induct >> rw[] >> rpt (qpat_x_assum `is_terminator _` mp_tac) >>
  asm_simp_tac (srw_ss()) [is_terminator_def]
QED

(* The literal's buffer and the reason encoder after it run, from a state
   at the start of that code, to the encoder's REVERT below the frontier. *)
Theorem lit_reason_revert_path_mem:
  !ctx func cenv cx es s0 str ml mt sa buf sm sb.
    compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf, sm) /\
    compile_revert_with_reason cenv
      (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) mt
      (32 + ((ml + 31) DIV 32) * 32) sm = ((), sb) /\
    fn_has_code sa sb func /\
    LENGTH str <= ml /\ 32 + ((ml + 31) DIV 32) * 32 < 2 ** 64 /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s0 0 (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_revert_reason_shape >>
  disch_then (qx_choosel_then [`op`, `sn`] strip_assume_tac) >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, base_ptr_def, is_word_type_def,
       comp_return_def] >> strip_tac >>
  qpat_x_assum `_ = sn` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = op` (SUBST_ALL_TAC o SYM) >>
  drule bytelike_literal_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sm.cs_current_insts = sa.cs_current_insts ++ LA :: rest` >>
  `emitted_insts sa sm = LA :: rest` by
    (rewrite_tac[emitted_insts_def] >> asm_rewrite_tac[] >>
     rewrite_tac[DROP_LENGTH_APPEND]) >>
  qabbrev_tac `ecode = reason_head sm.cs_next_id sm.cs_next_var
                       (32 + ((ml + 31) DIV 32) * 32) ++
                     reason_tail (sm.cs_next_id + 4) (sm.cs_next_var + 3)
                       sm.cs_next_var buf.buf_operand` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ (emitted_insts sa sm ++ ecode)` by
    (qpat_x_assum `sb = _` SUBST1_TAC >>
     simp[Abbr `ecode`]) >>
  qspecl_then [`sa`, `sb`, `func`, `emitted_insts sa sm ++ ecode`] mp_tac
    fn_has_code_code >>
  impl_tac >- simp[] >>
  strip_tac >>
  `!i. MEM i ecode ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> qpat_assum `!i. MEM i _ ==> MEM i (fn_insts func)` irule >>
     simp[]) >>
  `32 + ((ml + 31) DIV 32) * 32 < 2 ** 64` by first_assum ACCEPT_TAC >>
  `64 + (32 + ((ml + 31) DIV 32) * 32) < dimword (:256) /\
   32 + ((ml + 31) DIV 32) * 32 < dimword (:256)` by
    (qpat_x_assum `_ < 2 ** 64` mp_tac >> simp[dimword_def]) >>
  `alloca_room ctx func s0 /\ alloca_next_valid s0 /\
   allocas_non_overlapping s0` by fs[stmt_state_rel_def, alloca_inv_def] >>
  (* the literal's buffer *)
  `MEM LA (fn_insts func)` by
    (qpat_assum `!i. MEM i (emitted_insts sa sm ++ ecode) ==>
                     MEM i (fn_insts func)` irule >>
     rewrite_tac[MEM_APPEND] >> disj1_tac >> asm_rewrite_tac[MEM]) >>
  qpat_x_assum `Abbrev (LA = _)` (assume_tac o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!x. FLOOKUP s0.vs_allocas sa.cs_next_id = SOME x ==>
       SND x = 32 + ((ml + 31) DIV 32) * 32` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `sa.cs_next_id`,
                  `32 + ((ml + 31) DIV 32) * 32`,
                  `[STRING #"%" (toString sa.cs_next_var)]`] mp_tac
       state_rel_site_size >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_x_assum `LA = _` (fn th => REWRITE_TAC [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  (* the literal's buffer *)
  qspecl_then [`ctx`, `func`, `MAP (n2w o ORD) str`, `ml`, `sa`, `buf`, `sm`,
               `s0`] mp_tac bytelike_literal_run_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_x_assum `LA = _` (fn th => REWRITE_TAC [GSYM th]) >>
          first_assum ACCEPT_TAC) >>
      simp[]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s0 = OK t1` >>
  qabbrev_tac `Z = 32 + ((ml + 31) DIV 32) * 32` >>
  qabbrev_tac `id0 = sm.cs_next_id` >> qabbrev_tac `v0 = sm.cs_next_var` >>
  `32 <= Z` by simp[Abbr `Z`] >>
  `allocas_non_overlapping t1` by metis_tac[] >>
  `MEM (mk_inst id0 ALLOCA [Lit (n2w (64 + Z))] ["%" ++ toString v0])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 3) ALLOCA [Lit (n2w Z)] ["%" ++ toString (v0 + 2)])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 4 + 5) ALLOCA [Lit 32w] ["%" ++ toString (v0 + 3 + 4)])
       (fn_insts func)` by
    (rpt conj_tac >>
     qpat_assum `!i. MEM i ecode ==> MEM i (fn_insts func)` irule >>
     simp[Abbr `ecode`, reason_head_def, reason_tail_def]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `(LENGTH str + 31) DIV 32 <= (ml + 31) DIV 32` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  (* the reason encoder, from the literal's buffer *)
  qspecl_then [`ctx`, `func`, `id0`, `v0`, `buf.buf_operand`, `t1`, `B`,
               `LENGTH str`, `Z`] mp_tac reason_encoder_run_mem >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (gen_tac >> strip_tac >>
          qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `t1`,
                       `sa.cs_next_id`, `id0`, `64 + Z`,
                       `["%" ++ toString v0]`] mp_tac other_site_size >>
          impl_tac >- simp[Abbr `id0`] >>
          disch_then drule >> strip_tac >> simp[] >>
          PairCases_on `x` >> fs[allocas_non_overlapping_def] >>
          `sa.cs_next_id <> id0` by simp[Abbr `id0`] >>
          first_x_assum (qspecl_then [`sa.cs_next_id`, `id0`, `B`, `Z`,
                                      `x0`, `x1`] mp_tac) >>
          simp[])
      >- (gen_tac >> strip_tac >>
          qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `t1`,
                       `sa.cs_next_id`, `id0 + 3`, `Z`,
                       `["%" ++ toString (v0 + 2)]`] mp_tac other_site_size >>
          impl_tac >- simp[Abbr `id0`] >>
          disch_then drule >> simp[])
      >- (gen_tac >> strip_tac >>
          qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `t1`,
                       `sa.cs_next_id`, `id0 + 4 + 5`, `32`,
                       `["%" ++ toString (v0 + 3 + 4)]`] mp_tac
            other_site_size >>
          impl_tac >- simp[Abbr `id0`] >>
          disch_then drule >> strip_tac >> simp[] >>
          gen_tac >> strip_tac >>
          `SND y = Z` by
            (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `id0 + 3`,
                          `Z`, `["%" ++ toString (v0 + 2)]`] mp_tac
               state_rel_site_size >>
             impl_tac >- simp[] >> disch_then drule >> simp[]) >>
          PairCases_on `x` >> PairCases_on `y` >> fs[] >>
          qpat_x_assum `allocas_non_overlapping s0`
            (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
          disch_then (qspecl_then [`id0 + 4 + 5`, `id0 + 3`, `x0`, `x1`,
                                   `y0`, `y1`] mp_tac) >>
          simp[])
      >- (simp[] >> rpt strip_tac >> fs[ASCIInumbersTheory.toString_11])
      >- simp[]
      >- simp[eval_operand_def]
      >- simp[]
      >- (qunabbrev_tac `Z` >> decide_tac) >>
      qunabbrev_tac `Z` >> decide_tac) >>
  strip_tac >>
  `ecode = reason_head id0 v0 Z ++
           reason_tail (id0 + 4) (v0 + 3) v0 buf.buf_operand` by
    simp[Abbr `ecode`] >>
  `run_inst_seq (emitted_insts sa sm ++ ecode) s0 = Abort Revert_abort t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s0 = OK t1`
       (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th] >> assume_tac th) >>
     qpat_assum `ecode = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm ++ ecode) s0` by
    (irule run_inst_seq_mem_ok_append >> reverse conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     `s' = t1` by
       (rpt (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s0 = _` mp_tac) >>
        simp_tac (srw_ss()) []) >>
     qpat_x_assum `s' = t1` SUBST1_TAC >>
     qpat_assum `ecode = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT))
     (emitted_insts sa sm ++ ecode)` by
    (rewrite_tac[EVERY_APPEND] >> conj_tac
     >- (irule alloca_add_mstore_opcodes >> first_assum ACCEPT_TAC) >>
     qpat_assum `ecode = _` SUBST1_TAC >>
     rewrite_tac[EVERY_APPEND, reason_encoder_ops]) >>
  qspecl_then [`emitted_insts sa sm ++ ecode`, `s0`, `t`, `Revert_abort`,
               `ctx`, `func`, `bb`] mp_tac run_inst_seq_revert_path_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_assum `s0.vs_current_bb = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC) >>
      qpat_assum `s0.vs_inst_idx = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexists_tac `t with vs_inst_idx := j` >>
  pop_assum mp_tac >> simp_tac (srw_ss()) [gas_marked_path_def]
QED

Theorem compile_raise_reason_lit_frag_mem:
  !d ctx func cx lctx RetQ cenv ty ml str es.
    LENGTH str <= ml /\
    type_memory_bytes cenv (BaseT (StringT ml)) < 2 ** 64 ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      (eval_stmt cx
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_reason_message_def, expr_type_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml sa` >>
  rename1 `compile_bytelike_literal _ _ sa = (buf, sm)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_revert_with_reason cenv VV MT MS sm` >>
  Cases_on `compile_revert_with_reason cenv VV MT MS sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, sc)` >> Cases_on `u` >>
  simp[] >> strip_tac >>
  qpat_x_assum `sc = sb` SUBST_ALL_TAC >>
  `MS = 32 + ((ml + 31) DIV 32) * 32` by
    simp[Abbr `MS`, Abbr `MT`, type_memory_bytes_def] >>
  qpat_x_assum `Abbrev (MS = _)` kall_tac >>
  qpat_x_assum `MS = _` SUBST_ALL_TAC >>
  qunabbrev_tac `VV` >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `str`, `ml`, `MT`,
               `sa`, `buf`, `sm`, `sb`] mp_tac lit_reason_revert_path_mem >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` assume_tac) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp_tac (srw_ss()) [gas_summary_at_def, gas_marked_exec_def,
                       gas_marked_path_def] >>
  qexistsl_tac [`INR (AssertException str)`, `es`, `Abort Revert_abort t`] >>
  conj_tac
  >- (conj_tac >- (
        gen_tac >> qunabbrev_tac `MT` >>
        simp_tac (srw_ss()) [Once evaluate_def] >>
        simp_tac (srw_ss()) [Once evaluate_def, evaluate_literal_def,
          bind_def, return_def, read_result_def, lift_option_type_def,
          dest_StringV_def, raise_def]) >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >>
  simp_tac (srw_ss()) [exit_result_def, stmt_exit_def, expr_exit_def]
QED
