Theory lowerDloadCoverageOrdinary
Ancestors
  lowerDloadOrdinaryNext lowerDloadControlPosition lowerDloadNormalData
  lowerDloadCoverageInvariant lowerDloadProvenanceSupport lowerDloadReachability
  lowerDloadNormalDispatch lowerDloadDefs lowerDloadOwnership
  ptrDiscipline memSafeRun unitMemInv o1PassContract
  venomInstProps venomExecSemantics venomExecProps venomState
  contextCodegenRel venomInst list rich_list

(* The prefix form gives the final j boundary by taking n = LENGTH ins.
   Only target executions are supplied: every later source anchor is produced. *)
Theorem ld_ordinary_segment_coverage:
  !ins T Q R F.
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn (HD (ins ++ [j])) s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!i. MEM i ins ==> (!v. MEM (Var v) i.inst_operands ==> v IN V)) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> RETURNDATACOPY /\
    MEM i.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY; SLOAD; SSTORE;
     TLOAD; TSTORE; ILOAD; ISTORE; PARAM; RETPC_PARAM; ASSIGN; NOP;
     INITIAL_FMP; BUMP; CALLER; CALLVALUE; CALLDATALOAD; CALLDATASIZE;
     CALLDATACOPY; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE; BALANCE;
     BLOCKHASH; BASEFEE; CODESIZE; CODECOPY; EXTCODESIZE; EXTCODEHASH;
     EXTCODECOPY; RETURNDATASIZE; RETURNDATACOPY; BLOBHASH; BLOBBASEFEE;
     SHA3; LOG; ASSERT; ASSERT_UNREACHABLE; OFFSET]) ins /\
  lower_dload_function_supply fa fn = (gn,fb) /\
  lower_dload_block_supply a bb = (gb,b) /\
  lower_dload_insts_supply a pre = (p,a1) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  bb.bb_instructions = pre ++ ins ++ j::post /\
  s.vs_inst_idx = LENGTH pre /\ t.vs_inst_idx = LENGTH p /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  T 0 = t /\ Q 0 = un /\
  (!h. h < LENGTH ins ==>
    step_inst (F h) CT (EL h ins) (T h) = OK (R h) /\
    T (SUC h) = (R h with vs_inst_idx := SUC (T h).vs_inst_idx) /\
    Q (SUC h) = step_taint (EL h ins) (T h) (R h) (Q h)) ==>
  !n. n <= LENGTH ins ==>
    ?sN AGN tnN.
      ld_annotated_reachable vs0 CS astk k L AP AGN tnN fn
        (EL n (ins ++ [j])) sN /\
      ld_normal_data CS fn V U lo E L H AP BP AGN
        (FOLDL (\g i. ld_step_prov BP g H i) BH (TAKE n ins))
        tnN (Q n) sN (T n) astk live keys d A suspended gstk f /\
      sN.vs_current_bb = s.vs_current_bb /\
      sN.vs_inst_idx = LENGTH pre + n /\
      (T n).vs_inst_idx = LENGTH p + n
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (strip_tac >> qexistsl_tac [`s`, `AG`, `tn`] >> gvs[]) >>
  strip_tac >>
  `n < LENGTH ins` by decide_tac >>
  qpat_x_assum `n <= _ ==> _` mp_tac >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_x_assum `ld_annotated_reachable _ _ _ _ _ _ _ _ _ (HD _) _` kall_tac >>
  qpat_x_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ s t _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `EVERY _ ins`
    (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  disch_then (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_x_assum `!h. _ ==> step_inst _ _ _ _ = _ /\ _`
    (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_x_assum `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ sN` mp_tac >>
  simp[EL_APPEND1] >> strip_tac >>
  `lookup_block sN.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb sN.vs_inst_idx = SOME (EL n ins)` by
    simp[get_instruction_def, EL_APPEND2, EL_APPEND1] >>
  `~in_revert_forward fn sN` by
    suspend "not_forward" >>
  rename1 `step_inst (Fs n) CT (EL n ins) (Ts n) = OK (Rs n)` >>
  `!v. MEM (Var v) (EL n ins).inst_operands ==> v IN V` by
    metis_tac[EL_MEM] >>
  `!u. step_inst (Fs n) CS (EL n ins) sN = OK u ==>
     active_inst fn (EL (SUC n) (ins ++ [j]))
       (u with vs_inst_idx := SUC sN.vs_inst_idx)` by
    suspend "successor_active" >>
  drule_all ld_normal_ordinary_next_backward >>
  disch_then (qspec_then `SUC (Ts n).vs_inst_idx` strip_assume_tac) >>
  `s'.vs_current_bb = sN.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  qexistsl_tac [`s' with vs_inst_idx := SUC sN.vs_inst_idx`,
    `ld_step_prov AP AGN L (EL n ins)`, `step_taint (EL n ins) sN s' tnN`] >>
  `TAKE (SUC n) ins = TAKE n ins ++ [EL n ins]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  qpat_x_assum `U = _` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (s' with vs_inst_idx := _) _ _ _ _ _ _ _ _ _` mp_tac >>
      asm_rewrite_tac[FOLDL_APPEND, FOLDL] >>
      BETA_TAC >> simp_tac pure_ss [arithmeticTheory.ADD_COMM] >>
      rewrite_tac[]) >>
  simp[]
QED

Resume ld_ordinary_segment_coverage[not_forward]:
  simp[in_revert_forward_def, revert_forward_at_def] >>
  rpt strip_tac >> gvs[revert_forward_pair_def] >>
  metis_tac[is_terminator_def]
QED

Resume ld_ordinary_segment_coverage[successor_active]:
  rpt strip_tac >>
  `u.vs_current_bb = sN.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = sN.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `SUC (n + LENGTH pre) - LENGTH pre = SUC n` by decide_tac >>
  simp[active_inst_def] >> qexists_tac `bb` >>
  Cases_on `SUC n < LENGTH ins`
  >- simp[EL_APPEND1, EL_APPEND2] >>
  `SUC n = LENGTH ins` by decide_tac >>
  `SUC (n + LENGTH pre) - (LENGTH ins + LENGTH pre) = 0` by decide_tac >>
  simp[EL_APPEND2]
QED

Finalise ld_ordinary_segment_coverage
