Theory bodyAbiDecodeLoopBodySetupCutMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeLoopPhasesObserved
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  gasOriginPtrLabels abiDecoderCoherence abiDecoderMemberInfos abiDecoderReentry
  abiDecoderOffset abiEncoder compileEnv venomInst venomExecSemantics venomState
  loweringStateRelDefs stateRelProj words list rich_list finite_map arithmetic
  valueEncodingProps abiStaticAggregateProps ptrDiscipline robustCopyTransportPtr fragGasPath
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeRuntimeLoopSyntaxLib

val counter_live =
  ``(aid:num,counter:string,cell:num,32:num,mem_bytes_at cell 32 s.vs_memory)::live``;
val prefix_protected =
  ``(d,mem_bytes_at d (32+k*msz) s.vs_memory)::protected``;
val setup_preparation = ``
  not_fresh_at anchor counter /\ not_fresh_at anchor input /\
  local_ptrs_reserved ce loop_body /\ not_fresh_at loop_body input /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
  abi_decoder_operand_live loop_body.cs_next_var hi /\ SUC k * msz <= n * msz``;

(* Both packets are cut from the checked setup/body interfaces. *)
val (setup_all, setup_cut_statement) =
  let
    val beta = bodyAbiDecodeGuardedEffectSyntaxLib.beta
    val old = concl abi_decode_loop_setup_observed
    val vs = free_vars old
    val (entry, origin_imp) = dest_imp old
    val (origin, result) = dest_imp origin_imp
    val (abort, normal) = dest_disj result
    val (ws, core) = strip_exists normal
    val (s,tn,u,tu) = (param vs "s", param vs "tn", param ws "u", param ws "tnu")
    val normal_effect = mk_conj (core, effect s tn u tu)
    val setup = beta (mk_imp (entry, mk_imp (origin,
      mk_disj (abort, list_mk_exists (ws, normal_effect)))))
    val all_setup = list_mk_forall (free_vars setup, setup)
    val (params, body) = strip_forall (guarded_effect_length_body_typed ())
    val (body_entry, body_result) = dest_imp body
    val (body_abort, _) = dest_disj body_result
    val normal_cut = beta (subst
      [param vs "sa" |-> param params "loop_body",
       param vs "sb" |-> param params "child",
       param vs "j" |-> param params "k",
       param vs "live" |-> counter_live,
       param vs "protected" |-> prefix_protected]
      (list_mk_exists (ws, mk_conj (normal_effect, setup_preparation))))
  in (all_setup, list_mk_forall (params,
          mk_imp (body_entry, mk_disj (body_abort, normal_cut)))) end;

Triviality setup_cut_snapshots:
  (^loop_resource) anchor k s G tn /\ not_fresh_at anchor counter /\
  anchor.cs_next_var <= loop_body.cs_next_var /\
  anchor.cs_next_id <= loop_body.cs_next_id ==>
  (^owned_decoder_state) ^counter_live ^prefix_protected loop_body s G tn
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?inst. MEM inst (fn_insts fn) /\ _ /\ _ /\ inst.inst_id = output_id`
    (qx_choose_then `inst` strip_assume_tac) >>
  asm_rewrite_tac[EVERY_DEF] >> simp[] >>
  conj_tac >-
    (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < anchor.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\ _) live` mp_tac >>
     qpat_assum `anchor.cs_next_id <= loop_body.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >> simp[] >> decide_tac) >>
  conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `EVERY (\(id,p,b,k,bytes). not_fresh_at anchor p) live` mp_tac >>
  qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem abi_decode_loop_body_setup_cut_conditional:
  ^setup_all ==> ^setup_cut_statement
Proof
  disch_then (mk_asm "setup") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. V H` (qx_choose_then `valid_H` assume_tac) >>
  `not_fresh_at anchor counter /\ not_fresh_at anchor input` by
    (qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var counter)` mp_tac >>
     qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var input)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, pred_setTheory.GSPECIFICATION] >> metis_tac[]) >>
  drule_all setup_cut_snapshots >> disch_then (assume_tac o BETA_RULE) >>
  qpat_assum `(^loop_resource) anchor k s G tn`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `local_ptrs_reserved ce loop_body /\ not_fresh_at loop_body input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x)` by
    (qpat_assum `local_ptrs_reserved ce anchor` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> _` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> _` mp_tac >>
     qpat_assum `not_fresh_at anchor input` mp_tac >>
     qpat_assum `origin.cs_next_var <= anchor.cs_next_var` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `abi_decoder_operand_live loop_body.cs_next_var src /\
   abi_decoder_operand_live loop_body.cs_next_var hi /\
   abi_decoder_operand_live loop_body.cs_next_var (Var dst) /\
   abi_decoder_operand_live loop_body.cs_next_var (Var counter)` by
    (qpat_assum `abi_decoder_operand_live _ src` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ hi` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var dst)` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var counter)` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
  `dec_info_needs_offset ei ==> 32 <= asz` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `ei = _` mp_tac >> qpat_assum `asz = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule abi_decoder_coherent_header >>
     drule abiDecoderDynamicTheory.abi_decoder_coherent_dynamic >>
     gvs[abi_decoder_header_def, abi_decoder_needs_offset_iff,
       abiDecodeRangesTheory.abi_member_head_size_def]) >>
  `cell < dimword (:256)` by
    (qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ s /\ _` drule >>
     strip_tac >>
     drule stmt_state_rel_alloca_room >>
     disch_then (mp_then Any mp_tac exprLoweringPropsTheory.alloca_room_next_lt) >>
     decide_tac) >>
  `asz < dimword (:256)` by
    (qpat_assum `srcoff+32+n*asz <= h` mp_tac >>
     qpat_assum `h <= LENGTH input_bytes` mp_tac >>
     qpat_assum `w2n input_word+LENGTH input_bytes < dimword (:256)` mp_tac >>
     qpat_assum `k<n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `n` >> simp[ADD1, RIGHT_ADD_DISTRIB] >> decide_tac) >>
  `lookup_var dst s = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var dst) s = SOME (n2w d)` mp_tac >>
     pure_rewrite_tac[eval_operand_def] >> disch_then irule) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     MATCH_ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `SUC k * msz <= n * msz` by (simp[LE_MULT_RCANCEL] >> decide_tac) >>
  asm_x "setup" (mp_tac o Q.INST [
    `sa` |-> `loop_body`, `sb` |-> `child`, `j` |-> `k`,
    `live` |-> `^counter_live`, `protected` |-> `^prefix_protected`] o SPEC_ALL) >>
  (impl_tac >- (BETA_TAC >> asm_rewrite_tac[])) >>
  (impl_tac >- (first_assum (ACCEPT_TAC o BETA_RULE))) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
       (qx_choose_then `q` (qx_choose_then `child_ptr`
         (map_every assume_tac o CONJUNCTS)))))))
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >> conj_tac
      >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
      rpt strip_tac >>
      qpat_assum `!obs. fn_has_code anchor _ obs ==> _` drule >>
      strip_tac >>
      qpat_assum `!obs. fn_has_code loop_body child obs ==> gas_path _ _ _ _ _`
        MATCH_MP_TAC >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`u`,`Gu`,`tnu`,`q`,`child_ptr`] >>
  asm_rewrite_tac[]
QED
