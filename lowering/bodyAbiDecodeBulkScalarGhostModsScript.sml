Theory bodyAbiDecodeBulkScalarGhostMods
Ancestors
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeOwnedStateProps
  bodyFullAbiDecodeClampMemory bodyFullAbiDecodeFiniteObserved
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  instSeqPtrLo fragGasOriginPtrDead fragGasOriginPtrLoop ghostPcTransportPtr
  exprSimWordBuiltins[qualified,ignore_grammar]
  abiDecoderBulk abiDecodePtrPrims exprLoweringProps freshWrites emitHelperProps
  stateFrame venomState venomExecSemantics venomInst ptrDiscipline
  loweringStateRelDefs loweringShapeRules emitHelper compileEnv abiDecoderReentry
  bodyPtrDefs words arithmetic list rich_list finite_map pred_set

(* Recover the existing owned-state syntax from its frame rule. *)
val owned_decoder_state =
  #1 (strip_comb (snd (dest_imp (concl abi_decode_owned_scalar_frame_with_history_lower))));

val scalar_statement =
  let
    val raw = ``
      emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
      emit_op ADD [src;Lit 32w] sm = (data,sb) /\
      eval_operand cnt s = SOME (n2w n) /\ eval_operand src s = SOME (n2w off) /\
      abi_decoder_operand_live sa.cs_next_var src /\
      op_prov G cnt = NONE /\ op_prov G src = NONE /\
      op_taint tn cnt = {} /\ op_taint tn src = {} /\
      fn_has_code sa sb fn /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
      not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
      ?u Gf tnf.
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
               (s,G,tn) [] (OK u,Gf,tnf)) /\
        (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (^owned_decoder_state) sb u Gf tnf /\
        u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
        u.vs_alloca_next = s.vs_alloca_next /\
        eval_operand copy_sz u = SOME (n2w (n*msz)) /\
        eval_operand data u = SOME (n2w (off+32)) /\
        op_prov Gf data = NONE /\ op_taint tnf data = {} /\
        op_taint tnf copy_sz = {} /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
            FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
        tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
        tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm``
    val tm = rhs (concl (DEPTH_CONV BETA_CONV raw))
  in list_mk_forall (free_vars tm,tm) end;

Theorem bulk_scalar_code[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) ==>
  bop_scalar_seq {x | not_fresh_at sa x}
    (cnt INSERT src INSERT {op | ?w. op = Lit w})
    (emitted_insts sa sb)
    (data INSERT copy_sz INSERT cnt INSERT src INSERT {op | ?w. op = Lit w}) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >>
  drule (Q.SPEC `MUL` emitted_insts_emit_op) >> strip_tac >>
  drule (Q.SPEC `ADD` emitted_insts_emit_op) >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule bop_scalar_seq_append >>
      qexists_tac `copy_sz INSERT cnt INSERT src INSERT {op | ?w. op = Lit w}` >>
      simp[] >> conj_tac >> irule bop_scalar_seq_single >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by metis_tac[emit_op_facts] >>
  simp[mk_inst_def, inst_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem bulk_scalar_raw[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand src s = SOME (n2w off) /\
  abi_decoder_operand_live sa.cs_next_var src ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand copy_sz t = SOME (n2w (n*msz)) /\
    eval_operand data t = SOME (n2w (off+32))
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `eval_operand src
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (n*msz)) s) =
   eval_operand src s` by
    (irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  gvs[MULT_COMM] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       ASCIInumbersTheory.toString_inj, word_mul_n2w, word_add_n2w, MULT_COMM]
QED

(* Fix the concrete MUL/ADD state, then select ghosts on that exact run. *)
Theorem abi_decode_bulk_scalar_joint_exact_mods:
  ^scalar_statement
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bulk_scalar_code >> strip_tac >>
  drule_all bulk_scalar_raw >> strip_tac >>
  `!op. op IN (cnt INSERT src INSERT {op | ?w. op = Lit w}) ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  qpat_x_assum `?H. V H` (qx_choose_then `Hv` assume_tac) >>
  qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (qspec_then `Hv` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel Hv _ _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  drule_all (bop_scalar_seq_run |> Q.INST
    [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
                 d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  drule bop_scalar_seq_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[abi_decode_scalar_seq_mem_ok] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post u. emitted_insts sa sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >> simp[] >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "resources_and_observer"
QED

Resume abi_decode_bulk_scalar_joint_exact_mods[resources_and_observer]:
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_memory = s.vs_memory` by
    (simp[Abbr `u`] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`,lookup_var_def,op_taint_def] >> gvs[]) >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[] >> gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- (BETA_TAC >> asm_rewrite_tac[]) >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> BETA_TAC >> asm_rewrite_tac[]) >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
    (rpt strip_tac >>
     qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     irule abi_decode_finite_success_observed >>
     simp[] >> qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
     fs[inst_extends_def,LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]) >>
  `eval_operand copy_sz u = SOME (n2w (n*msz)) /\
   eval_operand data u = SOME (n2w (off+32))` by
    simp[Abbr `u`,eval_operand_inst_idx] >>
  qpat_assum `!op. op IN data INSERT copy_sz INSERT _ ==> _`
    (fn th => map_every (fn opnd =>
      qspec_then opnd (strip_assume_tac o SIMP_RULE (srw_ss()) []) th)
      [`data`, `copy_sz`]) >>
  qpat_x_assum `(^owned_decoder_state) sb u G' tn'` (assume_tac o BETA_RULE) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[Abbr `u`]) >>
  asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[]
QED

Finalise abi_decode_bulk_scalar_joint_exact_mods
