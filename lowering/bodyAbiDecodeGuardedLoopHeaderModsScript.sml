Theory bodyAbiDecodeGuardedLoopHeaderMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeLoopPhasesObserved
  bodyFullAbiDecodeLoopHeaderExact
  bodyFullAbiDecodeRelativeLoadExact
  bodyFullAbiDecodeInputOrigin
  fragExec fragGasPath venomState venomInst words finite_map
  typedMemoryCopy emitHelperProps stmtSimProps
  compileEnv emitHelper loweringShapeRules loweringStateRelDefs exprLoweringProps
  ptrDiscipline[qualified] fragGasSeqPtrContext[qualified]
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

fun extend_phase theorem additions =
  let
    val old = bodyAbiDecodeGuardedEffectSyntaxLib.beta (concl theorem)
    val (pre,post) = dest_imp old
    val (ws,body) = strip_exists post
    val tm = mk_imp (pre,list_mk_exists (ws,mk_conj (body,additions (free_vars old) ws)))
  in
    list_mk_forall (free_vars tm,tm)
  end;

val counter_effect = extend_phase abi_decode_loop_counter_load_exact
  (fn vs => fn ws =>
    let val tn = param vs "tn" and tnf = param ws "tnf"
    in ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
          ^tnf.t_imm = ^tn.t_imm`` end);

val load_effect = extend_phase abi_decode_owned_relative_load_exact
  (fn vs => fn ws =>
    let val tn = param vs "tn" and tnf = param ws "tnf"
        val s = param vs "s" and t = param ws "t"
        val sa = param vs "sa" and sc = param vs "sc" and ctx = param vs "ctx"
    in ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
          ^tnf.t_imm = ^tn.t_imm /\
          (!obs. fn_has_code ^sa ^sc obs ==> gas_path ^ctx obs ^s 0 (OK ^t))`` end);

val branch_effect =
  let
    val (pre, post) = dest_imp (concl abi_decode_loop_owned_branch_exact)
    val (ws, body) = strip_exists post
    val tn = param (free_vars pre) "tn" and tnf = param ws "tnf"
    val extra = ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
                  ^tnf.t_imm = ^tn.t_imm``
    val raw = mk_imp (pre,list_mk_exists(ws,list_mk_conj(strip_conj body @ strip_conj extra)))
  in
    list_mk_forall (free_vars raw,bodyAbiDecodeGuardedEffectSyntaxLib.beta raw)
  end;

(* All three contracts share the ownership data. Rebind only the cut-specific
   parameters, leaving the common parameters at their original names. *)
fun phase_at name bindings = asm_x name (mp_tac o Q.INST bindings o SPEC_ALL);

val header_effect =
  let
    val old = bodyAbiDecodeGuardedEffectSyntaxLib.beta (concl abi_decode_loop_header_observed)
    val (pre,post) = dest_imp old
    val (origin,post') = dest_imp post
    val (ws,body) = strip_exists post'
    val s = param (free_vars pre) "s"
    val tn = param (free_vars pre) "tn"
    val t = param ws "t"
    val tnf = param ws "tnf"
    val eff = ``abi_decode_guarded_effect_core ^s ^tn ^t ^tnf``
    val tm = mk_imp (pre,mk_imp(origin,list_mk_exists(ws,mk_conj(body,eff))))
  in
    list_mk_forall(free_vars tm,tm)
  end;

(* Select the three normal endpoints before choosing a horizon or observer.
   The relative load's raw PC witness is used only to transport FMP safety. *)
Theorem abi_decode_loop_header_observed_effect_from_phases_mods:
  ^counter_effect ==> ^load_effect ==> ^branch_effect ==> ^header_effect
Proof
  rpt gen_tac >>
  disch_then (mk_asm "counter") >>
  disch_then (mk_asm "load") >>
  disch_then (mk_asm "branch") >>
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_tac >>
  `s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (!i. w2n (n2w cell :256 word) <= i /\
     i < w2n (n2w cell :256 word)+32 ==> i NOTIN tn.t_mem) /\
   w2n (n2w cell :256 word)+32 <= s.vs_alloca_next` by simp[] >>
  phase_at "counter" [`out` |-> `idx`, `a` |-> `n2w cell`] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu`
    (qx_choose_then `tu` (map_every assume_tac o CONJUNCTS)))) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `emit_op MLOAD [Var _] _ = (Var _,_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[emit_op_eq] >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (qpat_assum `sa.cs_next_var <= sb.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at sb input /\ local_ptrs_reserved ce sb /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x)` by
    (conj_tac >- simp[] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb x` irule >>
     (qpat_assum `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
        (drule_then ACCEPT_TAC) ORELSE
      qpat_assum `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
        (drule_then ACCEPT_TAC))) >>
  `eval_operand src u = SOME (n2w srcoff) /\ op_taint tu src = {}` by
    (qpat_assum `eval_operand src s = SOME (n2w srcoff)` mp_tac >>
     qpat_assum `op_taint tn src = {}` mp_tac >>
     qpat_assum `!x. src = Var x ==> not_fresh_at sa x` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `u.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `src` >>
     rw[eval_operand_def] >> fs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `srcoff+32 <= LENGTH input_bytes` by
    (qpat_assum `srcoff + 32 + n * asz <= h` mp_tac >>
     qpat_assum `h <= LENGTH input_bytes` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `allocas_from lo u` by
    (simp[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`allocas_below_fmp u <=> allocas_below_fmp s` by
       simp[ptrDisciplineTheory.allocas_below_fmp_def] >> simp[]) >>
  phase_at "load" [`sa` |-> `sb`, `sb` |-> `sc`, `sc` |-> `sd`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
    `pos` |-> `src`, `p` |-> `srcoff`, `v` |-> `count_op`] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `count_var` (qx_choose_then `v` (qx_choose_then `Gv`
    (qx_choose_then `tv` (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `?raw. run_inst_seq _ _ = OK raw /\ _` strip_assume_tac >>
  suspend "branch"
QED

Resume abi_decode_loop_header_observed_effect_from_phases_mods[branch]:
  `emit_op ADD [Var input;src] sb = (addr,sc)` by
    (qpat_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abiEncoderTheory.compile_abi_dec_addr_def]) >>
  `sb.cs_next_var <= sd.cs_next_var /\ not_fresh_at sb idx` by
    (qpat_assum `emit_op MLOAD _ sa = _` mp_tac >>
     qpat_assum `emit_op ADD _ sb = _` mp_tac >>
     qpat_assum `emit_op MLOAD _ sc = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_op_eq, not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at sb x ==> not_fresh_at sd x` by
    (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sb` >> asm_rewrite_tac[]) >>
  `not_fresh_at sd input /\ local_ptrs_reserved ce sd /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    (conj_tac >- simp[] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[]) >>
     conj_tac >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sb x ==> not_fresh_at sd x` irule >>
     (qpat_assum `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x`
        (drule_then ACCEPT_TAC) ORELSE
      qpat_assum `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x`
        (drule_then ACCEPT_TAC))) >>
  `mload (w2n (n2w cell :256 word)) s = n2w j` by
    simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, w2n_n2w,
         arithmeticTheory.LESS_MOD] >>
  `lookup_var idx u = SOME (n2w j) /\ FLOOKUP Gu idx = NONE` by
    (qpat_assum `eval_operand (Var idx) u = SOME (mload _ s)` mp_tac >>
     qpat_assum `op_prov Gu (Var idx) = NONE` mp_tac >>
     pure_rewrite_tac[eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
     asm_rewrite_tac[] >> simp[]) >>
  `mload (w2n input_word + srcoff) u = n2w n` by
    (pure_rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
     asm_rewrite_tac[]) >>
  `lookup_var idx v = SOME (n2w j) /\ FLOOKUP Gv idx = NONE /\
   op_taint tv (Var idx) = {} /\ eval_operand count_op v = SOME (n2w n)` by
    (Q.UNDISCH_THEN `!x. not_fresh_at sb x ==>
       lookup_var x v = lookup_var x u /\ FLOOKUP Gv x = FLOOKUP Gu x /\
       op_taint tv (Var x) = op_taint tu (Var x)`
       (qspec_then `idx` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `eval_operand count_op v = SOME (mload _ u)` mp_tac >>
     asm_rewrite_tac[]) >>
  `allocas_from lo v` by
    (simp[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` (drule_then assume_tac) >>
     qpat_assum `v = _ with vs_inst_idx := _` SUBST1_TAC >>
     pure_rewrite_tac[allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_updates] >>
     irule fragGasSeqPtrContextTheory.run_inst_seq_allocas_below_fmp >>
     goal_assum (drule_at Any) >> qexists_tac `emitted_insts sb sd` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `inst_extends sb sc /\ inst_extends sc sd` by
       (conj_tac >> irule inst_extends_emit_op >> goal_assum drule >> simp[]) >>
     `emitted_insts sb sd = emitted_insts sb sc ++ emitted_insts sc sd` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     qpat_assum `emit_op ADD _ sb = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ sc = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def, is_alloca_op_def]) >>
  phase_at "branch" [`sa` |-> `sd`, `sb` |-> `se`, `sc` |-> `sf`, `sd` |-> `sg`,
    `s` |-> `v`, `G` |-> `Gv`, `tn` |-> `tv`,
    `counter` |-> `idx`, `length` |-> `count_op`, `exit` |-> `exit_lbl`] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gland`
    (qx_choose_then `tt` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "join"
QED

Resume abi_decode_loop_header_observed_effect_from_phases_mods[join]:
  `!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP Gland p = FLOOKUP G p /\
    op_taint tt (Var p) = op_taint tn (Var p)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sb p /\ not_fresh_at sd p` by simp[] >>
     ntac 3 (qpat_x_assum `!x. not_fresh_at _ x ==> lookup_var x _ = _ /\ _`
       (qspec_then `p` (fn th => mp_tac th >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac))) >>
     asm_rewrite_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   tt.t_mem = tn.t_mem` by asm_rewrite_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (gen_tac >> strip_tac >>
     qpat_assum `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `eval_operand src t = eval_operand src s /\
   eval_operand hi t = eval_operand hi s` by
    (conj_tac >> (irule stmtSimReturnTheory.eval_operand_old_vars >>
     (reverse conj_tac >- first_assum ACCEPT_TAC) >>
     qexists_tac `sa` >> asm_rewrite_tac[])) >>
  `eval_operand src t = SOME (n2w srcoff) /\
   eval_operand hi t = SOME (n2w h)` by asm_rewrite_tac[] >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,Gland,tt)` by
    (rpt strip_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> conj_tac >- simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gv`,`v`,`tv`] >> simp[]) >>
  `!obs. fn_has_code sa sg obs ==> gas_path ctx obs s 0 (OK t)` by suspend "observer" >>
  qexistsl_tac [`t`,`Gland`,`tt`] >>
  reverse conj_tac >- simp[abi_decode_guarded_effect_core_def] >>
  conj_tac
  >- (irule abi_decode_input_origin_transport >> qexistsl_tac [`s`,`sa`] >>
      asm_rewrite_tac[] >> rpt strip_tac >> simp[]) >>
  asm_rewrite_tac[] >> simp[]
QED

Resume abi_decode_loop_header_observed_effect_from_phases_mods[observer]:
  rpt strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\
   cs_extends sd se /\ cs_extends se sf /\ cs_extends sf sg` by
    (qpat_assum `emit_op MLOAD _ sa = _` mp_tac >>
     qpat_assum `emit_op ADD _ sb = _` mp_tac >>
     qpat_assum `emit_op MLOAD _ sc = _` mp_tac >>
     qpat_assum `emit_op LT _ sd = _` mp_tac >>
     qpat_assum `emit_op ISZERO _ se = _` mp_tac >>
     qpat_assum `emit_inst JNZ _ _ sf = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[typed_copy_emit_op_mono, ci_mono_def, cs_extends_emit_inst]) >>
  `cs_extends sb sd /\ cs_extends sd sg /\ cs_extends sb sg` by
    (qpat_assum `cs_extends sb sc` mp_tac >>
     qpat_assum `cs_extends sc sd` mp_tac >>
     qpat_assum `cs_extends sd se` mp_tac >>
     qpat_assum `cs_extends se sf` mp_tac >>
     qpat_assum `cs_extends sf sg` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sb obs /\ fn_has_code sb sg obs` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `fn_has_code sb sd obs /\ fn_has_code sd sg obs` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `gas_path ctx obs s 0 (OK u)` by simp[] >>
  `gas_path ctx obs u 0 (OK v)` by simp[] >>
  `gas_path ctx obs v 0 (OK t)` by simp[] >>
  qpat_assum `gas_path ctx obs s 0 (OK u)` mp_tac >>
  qpat_assum `gas_path ctx obs u 0 (OK v)` mp_tac >>
  qpat_assum `gas_path ctx obs v 0 (OK t)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[gas_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []]
QED

Finalise abi_decode_loop_header_observed_effect_from_phases_mods
