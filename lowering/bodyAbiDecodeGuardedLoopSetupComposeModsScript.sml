Theory bodyAbiDecodeGuardedLoopSetupComposeMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeLoopPhasesObserved bodyFullAbiDecodeLoopSetupExact
  bodyFullAbiDecodeLoopHeaderExact bodyFullAbiDecodeLoopSourceExact
  bodyFullAbiDecodeLoopSelectExact bodyFullAbiDecodeLoopDestinationExact
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeInputOrigin
  fragGasPath fragGasOriginPtr decoderArraySetupPtr
  abiDecoderReentry abiDecoderIndexedAddress freshWrites
  exprLoweringProps placeMemoryCodeLayout loweringShapeRules
  ptrDiscipline venomState venomInst fragExec words list rich_list arithmetic
  compileEnv loweringStateRelDefs valueEncodingProps fragGasSeqPtrContext
  decoderGhostFramePtr exprSimCopy
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

local
  open bodyAbiDecodeGuardedEffectSyntaxLib
  fun map_result f tm = let val (a,b) = dest_imp tm in mk_imp (a,f b) end
  fun map_normal f tm = let val (a,b) = dest_disj tm in mk_disj (a,f b) end
  fun add_frame taint_name frame template =
    let
      val tn = param (free_vars template) "tn"
      val (vs,body) = strip_exists template
      val tf = param vs taint_name
    in list_mk_exists (vs,mk_conj (body,frame vs tn tf)) end
  fun fields _ tn tf =
    ``^tf.t_stor = ^tn.t_stor /\ ^tf.t_trans = ^tn.t_trans /\ ^tf.t_imm = ^tn.t_imm``
  fun mold raw =
    let val vars = free_vars (beta raw)
        val eq = beta_conv (list_mk_forall (vars,raw))
    in (rhs (concl eq), REWR_CONV (GSYM eq)) end
  fun phase result taint_name th =
    mold (map_result (result (add_frame taint_name fields)) (concl th))
  val observed_setup = concl abi_decode_loop_setup_observed
  fun setup_frame tm =
    let
      val s = param (free_vars tm) "s"
    in add_frame "tnu" (fn vs => fn tn => fn tf => effect s tn (param vs "u") tf) tm end
in
  val (counter_phase,fold_counter) = phase I "tnf" abi_decode_loop_counter_load_exact
  val (source_phase,fold_source) = phase I "tnu" abi_decode_loop_source_joint_exact
  val (select_phase,fold_select) = phase map_normal "tnu" abi_decode_loop_select_joint_exact
  val (destination_phase,fold_destination) = phase I "tnu" abi_decode_loop_destination_joint_exact
  val (setup_effect,fold_setup) = mold (checked "observed setup" observed_setup
    (map_result (map_result (map_normal setup_frame)) observed_setup))
end;

Theorem setup_source_observed[local]:
  emit_op ADD [src;Lit 32w] a = (data,b) /\
  emit_op MUL [idx;Lit (n2w asz)] b = (offset,c) /\
  emit_op ADD [data;offset] c = (head,d) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a d) s = OK v ==>
  (!obs. fn_has_code a d obs ==>
    gas_path ctx obs s 0 (OK (v with vs_inst_idx := LENGTH d.cs_current_insts))) /\
  (allocas_below_fmp s ==> allocas_below_fmp v)
Proof
  strip_tac >>
  qpat_assum `emit_op ADD _ a = _`
    (strip_assume_tac o MATCH_MP emit_op_facts) >>
  qpat_assum `emit_op MUL _ b = _`
    (strip_assume_tac o MATCH_MP emit_op_facts) >>
  qpat_assum `emit_op ADD _ c = _`
    (strip_assume_tac o MATCH_MP emit_op_facts) >>
  `d.cs_current_insts = a.cs_current_insts ++ emitted_insts a d /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts a d) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts a d)) = 0` by
    (pure_asm_rewrite_tac [emitted_insts_def, GSYM APPEND_ASSOC,
       DROP_LENGTH_APPEND, APPEND] >> simp[mk_inst_def, is_terminator_def]) >>
  `d.cs_current_bb = a.cs_current_bb` by simp[] >>
  conj_tac >-
    (match_mp_tac (GEN_ALL abi_decode_finite_success_observed) >>
     qexists_tac `emitted_insts a d` >> asm_rewrite_tac[]) >>
  strip_tac >> irule run_inst_seq_allocas_below_fmp >>
  qexistsl_tac [`emitted_insts a d`,`s`] >> asm_rewrite_tac[] >>
  qpat_x_assum `d.cs_current_insts = a.cs_current_insts ++ emitted_insts a d` kall_tac >>
  pure_asm_rewrite_tac [emitted_insts_def, GSYM APPEND_ASSOC,
    DROP_LENGTH_APPEND, APPEND] >> simp[mk_inst_def,is_terminator_def,is_alloca_op_def]
QED

Theorem setup_live_operand_frame[local]:
  abi_decoder_operand_live st.cs_next_var op /\ t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
  op_taint tf op = op_taint tn op
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def,not_fresh_at_def]) >>
  drule_all old_operand_ghost_frame >> simp[]
QED

Theorem setup_origin_then[local]:
  gas_origin_ptr_path env (s,G,tn) [] (OK t,Gf,tf) /\
  gas_origin_ptr_path env (t,Gf,tf) [] (r,Gr,tr) ==>
  gas_origin_ptr_path env (s,G,tn) [] (r,Gr,tr)
Proof
  metis_tac[gas_origin_ptr_path_append,APPEND]
QED

Theorem setup_observer_then[local]:
  gas_path ctx obs s 0 (OK t) /\ gas_path ctx obs t 0 r ==>
  gas_path ctx obs s 0 r
Proof
  metis_tac[Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then |> SIMP_RULE bool_ss [ADD_CLAUSES]]
QED

Theorem setup_observer_cuts[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ cs_extends d e ==>
  !obs. fn_has_code a e obs ==>
    fn_has_code a b obs /\ fn_has_code b c obs /\
    fn_has_code c d obs /\ fn_has_code d e obs
Proof
  rpt strip_tac >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

Theorem setup_reserve_mono[local]:
  sa.cs_next_var <= sb.cs_next_var /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  not_fresh_at sb input /\ local_ptrs_reserved ce sb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x)
Proof
  metis_tac[not_fresh_at_mono,local_ptrs_reserved_next_var]
QED

Theorem setup_old_frame_then[local]:
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x midS = lookup_var x s /\
    FLOOKUP midG x = FLOOKUP G x /\ op_taint midT (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at sb x ==> lookup_var x endS = lookup_var x midS /\
    FLOOKUP endG x = FLOOKUP midG x /\ op_taint endT (Var x) = op_taint midT (Var x)) ==>
  !x. not_fresh_at sa x ==> lookup_var x endS = lookup_var x s /\
    FLOOKUP endG x = FLOOKUP G x /\ op_taint endT (Var x) = op_taint tn (Var x)
Proof
  metis_tac[not_fresh_at_mono]
QED

Theorem abi_decode_loop_setup_effect_observed_conditional:
  ^counter_phase ==> ^source_phase ==> ^select_phase ==> ^destination_phase ==>
  ^setup_effect
Proof
  disch_then (mk_asm "counter") >> disch_then (mk_asm "source") >>
  disch_then (mk_asm "select") >> disch_then (mk_asm "destination") >>
  CONV_TAC fold_setup >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  drule abi_decode_loop_setup_segments >> strip_tac >>
  drule_all abi_decode_loop_setup_code >> strip_tac >>
  `cs_extends s1 s4` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `!obs. fn_has_code sa sb obs ==>
     fn_has_code sa s1 obs /\ fn_has_code s1 s4 obs /\
     fn_has_code s4 s5 obs /\ fn_has_code s5 sb obs` by
    (match_mp_tac setup_observer_cuts >> asm_rewrite_tac[]) >>
  `?out. idx = Var out` by
    (qpat_assum `emit_op MLOAD _ sa = (idx,s1)` (mp_then Any strip_assume_tac emit_op_next_var) >>
     goal_assum (drule_at Any)) >>
  pop_assum strip_assume_tac >> qpat_x_assum `idx = Var out` SUBST_ALL_TAC >>
  `(!i. w2n (n2w cell:bytes32) <= i /\
         i < w2n (n2w cell:bytes32)+32 ==> i NOTIN tn.t_mem) /\
   w2n (n2w cell:bytes32)+32 <= s.vs_alloca_next` by simp[] >>
  asm_x "counter" (mp_tac o Q.INST [`sb` |-> `s1`,`a` |-> `n2w cell`] o
    SPEC_ALL o CONV_RULE fold_counter) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> BETA_TAC >>
     qpat_assum `_ live protected sa s G tn` (assume_tac o BETA_RULE) >>
     asm_rewrite_tac[])) >> strip_tac >>
  `not_fresh_at s1 input /\ local_ptrs_reserved ce s1 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (irule setup_reserve_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live s1.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live s1.cs_next_var (Var out)` by
    (qpat_assum `emit_op MLOAD _ sa = (Var out,s1)`
      (mp_then Any ACCEPT_TAC abi_decoder_operand_live_emit)) >>
  `eval_operand src t = SOME (n2w srcoff) /\
   op_prov Gf src = NONE /\ op_taint tnf src = {}` by
    (`eval_operand src t = eval_operand src s /\ op_prov Gf src = op_prov G src /\
      op_taint tnf src = op_taint tn src` suffices_by simp[] >>
     irule setup_live_operand_frame >> conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `eval_operand (Var out) t = SOME (n2w j)` by
    simp[w2n_n2w,LESS_MOD,GSYM mem_word_at_eq_mload] >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (assume_tac o REWRITE_RULE[allocas_below_fmp_def]) >>
     asm_rewrite_tac[allocas_below_fmp_def]) >>
  asm_x "source" (mp_tac o Q.INST
    [`sa` |-> `s1`,`s1` |-> `s2`,`s2` |-> `s3`,`sb` |-> `s4`,
     `s` |-> `t`,`G` |-> `Gf`,`tn` |-> `tnf`,`idx` |-> `Var out`] o
    SPEC_ALL o CONV_RULE fold_source) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `(!obs. fn_has_code s1 s4 obs ==> gas_path ctx obs t 0 (OK u)) /\
   (allocas_below_fmp t ==> allocas_below_fmp v)` by
    (qpat_assum `u = v with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `emit_op ADD _ s1 = _`
       (mp_then (Pos hd) mp_tac setup_source_observed) >>
     disch_then (qpat_assum `emit_op MUL _ s2 = _` o mp_then (Pos hd) mp_tac) >>
     disch_then (qpat_assum `emit_op ADD _ s3 = _` o mp_then (Pos hd) mp_tac) >>
     disch_then (qspecl_then [`v`,`t`,`ctx`] mp_tac) >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`allocas_below_fmp u <=> allocas_below_fmp v` by
       (qpat_assum `u = v with vs_inst_idx := _` SUBST1_TAC >>
        simp[allocas_below_fmp_def]) >>
     strip_tac >> asm_rewrite_tac[] >>
     qpat_assum `allocas_below_fmp t ==> allocas_below_fmp v` irule >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` irule >>
     asm_rewrite_tac[]) >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!obs. fn_has_code sa sb obs ==> _ /\ _` drule >> strip_tac >>
     irule setup_observer_then >> qexists_tac `t` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)` by
    (gen_tac >> irule setup_origin_then >> qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)` by
    (match_mp_tac (Q.INST [`sb` |-> `s1`,`midS` |-> `t`, `midG` |-> `Gf`,
      `midT` |-> `tnf`] setup_old_frame_then) >> asm_rewrite_tac[]) >>
  suspend "select"
QED

Resume abi_decode_loop_setup_effect_observed_conditional[select]:
  `not_fresh_at s4 input /\ local_ptrs_reserved ce s4 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x)` by
    (irule setup_reserve_mono >> qexists_tac `s1` >> asm_rewrite_tac[]) >>
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var /\
   s1.cs_next_var <= s5.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live s4.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  `eval_operand hi u = SOME (n2w h) /\
   op_prov Gu hi = NONE /\ op_taint tnu hi = {}` by
    (`eval_operand hi u = eval_operand hi s /\ op_prov Gu hi = op_prov G hi /\
      op_taint tnu hi = op_taint tn hi` suffices_by simp[] >>
     irule setup_live_operand_frame >> conj_tac >- simp[] >>
     qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `srcoff+32+j*asz+asz <= h /\ srcoff+32+j*asz <= h /\
   srcoff+32+j*asz+asz <= LENGTH input_bytes` by
    (match_mp_tac (Q.INST [`n` |-> `n`] abi_decode_loop_setup_window) >> asm_rewrite_tac[]) >>
  `h < dimword (:256) /\
   (dec_info_needs_offset ei ==> srcoff+32+j*asz+32 <= LENGTH input_bytes)` by
    (conj_tac >- decide_tac >> strip_tac >>
     qpat_assum `dec_info_needs_offset ei ==> _` drule >> decide_tac) >>
  asm_x "select" (mp_tac o Q.INST
    [`sa` |-> `s4`, `sb` |-> `s5`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`,
     `p` |-> `srcoff+32+j*asz`, `dw` |-> `n2w (srcoff+32)`] o
    SPEC_ALL o CONV_RULE fold_select) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac
  >- suspend "reject" >>
  suspend "destination"
QED

Resume abi_decode_loop_setup_effect_observed_conditional[reject]:
  disj1_tac >> qexistsl_tac [`t'`,`Gf'`,`tnf'`] >> conj_tac
  >- (gen_tac >> irule setup_origin_then >> qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!obs. fn_has_code sa sb obs ==> _ /\ _` drule >> strip_tac >>
  irule setup_observer_then >> qexists_tac `u` >> simp[]
QED

Resume abi_decode_loop_setup_effect_observed_conditional[destination]:
  `!x. not_fresh_at sa x ==> lookup_var x u' = lookup_var x s /\
     FLOOKUP Gu' x = FLOOKUP G x /\ op_taint tnu' (Var x) = op_taint tn (Var x)` by
    (match_mp_tac (Q.INST [`sb` |-> `s4`,`midS` |-> `u`,`midG` |-> `Gu`,
       `midT` |-> `tnu`] setup_old_frame_then) >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at s1 x ==> lookup_var x u' = lookup_var x t /\
     FLOOKUP Gu' x = FLOOKUP Gf x /\ op_taint tnu' (Var x) = op_taint tnf (Var x)` by
    (match_mp_tac (Q.INST [`sb` |-> `s4`,`midS` |-> `u`,`midG` |-> `Gu`,
       `midT` |-> `tnu`] setup_old_frame_then) >> asm_rewrite_tac[]) >>
  `not_fresh_at s5 input /\ local_ptrs_reserved ce s5 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x)` by
    (irule setup_reserve_mono >> qexists_tac `s4` >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live s5.cs_next_var (Var dst)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live s5.cs_next_var (Var out)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `s1.cs_next_var` >> simp[]) >>
  `not_fresh_at sa dst` by
    (qpat_assum `abi_decoder_operand_live sa.cs_next_var (Var dst)`
      (mp_tac o SIMP_RULE (srw_ss()) [abi_decoder_operand_live_def,
         abi_decoder_older_vars_def,not_fresh_at_def]) >> simp[not_fresh_at_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u' = _ /\ _`
    (qspec_then `dst` drule) >> strip_tac >>
  `ptr_covers Gu' tnu' dst u' (32+n*msz)` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> asm_rewrite_tac[]) >>
  `eval_operand (Var out) u' = SOME (n2w j) /\
   op_prov Gu' (Var out) = NONE /\ op_taint tnu' (Var out) = {}` by
    (`eval_operand (Var out) u' = eval_operand (Var out) t /\
      op_prov Gu' (Var out) = op_prov Gf (Var out) /\
      op_taint tnu' (Var out) = op_taint tnf (Var out)` suffices_by simp[] >>
     irule setup_live_operand_frame >> conj_tac >- simp[] >>
     qexists_tac `s1` >> asm_rewrite_tac[]) >>
  `allocas_from lo u'` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  asm_x "destination" (mp_tac o Q.INST [`sa` |-> `s5`, `s` |-> `u'`,
    `G` |-> `Gu'`, `tn` |-> `tnu'`, `idx` |-> `Var out`] o
    SPEC_ALL o CONV_RULE fold_destination) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "success"
QED

Resume abi_decode_loop_setup_effect_observed_conditional[success]:
  `!op. abi_decoder_operand_live s5.cs_next_var op ==>
     eval_operand op u'' = eval_operand op u' /\ op_prov Gu'' op = op_prov Gu' op /\
     op_taint tnu'' op = op_taint tnu' op` by
    (gen_tac >> strip_tac >> irule setup_live_operand_frame >> conj_tac >- simp[] >>
     qexists_tac `s5` >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live s5.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `s4.cs_next_var` >> simp[]) >>
  qpat_assum `!op. abi_decoder_operand_live s5.cs_next_var op ==> _`
    (fn th => map_every (fn qt => qspec_then qt drule th >> strip_tac)
       [`Var out`, `child_src`, `hi`]) >>
  `s5.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `abi_decode_indexed_address _ _ _ s5 = _`
      (mp_then Any strip_assume_tac abi_decode_indexed_address_counters) >> simp[]) >>
  `abi_decoder_operand_live sb.cs_next_var (Var out)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `s5.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live sb.cs_next_var child_src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `s5.cs_next_var` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u'' = lookup_var x s /\
     FLOOKUP Gu'' x = FLOOKUP G x /\ op_taint tnu'' (Var x) = op_taint tn (Var x)` by
    (match_mp_tac (Q.INST [`sb` |-> `s5`,`midS` |-> `u'`,`midG` |-> `Gu'`,
       `midT` |-> `tnu'`] setup_old_frame_then) >> asm_rewrite_tac[]) >>
  `!name b k. local_region ce es.scopes u'' name b k ==>
     cell+32 <= b \/ b+k <= cell` by
    (`!name b k. local_region ce es.scopes u'' name b k <=>
       local_region ce es.scopes s name b k` by
       (rpt gen_tac >> metis_tac[copy_buffer_local_region_frame]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!name b k. local_region ce es.scopes s name b k ==> _`
       (qspecl_then [`name`,`b`,`k`] irule) >>
     qpat_assum `!name b k. local_region ce es.scopes u'' name b k <=> _`
       (qspecl_then [`name`,`b`,`k`] (fn th => REWRITE_TAC[GSYM th])) >>
     (metis_tac[])) >>
  suspend "assemble"
QED

Resume abi_decode_loop_setup_effect_observed_conditional[assemble]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u',Gu',tnu')` by
    (gen_tac >> irule setup_origin_then >> qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u'',Gu'',tnu'')` by
    (gen_tac >> irule setup_origin_then >> qexistsl_tac [`Gu'`,`u'`,`tnu'`] >> simp[]) >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u'')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!obs. fn_has_code sa sb obs ==> _ /\ _` drule >> strip_tac >>
     `gas_path ctx obs s 0 (OK u')` by
       (irule setup_observer_then >> qexists_tac `u` >> simp[]) >>
     irule setup_observer_then >> qexists_tac `u'` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`u''`,`Gu''`,`tnu''`,`q`,`child`] >>
  BETA_TAC >> conj_tac
  >- (conj_tac
      >- (qpat_assum `(λs. _) s` (fn th => DISJ_CASES_TAC (BETA_RULE th)) >>
       qpat_assum `u''.vs_allocas = u'.vs_allocas` (fn th => once_rewrite_tac[th]) >>
       qpat_assum `u'.vs_allocas = u.vs_allocas` (fn th => once_rewrite_tac[th]) >>
       qpat_assum `u.vs_allocas = t.vs_allocas` (fn th => once_rewrite_tac[th]) >>
       qpat_assum `t.vs_allocas = s.vs_allocas` (fn th => once_rewrite_tac[th]) >>
       `!name b k. local_region ce es.scopes u'' name b k <=>
          local_region ce es.scopes s name b k` by
         (rpt gen_tac >> metis_tac[copy_buffer_local_region_frame]) >>
       asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
      qpat_assum `_ sb u'' Gu'' tnu''` (assume_tac o BETA_RULE) >>
      asm_rewrite_tac[] >> simp[]) >>
  simp[abi_decode_guarded_effect_core_def]
QED

Finalise abi_decode_loop_setup_effect_observed_conditional
