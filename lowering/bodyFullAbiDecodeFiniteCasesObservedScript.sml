Theory bodyFullAbiDecodeFiniteCasesObserved
Ancestors bodyPtrBopScalarSeq[qualified,ignore_grammar]
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeFiniteCases
  bodyFullAbiDecodeInputOrigin calldataOverwritePtr
  assignTuplePtrStoreWord exprSimProps emitHelperProps
  fragGasSeqPtr exprLoweringProps venomInst venomExecSemantics pred_set words
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeLeafCases stateRelProj
  stateFrame wordLoadStorePtr bodyPtrDefs compileEnv loweringStateRelDefs
  venomState finite_map list rich_list valueEncodingProps exprSimCopy
  abiDecodePtrMemberFrame bodyFullAbiDecodeRelativeLoadExact
  fragExec fragGasPath fragGasOriginPtrLoop loweringShapeRules
  abiDecoderReentry abiDecoderCoherence abiDecodeRanges abiEncoder
  exprLowering builtinAbi freshWrites venomMemDefs combin pair
  bodyFullAbiDecodeGuardReadObserved abiDecodePtrBytesMember
  abiDecoderBytestringCases abiDecoderBytesRuntime
  emitHelper ptrDiscipline bodyFullAbiDecodeOwnedWordStoreObserved
  abiBoundedBytesExecution varsExt appendStorageStageTransportPtr
  bodyFullAbiDecodeScalarObserved fragGasOriginPtr forPtrAllocationFrame
  bodyFullAbiDecodeOwnedCopyEffect abiEncoderWindowLeaves[qualified]
  bodyFullAbiDecodeArrayBulkWindow[qualified]

(* Same owned-state quotation as the finite constructor contracts. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val input_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
     FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
     w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

val guarded_observed_pre = ``\start finish dst src opc base_op hi info env sf ty tv d s G tn.
  abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes /\
     ((?clamp. info = DecPrimWord clamp) ==>
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
  compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (d-d+type_memory_size tv) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= d /\ d+type_memory_size tv <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+type_memory_size tv <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= d \/ d+type_memory_size tv <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+type_memory_size tv <= a) protected /\
  (^owned_decoder_state) start s G tn /\
  EVERY (\(a,bytes). output_base <= a /\ a+LENGTH bytes <= output_base+output_cap) protected /\
  (^input_origin) s``;

val guarded_observed_post = ``\start finish s G tn tv d.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
       (^input_origin) t /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tn'.t_mem ==>
         i IN tn.t_mem) /\
       (!v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
         !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
           val_in_memory tv v d mem)) \/
     (?t. r = Abort Revert_abort t))``;

Theorem abi_decode_bytes_case_observed_conditional:
  !dst src opc base_op hi n env sf ty tv live protected start finish s G tn d.
    (^guarded_observed_pre) start finish dst src opc base_op hi (DecBytestring n)
      env sf ty tv d s G tn ==>
    (^guarded_observed_post) start finish s G tn tv d
Proof
  rpt gen_tac >>
  qabbrev_tac `OS = (^owned_decoder_state)` >>
  qabbrev_tac `IO = (^input_origin)` >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size tv = 32+32*((n+31) DIV 32)` by
    (drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >>
     gvs[valueEncodingTheory.type_memory_size_def,vfmConstantsTheory.word_size_def]) >>
  `output_base+output_cap < dimword (:256)` by fs[Abbr `OS`] >>
  `n+31 < dimword (:256)` by
    (mp_tac (abi_decode_bytes_round_bounds |> Q.INST [`c` |-> `n`]) >> decide_tac) >>
  rename1 `fn_has_code start fin fn` >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _` kall_tac >>
  qpat_x_assum `?off h. _`
    (qx_choose_then `off` (qx_choose_then `h` (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `dstv` strip_assume_tac) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`dst = Var dstv`, `base_op = Var input`, `opc = MLOAD`] >>
  drule_all abi_decode_bytes_member_phases >>
  disch_then (qx_choose_then `head` (qx_choose_then `addr` (qx_choose_then `cnt`
    (qx_choose_then `sh` (qx_choose_then `sa` (qx_choose_then `sl`
      (qx_choose_then `sc` (qx_choose_then `sg` strip_assume_tac)))))))) >>
  `cs_extends start sh /\ cs_extends sh sa /\ cs_extends sa sl /\
   cs_extends sl sc /\ cs_extends sc sg /\ cs_extends sg fin` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND]) >>
  `cs_extends sh sl /\ cs_extends sl fin /\ cs_extends sc fin /\
   cs_extends sh fin` by metis_tac[cs_extends_trans] >>
  `fn_has_code start sh fn /\ fn_has_code sh sl fn /\ fn_has_code sl sc fn /\
   fn_has_code sc sg fn /\ fn_has_code sg fin fn` by
    (map_every (fn args => qspecl_then args mp_tac
       fragExecTheory.fn_has_code_split >> simp[] >> strip_tac)
       [[`start`,`sh`,`fin`,`fn`], [`sh`,`sl`,`fin`,`fn`],
        [`sl`,`sc`,`fin`,`fn`], [`sc`,`sg`,`fin`,`fn`]] >> simp[]) >>
  `h < dimword (:256)` by decide_tac >>
  `allocas_from lo s /\ origin.cs_next_var <= start.cs_next_var` by
    (fs[Abbr `OS`] >> metis_tac[ghost_inv_at_def]) >>
  `not_fresh_at start input /\ not_fresh_at start dstv` by
    fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_bytes_head_joint_observed)) >>
  reverse (disch_then (qspecl_then [`explicit`,`PG`]
    (DISJ_CASES_THEN2
      (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `Tu` strip_assume_tac)))
      (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac))))))
  >- (qexistsl_tac [`Abort Revert_abort z`,`Gz`,`Tz`] >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      qspecl_then [`start`,`sh`,`fin`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
      simp[] >> strip_tac >> simp[]) >>
  (* Continue from the successful head guard. *)
  `start.cs_next_var <= sh.cs_next_var` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
       compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK u,Gu,Tu)`
       (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP
          gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `eval_operand src u = SOME (n2w off) /\ op_taint Tu src = {}` by
    (qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_assum `u.vs_labels = s.vs_labels` mp_tac >>
     qpat_assum `eval_operand src s = SOME (n2w off)` mp_tac >>
     qpat_assum `op_taint tn src = {}` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
          not_fresh_at_def,eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `not_fresh_at sh input /\ local_ptrs_reserved ce sh /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `off+32 <= LENGTH input_bytes` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_bytes_owned_load_frame_joint_observed)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `out` (qx_choose_then `ar` (qx_choose_then `v`
      (qx_choose_then `Gv` (qx_choose_then `Tv` strip_assume_tac)))))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,Gv,Tv)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`Tu`] >> simp[]) >>
  `!obs. fn_has_code start sl obs ==> gas_path ctx obs s 0 (OK v)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sh`,`sl`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
     simp[] >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists_tac `u` >> simp[]) >>
  (* Continue from the loaded byte count. *)
  `sh.cs_next_var <= sl.cs_next_var` by
    (`emit_op ADD [Var input;src] sh = (addr,sa)` by
       fs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     decide_tac) >>
  `not_fresh_at sl input /\ local_ptrs_reserved ce sl /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  qmatch_asmsub_abbrev_tac `eval_operand cnt v = SOME wc` >>
  qabbrev_tac `c = w2n wc` >>
  `wc = (n2w c:bytes32) /\ c < dimword (:256) /\ n < dimword (:256)` by
    (simp[Abbr `c`,w2n_lt] >> decide_tac) >>
  `eval_operand cnt v = SOME (n2w c)` by simp[] >>
  `abi_decoder_operand_live sl.cs_next_var cnt` by
    fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_bytes_count_joint_observed)) >>
  reverse (disch_then (qspecl_then [`explicit`,`PG`]
    (DISJ_CASES_THEN2
      (qx_choose_then `w` (qx_choose_then `Gw` (qx_choose_then `Tw` strip_assume_tac)))
      (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac))))))
  >- (`cs_extends start sl` by metis_tac[cs_extends_trans] >>
      qexistsl_tac [`Abort Revert_abort z`,`Gz`,`Tz`] >> conj_tac
      >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
          qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[]) >>
      conj_tac
      >- (qx_gen_tac `obs` >> disch_tac >>
          qspecl_then [`start`,`sl`,`fin`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
          simp[] >> strip_tac >>
          qspecl_then [`sl`,`sc`,`fin`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
          simp[] >> strip_tac >>
          irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
          qexists_tac `v` >> simp[]) >>
      disj2_tac >> qexists_tac `z` >> simp[]) >>
  (* Continue with the payload on the successful count check. *)
  `sl.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abiDecoderGuardTheory.abi_decode_le_guard_def,emit_op_def,emit_void_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `abi_decoder_operand_live sh.cs_next_var head` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
          compile_abi_decode_range_check_def,emit_op_def,emit_void_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def] >> rpt strip_tac >>
     gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK w,Gw,Tw)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[]) >>
  `cs_extends start sl` by metis_tac[cs_extends_trans] >>
  `!obs. fn_has_code start sc obs ==> gas_path ctx obs s 0 (OK w)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sl`,`sc`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
     simp[] >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists_tac `v` >> simp[]) >>
  `v.vs_labels = u.vs_labels /\ w.vs_labels = v.vs_labels` by
    (conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,Tu) _ (OK v,Gv,Tv)`
           (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,Gv,Tv) _ (OK w,Gw,Tw)`
       (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `not_fresh_at sc input /\ local_ptrs_reserved ce sc /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`sl.cs_next_var <= sc.cs_next_var`, `not_fresh_at sl input`,
        `local_ptrs_reserved ce sl`,
        `!x sz. ce.ce_return_buf = _ ==> not_fresh_at sl x`,
        `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sl x`] >>
     rpt (pop_assum kall_tac) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var]) >>
  `!op. abi_decoder_operand_live sh.cs_next_var op ==>
     eval_operand op w = eval_operand op u /\
     op_prov Gw op = op_prov Gu op /\ op_taint Tw op = op_taint Tu op` by
    (qpat_assum `!x. not_fresh_at sh x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sl x ==> _` mp_tac >>
     qpat_assum `sh.cs_next_var <= sl.cs_next_var` mp_tac >>
     qpat_assum `v.vs_labels = u.vs_labels` mp_tac >>
     qpat_assum `w.vs_labels = v.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
         not_fresh_at_def,eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
     eval_operand op w = eval_operand op s /\
     op_prov Gw op = op_prov G op /\ op_taint Tw op = op_taint tn op` by
    (qpat_assum `!x. not_fresh_at start x ==> _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live sh.cs_next_var op ==> _` mp_tac >>
     qpat_assum `start.cs_next_var <= sh.cs_next_var` mp_tac >>
     qpat_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `abi_decoder_operand_live sh.cs_next_var op` by
       metis_tac[abi_decoder_operand_live_mono] >>
     qpat_assum `!op. abi_decoder_operand_live sh.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >> simp[] >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
         not_fresh_at_def,eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  `eval_operand head w = SOME (n2w (off+32)) /\
   op_prov Gw head = NONE /\ op_taint Tw head = {}` by simp[] >>
  `eval_operand hi w = SOME (n2w h) /\ op_prov Gw hi = NONE /\
   op_taint Tw hi = {}` by simp[] >>
  `eval_operand cnt w = SOME (n2w c) /\ op_prov Gw cnt = NONE /\
   op_taint Tw cnt = {}` by
    (qpat_assum `!x. not_fresh_at sl x ==> _` (qspec_then `out` mp_tac) >>
     qpat_assum `cnt = Var out` mp_tac >>
     qpat_assum `not_fresh_at sl out` mp_tac >>
     qpat_assum `eval_operand cnt v = SOME (n2w c)` mp_tac >>
     qpat_assum `op_prov Gv cnt = NONE` mp_tac >>
     qpat_assum `op_taint Tv cnt = {}` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[eval_operand_def,op_prov_def]) >>
  `abi_decoder_operand_live sc.cs_next_var head /\
   abi_decoder_operand_live sc.cs_next_var cnt /\
   abi_decoder_operand_live sc.cs_next_var hi` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decoder_operand_live sh.cs_next_var head`,
        `abi_decoder_operand_live sl.cs_next_var cnt`,
        `abi_decoder_operand_live start.cs_next_var hi`,
        `start.cs_next_var <= sh.cs_next_var`, `sh.cs_next_var <= sl.cs_next_var`,
        `sl.cs_next_var <= sc.cs_next_var`] >>
     rpt (pop_assum kall_tac) >>
     metis_tac[abi_decoder_operand_live_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  `off+32 < dimword (:256)` by decide_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;hi}
         (emitted_insts sc sg) B /\ {head;cnt;hi} SUBSET B` by
    (irule abi_decode_bytes_payload_scalar >> conj_tac >- simp[] >>
     qexistsl_tac [`head`,`hi`,`cnt`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
          ~is_ext_call_op i.inst_opcode) (emitted_insts sc sg)` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o CONJUNCT1)
       bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     simp[is_terminator_def,is_ext_call_op_def]) >>
  `!op. abi_decoder_operand_live sc.cs_next_var op ==>
        eval_operand op (drop_fresh sc w) = eval_operand op w` by
    (gen_tac >> disch_tac >> irule eval_operand_drop_fresh >>
     qpat_x_assum `abi_decoder_operand_live sc.cs_next_var op` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `op` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `eval_operand head (drop_fresh sc w) = SOME (n2w (off+32)) /\
   eval_operand cnt (drop_fresh sc w) = SOME (n2w c) /\
   eval_operand hi (drop_fresh sc w) = SOME (n2w h)` by simp[] >>
  `cs_extends start sc` by metis_tac[cs_extends_trans] >>
  `sg.cs_current_bb = sc.cs_current_bb` by fs[same_blocks_def] >>
  `!op. op IN {head;cnt;hi} ==> op_prov Gw op = NONE /\ op_taint Tw op = {}` by
    (simp[] >> metis_tac[]) >>
  `lo <= w.vs_alloca_next` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS sc w Gw Tw` (ACCEPT_TAC o cj 2 o BETA_RULE o
         PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]))) >>
  reverse (qsuff_tac `(?r. run_inst_seq (emitted_insts sc sg) w = Abort Revert_abort r) \/
    (?r. run_inst_seq (emitted_insts sc sg) w = OK r /\ off+32+c <= h)`)
  >- (assume_tac (Q.SPECL [`sc`,`w`] fresh_vars_wrt_drop_fresh) >>
      assume_tac (Q.SPECL [`sc`,`w`] vars_ext_drop_fresh) >>
      drule_all abi_decode_bytes_payload_guard_total >> strip_tac
      >- (disj1_tac >> drule_all run_inst_seq_vars_ext_abort >> metis_tac[]) >>
      disj2_tac >> drule_all_then (qx_choose_then `rw` strip_assume_tac)
        run_inst_seq_vars_ext_ok >>
      qexists_tac `rw` >> simp[] >>
      qpat_x_assum `w2n (n2w (off+32):bytes32) + w2n (n2w c:bytes32) <= _` mp_tac >>
      simp[w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `rr` assume_tac)
                             (qx_choose_then `rw` strip_assume_tac))
  >- (drule_all member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`,`PG`]
        (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac)))) >>
      qexistsl_tac [`Abort Revert_abort z`,`Gz`,`Tz`] >> conj_tac
      >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
          qexistsl_tac [`Gw`,`w`,`Tw`] >> simp[]) >>
      conj_tac
      >- (qx_gen_tac `obs` >> disch_tac >>
          qspecl_then [`start`,`sc`,`fin`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
          simp[cs_extends_trans] >> strip_tac >>
          qspecl_then [`sc`,`sg`,`fin`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
          simp[] >> strip_tac >>
          irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
          qexists_tac `w` >> simp[]) >>
      disj2_tac >> qexists_tac `z` >> simp[]) >>
  `sc.cs_next_var <= sg.cs_next_var /\ sc.cs_next_id <= sg.cs_next_id` by
    (qpat_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_def,
          compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sc sg)` by
    metis_tac[bodyFullAbiDecodeScalarNoAllocaTheory.abi_decode_scalar_seq_no_alloca] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp w` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_scalar_frame_joint)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `y` (qx_choose_then `Gy` (qx_choose_then `Ty` strip_assume_tac)))) >>
  `!obs. fn_has_code sc sg obs ==> gas_path ctx obs w 0 (OK y)` by
    (qpat_assum `y = _` SUBST1_TAC >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts sc sg`, `sc`] >>
     `sg.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sg` by
       metis_tac[inst_extends_def] >>
     drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >>
     simp[LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]) >>
  (* Compose the successful payload guard with the checked prefix. *)
  `cs_extends start sg` by metis_tac[cs_extends_trans] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK y,Gy,Ty)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gw`,`w`,`Tw`] >> simp[]) >>
  `!obs. fn_has_code start sg obs ==> gas_path ctx obs s 0 (OK y)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sc`,`sg`,`obs`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists_tac `w` >> conj_tac
     >- (qpat_assum `!obs. fn_has_code start sc obs ==> _`
           (qspec_then `obs` (drule_then ACCEPT_TAC))) >>
     qpat_assum `!obs. fn_has_code sc sg obs ==> _`
       (qspec_then `obs` (drule_then ACCEPT_TAC))) >>
  `start.cs_next_var <= sc.cs_next_var /\ sl.cs_next_var <= sg.cs_next_var` by decide_tac >>
  `not_fresh_at sg input /\ not_fresh_at sg dstv /\ not_fresh_at sg ar /\
   local_ptrs_reserved ce sg /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x)` by
    metis_tac[not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `abi_decoder_operand_live sg.cs_next_var cnt` by metis_tac[abi_decoder_operand_live_mono] >>
  `Ty.t_mem = Tv.t_mem /\ Ty.t_mem = tn.t_mem` by metis_tac[] >>
  `abi_decode_ptr_window Gy Ty y ar (input_word + n2w off) (LENGTH input_bytes - off)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[] >>
     `not_fresh_at sc ar` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `lookup_var dstv y = SOME (n2w d) /\
   FLOOKUP Gy dstv = SOME (output_base,output_cap) /\ op_taint Ty (Var dstv) = {}` by
    (qpat_assum `!op. abi_decoder_operand_live start.cs_next_var op ==> _`
       (qspec_then `Var dstv` mp_tac) >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x y = _ /\ _`
       (qspec_then `dstv` mp_tac) >>
     `not_fresh_at sc dstv` by metis_tac[not_fresh_at_mono] >>
     map_every (fn p => qpat_assum p mp_tac)
       [`not_fresh_at sc dstv`, `abi_decoder_operand_live start.cs_next_var (Var dstv)`,
        `eval_operand (Var dstv) s = _`, `FLOOKUP G dstv = _`, `op_taint tn (Var dstv) = _`] >>
     rpt (pop_assum kall_tac) >> simp[eval_operand_def,op_prov_def] >> metis_tac[]) >>
  `eval_operand cnt y = SOME (n2w c) /\ op_prov Gy cnt = NONE /\ op_taint Ty cnt = {}` by
    (`not_fresh_at sc out` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x y = _ /\ _`
       (qspec_then `out` mp_tac) >>
     map_every (fn p => qpat_assum p mp_tac)
       [`cnt = Var out`, `not_fresh_at sc out`,
        `eval_operand cnt w = SOME (n2w c)`, `op_prov Gw cnt = NONE`,
        `op_taint Tw cnt = {}`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[eval_operand_def,op_prov_def]) >>
  `w2n input_word + off < dimword (:256) /\
   32+c <= LENGTH input_bytes - off` by decide_tac >>
  `input_word + n2w off = (n2w (w2n input_word + off):bytes32)` by
    (CONV_TAC (RHS_CONV (REWR_CONV (GSYM wordsTheory.word_add_n2w))) >>
     simp[wordsTheory.n2w_w2n]) >>
  `abi_decode_ptr_window Gy Ty y ar (n2w (w2n input_word + off)) (32+c)` by
    (qpat_assum `abi_decode_ptr_window Gy Ty y ar (input_word + n2w off) _` mp_tac >>
     qpat_assum `input_word + n2w off = _` mp_tac >>
     qpat_assum `w2n input_word + off < dimword (:256)` mp_tac >>
     qpat_assum `32+c <= LENGTH input_bytes - off` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[abi_decode_ptr_window_def,w2n_n2w,arithmeticTheory.LESS_MOD] >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `LENGTH input_bytes - off` >> simp[]) >>
  qpat_assum `addr = Var ar` SUBST_ALL_TAC >>
  Cases_on `emit_op ADD [cnt;Lit 31w] sg` >>
  rename1 `emit_op ADD [cnt;Lit 31w] sg = (up,c1)` >>
  Cases_on `emit_op NOT [Lit 31w] c1` >>
  rename1 `emit_op NOT [Lit 31w] c1 = (mask,c2)` >>
  Cases_on `emit_op AND [up;mask] c2` >>
  rename1 `emit_op AND [up;mask] c2 = (rounded,c3)` >>
  Cases_on `emit_op ADD [Var dstv;rounded] c3` >>
  rename1 `emit_op ADD [Var dstv;rounded] c3 = (last,c4)` >>
  Cases_on `emit_void MSTORE [last;Lit 0w] c4` >>
  rename1 `emit_void MSTORE [last;Lit 0w] c4 = (unit,c5)` >>
  Cases_on `unit` >>
  Cases_on `emit_op ADD [Lit 32w;cnt] c5` >>
  rename1 `emit_op ADD [Lit 32w;cnt] c5 = (copysz,c6)` >>
  `emit_void MCOPY [Var dstv;Var ar;copysz] c6 = ((),fin)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_bytes_runtime_tail _ _ _ _ = _`,
        `emit_op ADD [cnt;Lit 31w] sg = _`, `emit_op NOT _ c1 = _`,
        `emit_op AND _ c2 = _`, `emit_op ADD _ c3 = _`,
        `emit_void MSTORE _ c4 = _`, `emit_op ADD _ c5 = _`] >>
     rpt (pop_assum kall_tac) >>
     ntac 6 disch_tac >>
     simp[abiDecoderBytesPhasesTheory.abi_decode_bytes_runtime_tail_def,
          comp_bind_def,comp_ignore_bind_def]) >>
  `c+31 < dimword (:256)` by decide_tac >>
  `eval_operand cnt (drop_fresh sg y) = SOME (n2w c)` by
    (`!z. cnt = Var z ==> not_fresh_at sg z` by
       (qpat_assum `abi_decoder_operand_live sg.cs_next_var cnt` mp_tac >>
        qpat_assum `cnt = Var out` mp_tac >>
        rpt (pop_assum kall_tac) >> disch_then SUBST1_TAC >>
        simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
     qpat_assum `eval_operand cnt y = SOME (n2w c)` (SUBST1_TAC o SYM) >>
     irule eval_operand_drop_fresh >> asm_rewrite_tac[]) >>
  assume_tac (Q.SPECL [`sg`,`y`] fresh_vars_wrt_drop_fresh) >>
  assume_tac (Q.SPECL [`sg`,`y`] vars_ext_drop_fresh) >>
  `bodyPtrBopScalarSeq$bop_scalar_seq {x | not_fresh_at sg x} {cnt; Lit 31w}
     (emitted_insts sg c3) (rounded INSERT mask INSERT up INSERT {cnt; Lit 31w})` by
    (irule abiDecodePtrBytesTailTheory.abi_decode_bytes_round_scalar >>
     simp[IgnAsm `cnt = Var out`] >>
     metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     ~is_ext_call_op i.inst_opcode) (emitted_insts sg c3)` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o CONJUNCT1)
       bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     simp[is_terminator_def,is_ext_call_op_def]) >>
  drule_all abiDecodePtrBytesTailTheory.abi_decode_bytes_round_sequence >>
  disch_then (qx_choose_then `rsmall` strip_assume_tac) >>
  drule_all_then (qx_choose_then `rround` strip_assume_tac) run_inst_seq_vars_ext_ok >>
  `eval_operand rounded rround = SOME (n2w (32*((c+31) DIV 32)))` by
    metis_tac[vars_ext_eval_operand] >>
  `sg.cs_next_var <= c3.cs_next_var /\ sg.cs_next_id <= c3.cs_next_id /\
   c3.cs_current_bb = sg.cs_current_bb /\ c3.cs_blocks = sg.cs_blocks /\
   isPREFIX sg.cs_current_insts c3.cs_current_insts` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`emit_op AND _ c2 = _`, `emit_op NOT _ c1 = _`, `emit_op ADD _ sg = _`] >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `inst_extends sg c3` by
    (map_every (fn pat => qpat_assum pat
       (mp_then Any mp_tac inst_extends_emit_op))
       [`emit_op AND _ c2 = _`, `emit_op NOT _ c1 = _`, `emit_op ADD _ sg = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> metis_tac[inst_extends_trans]) >>
  `cs_extends sg c3` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends c3 c4 /\ cs_extends c4 c5 /\ cs_extends c5 c6 /\ cs_extends c6 fin` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`emit_op ADD _ c3 = _`, `emit_void MSTORE _ c4 = _`,
        `emit_op ADD _ c5 = _`, `emit_void MCOPY _ c6 = _`] >>
     rpt (pop_assum kall_tac) >> ntac 4 disch_tac >>
     imp_res_tac loweringShapeRulesTheory.emit_op_facts >>
     fs[emit_void_def, GSYM emit_inst_def] >> imp_res_tac emit_inst_extends >>
     rpt conj_tac >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends c3 fin /\ cs_extends c4 fin /\ cs_extends c5 fin` by metis_tac[cs_extends_trans] >>
  map_every (fn args =>
    (qspecl_then args mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac))
    [[`sg`,`c3`,`fin`,`fn`], [`c3`,`c4`,`fin`,`fn`],
     [`c4`,`c5`,`fin`,`fn`], [`c5`,`c6`,`fin`,`fn`]] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sg c3)` by
    metis_tac[bodyFullAbiDecodeScalarNoAllocaTheory.abi_decode_scalar_seq_no_alloca] >>
  `!op. op IN {cnt;Lit 31w} ==> op_prov Gy op = NONE /\ op_taint Ty op = {}` by
    (qpat_assum `op_prov Gy cnt = NONE` mp_tac >>
     qpat_assum `op_taint Ty cnt = {}` mp_tac >>
     rpt (pop_assum kall_tac) >> ntac 2 disch_tac >>
     simp[] >> gen_tac >> strip_tac >> asm_rewrite_tac[] >>
     simp[op_prov_def,op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp y` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all ((PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_scalar_frame_joint) |>
      Q.INST [`sa` |-> `sg`, `sb` |-> `c3`, `s` |-> `y`, `t` |-> `rround`])) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z3` (qx_choose_then `G3` (qx_choose_then `T3` strip_assume_tac)))) >>
  `!obs. fn_has_code sg c3 obs ==> gas_path ctx obs y 0 (OK z3)` by
    (qpat_assum `z3 = _` SUBST1_TAC >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts sg c3`,`sg`] >>
     `c3.cs_current_insts = sg.cs_current_insts ++ emitted_insts sg c3` by
       fs[inst_extends_def] >>
     qpat_assum `bop_scalar_seq _ _ (emitted_insts sg c3) _`
       (mp_then Any mp_tac bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes) >>
     simp[LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]) >>
  `eval_operand rounded z3 = SOME (n2w (32*((c+31) DIV 32)))` by
    (qpat_assum `z3 = _` SUBST1_TAC >>
     simp[ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  `op_prov G3 rounded = NONE /\ op_taint T3 rounded = {}` by
    (qpat_assum `!op. op IN _ ==> op_prov G3 op = _ /\ _`
       (qspec_then `rounded` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live c3.cs_next_var rounded` by
    (qpat_assum `emit_op AND _ c2 = _`
      (mp_then Any ACCEPT_TAC abiDecoderReentryTheory.abi_decoder_operand_live_emit)) >>
  `lookup_var dstv z3 = SOME (n2w d) /\
   FLOOKUP G3 dstv = SOME (output_base,output_cap) /\ op_taint T3 (Var dstv) = {}` by
    (qpat_assum `!x. not_fresh_at sg x ==> lookup_var x z3 = _ /\ _`
       (qspec_then `dstv` mp_tac) >> simp[]) >>
  `local_ptrs_reserved ce c3 /\ not_fresh_at c3 input /\ not_fresh_at c3 dstv /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c3 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c3 x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`sg.cs_next_var <= c3.cs_next_var`, `local_ptrs_reserved ce sg`,
        `not_fresh_at sg input`, `not_fresh_at sg dstv`,
        `!x sz. ce.ce_return_buf = _ ==> not_fresh_at sg x`,
        `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sg x`] >>
     rpt (pop_assum kall_tac) >> metis_tac[local_ptrs_reserved_next_var,not_fresh_at_mono]) >>
  `32*((c+31) DIV 32) <= 32*((n+31) DIV 32)` by
    (`(c+31) DIV 32 <= (n+31) DIV 32` by (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
     decide_tac) >>
  `d+32*((c+31) DIV 32)+32 <= output_base+output_cap` by decide_tac >>
  `d < dimword (:256) /\ d+type_memory_size tv < dimword (:256) /\
   32*((c+31) DIV 32)+32 <= type_memory_size tv` by decide_tac >>
  `ptr_covers G3 T3 dstv z3 (type_memory_size tv)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var dstv z3 = _`, `FLOOKUP G3 dstv = _`, `op_taint T3 (Var dstv) = _`,
        `output_base <= d`, `d+type_memory_size tv <= output_base+output_cap`,
        `d < dimword (:256)`] >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def,w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  `?padvar. last = Var padvar` by
    (qpat_assum `emit_op ADD _ c3 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `emit_op ADD [Var dstv;rounded] c3 = (Var padvar,c4)` by
    (qpat_assum `last = Var padvar` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `w2n (n2w d : 256 word) + type_memory_size tv < dimword (:256)` by
    simp[w2n_n2w,arithmeticTheory.LESS_MOD] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all ((PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      bodyFullAbiDecodeArrayBulkWindowTheory.abi_decode_bulk_window_add_joint) |>
      Q.INST [`sa` |-> `c3`, `sb` |-> `c4`, `s` |-> `z3`, `k` |-> `32`,
              `cap` |-> `type_memory_size tv`])) >>
  disch_then (qspecl_then [`explicit`,`PG`] (mp_tac o REWRITE_RULE [LET_THM])) >>
  BETA_TAC >>
  qabbrev_tac `z4 = (update_var padvar (n2w d + n2w (32*((c+31) DIV 32))) z3)
                    with vs_inst_idx := LENGTH c4.cs_current_insts` >>
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ _ [] (_,G4,T4)` >>
  strip_tac >>
  `z4 = (update_var padvar (n2w (d + 32*((c+31) DIV 32))) z3)
        with vs_inst_idx := SUC z3.vs_inst_idx` by
    (qpat_assum `emit_op ADD [Var dstv;rounded] c3 = (Var padvar,c4)`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[Abbr `z4`,word_add_n2w,arithmeticTheory.ADD1]) >>
  `!obs. fn_has_code c3 c4 obs ==> gas_path ctx obs z3 0 (OK z4)` by
    (qpat_assum `z4 = _` SUBST1_TAC >> qx_gen_tac `obs` >> disch_tac >>
     qpat_assum `emit_op ADD _ c3 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `padvar = STRING #"%" (toString c3.cs_next_var)` by metis_tac[operand_11] >>
     qpat_assum `padvar = STRING _ _` SUBST1_TAC >>
     `eval_operand (Var dstv) z3 = SOME (n2w d)` by simp[eval_operand_def] >>
     qpat_assum `emit_op ADD _ c3 = _`
       (mp_then Any irule emitHelperPropsTheory.emit_op_zero_path) >>
     simp[IgnAsm `z3 = _`,step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
          word_add_n2w,is_terminator_def]) >>
  `output_base+output_cap <= z4.vs_alloca_next` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS c4 z4 G4 T4` (map_every assume_tac o CONJUNCTS o
         BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     `alloca_inv z4` by
       (qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
          qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es z4 /\ _`
            (assume_tac o CONJUNCT1 o (fn th => MATCH_MP th vh)))) >>
        qpat_assum `stmt_state_rel _ ctx fn ce cx es z4`
          (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca)) >>
     irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `output_id` >> first_assum ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z3,G3,T3)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gy`,`y`,`Ty`] >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z4,G4,T4)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`G3`,`z3`,`T3`] >> simp[]) >>
  `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z4.vs_allocas aid = SOME b` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK z4,G4,T4)`
       (qspec_then `DF (@H. V H)` (mp_tac o CONJUNCT2 o
         MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
     disch_then (mp_tac o MATCH_MP forPtrAllocationFrameTheory.gas_path_ptr_old_allocations) >>
     simp[]) >>
  `start.cs_next_var <= sg.cs_next_var /\ start.cs_next_var <= c3.cs_next_var` by decide_tac >>
  `!x. not_fresh_at start x ==> lookup_var x z4 = lookup_var x s /\
     FLOOKUP G4 x = FLOOKUP G x /\ op_taint T4 (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sc x /\ not_fresh_at sg x /\ not_fresh_at c3 x` by
       metis_tac[not_fresh_at_mono] >>
     `abi_decoder_operand_live start.cs_next_var (Var x)` by
       fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def] >>
     `lookup_var x w = lookup_var x s /\ FLOOKUP Gw x = FLOOKUP G x /\
      op_taint Tw (Var x) = op_taint tn (Var x)` by
       (qpat_assum `!op. abi_decoder_operand_live start.cs_next_var op ==>
                        eval_operand op w = eval_operand op s /\ _`
          (qspec_then `Var x` (mp_tac o SIMP_RULE (srw_ss()) [eval_operand_def,op_prov_def])) >>
        asm_rewrite_tac[]) >>
     map_every (fn pat => qpat_assum pat (qspec_then `x` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at sc x ==> lookup_var x y = _ /\ _`,
        `!x. not_fresh_at sg x ==> lookup_var x z3 = _ /\ _`,
        `!x. not_fresh_at c3 x ==> lookup_var x z4 = _ /\ _`] >>
     asm_rewrite_tac[]) >>
  `IO z4` by
    (qpat_assum `Abbrev (IO = _)` (fn th =>
       qpat_assum `IO s` (mp_tac o BETA_RULE o PURE_REWRITE_RULE
         [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th] >> BETA_TAC) >>
     disch_tac >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`start`] >> rpt conj_tac >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qabbrev_tac `pad = d + 32*((c+31) DIV 32)` >>
  `pad + 32 <= d + type_memory_size tv /\ pad < dimword (:256)` by
    (simp[Abbr `pad`] >> decide_tac) >>
  `w2n (n2w pad : 256 word) = pad` by simp[w2n_n2w] >>
  `lookup_var padvar z4 = SOME (n2w pad) /\
   op_taint T4 (Lit 0w) = {} /\ eval_operand (Lit 0w) z4 = SOME 0w` by
    (conj_tac >-
       (qpat_assum `lookup_var padvar z4 = _` mp_tac >>
        simp[NoAsms,Abbr `pad`,word_add_n2w]) >>
     simp[NoAsms,op_taint_def,eval_operand_def]) >>
  `c3.cs_next_var <= c4.cs_next_var` by
    (qpat_assum `emit_op ADD _ c3 = _`
       (mp_then Any strip_assume_tac loweringShapeRulesTheory.emit_op_facts) >> decide_tac) >>
  `local_ptrs_reserved ce c4 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x)` by
    metis_tac[local_ptrs_reserved_next_var,not_fresh_at_mono] >>
  Q.SUBGOAL_THEN
    `output_base <= w2n (n2w pad : 256 word) /\
     w2n (n2w pad : 256 word) + 32 <= output_base+output_cap /\
     w2n (n2w pad : 256 word) + 32 <= z4.vs_alloca_next /\
     (w2n input_word + LENGTH input_bytes <= w2n (n2w pad : 256 word) \/
      w2n (n2w pad : 256 word) + 32 <= w2n input_word)`
    (map_every assume_tac o CONJUNCTS) >-
    (simp[IgnAsm `z4 = _`,IgnAsm `z3 = _`,Abbr `pad`] >> decide_tac) >>
  `EVERY (\(aid,p,b,k,bytes). b+k <= w2n (n2w pad : 256 word) \/
     w2n (n2w pad : 256 word)+32 <= b) live /\
   EVERY (\(b,bytes). b+LENGTH bytes <= w2n (n2w pad : 256 word) \/
     w2n (n2w pad : 256 word)+32 <= b) protected` by
    (asm_rewrite_tac[] >> conj_tac >-
       (simp[NoAsms,EVERY_MEM,FORALL_PROD] >> rpt gen_tac >> disch_tac >>
        qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ _) live`
          (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM,FORALL_PROD]) >>
        disch_then drule >> simp[Abbr `pad`] >> decide_tac) >>
     simp[NoAsms,EVERY_MEM,FORALL_PROD] >> rpt gen_tac >> disch_tac >>
     qpat_assum `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ _) protected`
       (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM,FORALL_PROD]) >>
     disch_then drule >> simp[Abbr `pad`] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z4` by simp[] >>
  `emit_void MSTORE [Var padvar; Lit 0w] c4 = ((),c5)` by metis_tac[] >>
  qpat_assum `Abbrev (OS = _)` (fn os =>
    qpat_assum `Abbrev (IO = _)` (fn io =>
      drule_all (PURE_REWRITE_RULE
        (map (GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) [os,io])
        bodyFullAbiDecodeOwnedWordStoreObservedTheory.abi_decode_owned_word_store_observed_exact |>
        Q.INST [`sa` |-> `c4`, `sb` |-> `c5`, `s` |-> `z4`,
                `dw` |-> `n2w pad`, `value` |-> `Lit 0w`]))) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z5` (qx_choose_then `G5` (qx_choose_then `T5` strip_assume_tac)))) >>
  `c5.cs_next_var = c4.cs_next_var` by
    (qpat_assum `emit_void MSTORE [Var padvar;Lit 0w] c4 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sg out` by
    (qpat_assum `abi_decoder_operand_live sg.cs_next_var cnt` mp_tac >>
     qpat_assum `cnt = Var out` mp_tac >> rpt (pop_assum kall_tac) >>
     disch_then SUBST1_TAC >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `not_fresh_at c3 out /\ not_fresh_at c4 out` by
    metis_tac[not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `eval_operand cnt z5 = SOME (n2w c) /\ op_prov G5 cnt = NONE /\ op_taint T5 cnt = {}` by
    (map_every (fn pat => qpat_assum pat (qspec_then `out` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at sg x ==> lookup_var x z3 = _ /\ _`,
        `!x. not_fresh_at c3 x ==> lookup_var x z4 = _ /\ _`,
        `!x. not_fresh_at c4 x ==> lookup_var x z5 = _ /\ _`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`cnt = Var out`, `eval_operand cnt y = _`, `op_prov Gy cnt = _`, `op_taint Ty cnt = _`,
        `lookup_var out z3 = _`, `FLOOKUP G3 out = _`, `op_taint T3 (Var out) = _`,
        `lookup_var out z4 = _`, `FLOOKUP G4 out = _`, `op_taint T4 (Var out) = _`,
        `lookup_var out z5 = _`, `FLOOKUP G5 out = _`, `op_taint T5 (Var out) = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[eval_operand_def,op_prov_def]) >>
  `abi_decoder_operand_live c5.cs_next_var cnt` by
    metis_tac[abi_decoder_operand_live_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `?raw6. run_inst_seq (emitted_insts c5 c6) z5 = OK raw6 /\
          eval_operand copysz raw6 = SOME (n2w (32+c))` by
    (qpat_assum `emit_op ADD [Lit 32w;cnt] c5 = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >>
     qpat_assum `eval_operand cnt z5 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, lookup_var_update_var, word_add_n2w]) >>
  `bop_scalar_seq {x | not_fresh_at c5 x} {Lit 32w;cnt}
       (emitted_insts c5 c6) (copysz INSERT {Lit 32w;cnt})` by
    (irule bodyPtrBopScalarCompileTheory.bop_scalar_seq_emit_op >> conj_tac >- simp[] >>
     qexistsl_tac [`ADD`,`[Lit 32w;cnt]`] >> simp[IgnAsm `cnt = Var out`]) >>
  `!op. op IN {Lit 32w;cnt} ==> op_prov G5 op = NONE /\ op_taint T5 op = {}` by
    (qpat_assum `op_prov G5 cnt = NONE` mp_tac >>
     qpat_assum `op_taint T5 cnt = {}` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[] >> rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  `inst_extends c5 c6 /\ c6.cs_current_bb = c5.cs_current_bb /\
   c5.cs_next_var <= c6.cs_next_var /\ c5.cs_next_id <= c6.cs_next_id /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts c5 c6)` by
    (qpat_assum `emit_op ADD [Lit 32w;cnt] c5 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule_then strip_assume_tac loweringShapeRulesTheory.emit_op_facts >>
     drule_then strip_assume_tac emitted_insts_emit_op >>
     simp[mk_inst_def] >> metis_tac[inst_extends_emit_op]) >>
  `local_ptrs_reserved ce c5 /\ not_fresh_at c5 input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x)` by
    (`c3.cs_next_var <= c5.cs_next_var` by decide_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`c3.cs_next_var <= c5.cs_next_var`, `local_ptrs_reserved ce c3`,
        `not_fresh_at c3 input`, `!x sz. ce.ce_return_buf = _ ==> not_fresh_at c3 x`,
        `!x sz. ce.ce_return_pc = _ ==> not_fresh_at c3 x`] >>
     rpt (pop_assum kall_tac) >> metis_tac[local_ptrs_reserved_next_var,not_fresh_at_mono]) >>
  `allocas_from lo z5` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS c5 z5 G5 T5` (map_every assume_tac o CONJUNCTS o
         BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
       qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es z5 /\ _`
          (mp_tac o CONJUNCT1 o CONJUNCT2 o (fn th => MATCH_MP th vh)))) >>
     simp[ghost_inv_at_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z5` by simp[] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all ((PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_scalar_frame_joint) |>
      Q.INST [`sa` |-> `c5`, `sb` |-> `c6`, `s` |-> `z5`, `t` |-> `rsize`])) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z6` (qx_choose_then `G6` (qx_choose_then `T6` strip_assume_tac)))) >>
  `!obs. fn_has_code c5 c6 obs ==> gas_path ctx obs z5 0 (OK z6)` by
    (qpat_assum `z6 = _` SUBST1_TAC >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts c5 c6`,`c5`] >>
     `c6.cs_current_insts = c5.cs_current_insts ++ emitted_insts c5 c6` by
       fs[inst_extends_def] >>
     qpat_assum `bop_scalar_seq _ _ (emitted_insts c5 c6) _`
       (mp_then Any mp_tac bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes) >>
     simp[LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]) >>
  `eval_operand copysz z6 = SOME (n2w (32+c))` by
    (qpat_assum `z6 = _` SUBST1_TAC >>
     simp[ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  `op_taint T6 copysz = {}` by
    (qpat_assum `!op. op IN _ ==> op_prov G6 op = _ /\ _`
       (qspec_then `copysz` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live c6.cs_next_var copysz` by
    (qpat_assum `emit_op ADD _ c5 = _`
      (mp_then Any ACCEPT_TAC abiDecoderReentryTheory.abi_decoder_operand_live_emit)) >>
  `c3.cs_next_var <= c5.cs_next_var /\ sg.cs_next_var <= c6.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sg x ==> lookup_var x z6 = lookup_var x y /\
     FLOOKUP G6 x = FLOOKUP Gy x /\ op_taint T6 (Var x) = op_taint Ty (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at c3 x /\ not_fresh_at c4 x /\ not_fresh_at c5 x` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`not_fresh_at sg x`, `sg.cs_next_var <= c3.cs_next_var`,
           `c3.cs_next_var <= c4.cs_next_var`, `c3.cs_next_var <= c5.cs_next_var`] >>
        rpt (pop_assum kall_tac) >>
        metis_tac[not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
     map_every (fn pat => qpat_assum pat (qspec_then `x` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at sg x ==> lookup_var x z3 = _ /\ _`,
        `!x. not_fresh_at c3 x ==> lookup_var x z4 = _ /\ _`,
        `!x. not_fresh_at c4 x ==> lookup_var x z5 = _ /\ _`,
        `!x. not_fresh_at c5 x ==> lookup_var x z6 = _ /\ _`] >>
     asm_rewrite_tac[]) >>
  `local_ptrs_reserved ce c6 /\ not_fresh_at c6 input /\
   not_fresh_at c6 dstv /\ not_fresh_at c6 ar /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`sg.cs_next_var <= c6.cs_next_var`, `local_ptrs_reserved ce sg`,
        `not_fresh_at sg input`, `not_fresh_at sg dstv`, `not_fresh_at sg ar`,
        `!x sz. ce.ce_return_buf = _ ==> not_fresh_at sg x`,
        `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sg x`] >>
     rpt (pop_assum kall_tac) >> metis_tac[local_ptrs_reserved_next_var,not_fresh_at_mono]) >>
  `lookup_var dstv z6 = SOME (n2w d) /\
   FLOOKUP G6 dstv = SOME (output_base,output_cap) /\ op_taint T6 (Var dstv) = {}` by
    (qpat_assum `!x. not_fresh_at sg x ==> lookup_var x z6 = _ /\ _`
       (qspec_then `dstv` mp_tac) >> simp[]) >>
  `lookup_var ar z6 = SOME (n2w (w2n input_word + off)) /\ ptr_covers G6 T6 ar z6 (32+c)` by
    (qpat_assum `!x. not_fresh_at sg x ==> lookup_var x z6 = _ /\ _`
       (qspec_then `ar` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var ar z6 = _`, `FLOOKUP G6 ar = _`, `op_taint T6 (Var ar) = _`,
        `abi_decode_ptr_window Gy Ty y ar (n2w (w2n input_word + off)) (32+c)`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_ptr_window_def,ptr_covers_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `abi_decode_ptr_window G6 T6 z6 input input_word (LENGTH input_bytes) /\
   w2n input_word + LENGTH input_bytes <= z6.vs_alloca_next /\
   output_base+output_cap <= z6.vs_alloca_next` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS c6 z6 G6 T6` (map_every assume_tac o CONJUNCTS o
         BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     `alloca_inv z6` by
       (qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
          qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es z6 /\ _`
            (assume_tac o CONJUNCT1 o (fn th => MATCH_MP th vh)))) >>
        qpat_assum `stmt_state_rel _ ctx fn ce cx es z6`
          (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `output_id` >> first_assum ACCEPT_TAC) >>
  `c <= 32*((n+31) DIV 32)` by
    (qpat_assum `c <= n` mp_tac >> rpt (pop_assum kall_tac) >>
     mp_tac (arithmeticTheory.DIVISION |> Q.SPEC `32`) >>
     rewrite_tac [DECIDE ``0 < 32``] >>
     disch_then (qspec_then `n+31` strip_assume_tac) >> strip_tac >> decide_tac) >>
  `d < dimword (:256) /\ 32+c < dimword (:256) /\
   d+(32+c) <= output_base+output_cap /\ d+(32+c) <= z6.vs_alloca_next /\
   (w2n input_word + off)+(32+c) <= z6.vs_alloca_next` by decide_tac >>
  `ptr_covers G6 T6 dstv z6 (32+c)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var dstv z6 = _`, `FLOOKUP G6 dstv = _`, `op_taint T6 (Var dstv) = _`,
        `output_base <= d`, `d+(32+c) <= output_base+output_cap`, `d < dimword (:256)`] >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def,w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  `!i. w2n input_word+off <= i /\ i < (w2n input_word+off)+(32+c) ==> i NOTIN T6.t_mem` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_ptr_window G6 T6 z6 input _ _`, `off+32+c <= h`, `h <= LENGTH input_bytes`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_ptr_window_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  Q.SUBGOAL_THEN
    `(w2n input_word+LENGTH input_bytes <= d \/ d+(32+c) <= w2n input_word) /\
     EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+(32+c) <= b) live /\
     EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+(32+c) <= b) protected`
    (map_every assume_tac o CONJUNCTS) >-
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`w2n input_word+LENGTH input_bytes <= d \/ _`,
        `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ _) live`,
        `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+type_memory_size tv <= b) protected`,
        `type_memory_size tv = _`, `c <= 32*((n+31) DIV 32)`] >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM,FORALL_PROD] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all ((PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      bodyFullAbiDecodeOwnedCopyEffectTheory.abi_decode_owned_mcopy_joint_effect) |>
      Q.INST [`sa` |-> `c6`, `sb` |-> `fin`, `s` |-> `z6`, `src` |-> `ar`, `dst` |-> `dstv`,
              `a` |-> `w2n input_word+off`, `b` |-> `d`, `n` |-> `32+c`])) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `zf` (qx_choose_then `Gf` (qx_choose_then `Tf` strip_assume_tac)))) >>
  (* The final MCOPY supplies the common endpoint and ghost witnesses. *)
  `!obs. fn_has_code c6 fin obs ==> gas_path ctx obs z6 0 (OK zf)` by
    (qpat_assum `zf = _` SUBST1_TAC >> rpt strip_tac >>
     `SUC z6.vs_inst_idx = LENGTH fin.cs_current_insts` by
       (qpat_assum `emit_void MCOPY _ c6 = _`
          (mp_then Any strip_assume_tac emitted_insts_emit_void) >> simp[]) >>
     qpat_assum `SUC z6.vs_inst_idx = LENGTH fin.cs_current_insts` SUBST1_TAC >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts c6 fin`,`c6`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`emit_void MCOPY _ c6 = _`, `fn_has_code c6 fin obs`,
        `lookup_var dstv z6 = _`, `lookup_var ar z6 = _`, `eval_operand copysz z6 = _`,
        `d < dimword (:256)`, `w2n input_word+off < dimword (:256)`,
        `32+c < dimword (:256)`, `~z6.vs_halted`,
        `z6.vs_current_bb = c6.cs_current_bb`, `z6.vs_inst_idx = LENGTH c6.cs_current_insts`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `eval_operand (Var dstv) z6 = SOME (n2w d) /\
      eval_operand (Var ar) z6 = SOME (n2w (w2n input_word+off))` by simp[eval_operand_def] >>
     drule_all_then strip_assume_tac abiEncoderWindowLeavesTheory.window_emit_copy_run >>
     drule_then strip_assume_tac emitted_insts_emit_void >>
     simp[mk_inst_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK zf,Gf,Tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`G4`,`z4`,`T4`] >>
     (conj_tac >- simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`G5`,`z5`,`T5`] >>
     (conj_tac >- simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`G6`,`z6`,`T6`] >> simp[]) >>
  `!obs. fn_has_code start fin obs ==> gas_path ctx obs s 0 (OK zf)` by
    (qx_gen_tac `obs` >> disch_tac >>
     map_every (fn args =>
       qspecl_then args mp_tac fragExecTheory.fn_has_code_split >>
       (impl_tac >- asm_rewrite_tac[]) >> strip_tac)
       [[`start`,`sg`,`fin`,`obs`], [`sg`,`c3`,`fin`,`obs`],
        [`c3`,`c4`,`fin`,`obs`], [`c4`,`c5`,`fin`,`obs`], [`c5`,`c6`,`fin`,`obs`]] >>
     map_every (fn pat => qpat_assum pat (qspec_then `obs` (drule_then assume_tac)))
       [`!obs. fn_has_code start sg obs ==> _`, `!obs. fn_has_code sg c3 obs ==> _`,
        `!obs. fn_has_code c3 c4 obs ==> _`, `!obs. fn_has_code c4 c5 obs ==> _`,
        `!obs. fn_has_code c5 c6 obs ==> _`, `!obs. fn_has_code c6 fin obs ==> _`] >>
     map_every (fn mid =>
       irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
       qexists_tac mid >> (conj_tac >- first_assum ACCEPT_TAC))
       [`y`,`z3`,`z4`,`z5`,`z6`] >> first_assum ACCEPT_TAC) >>
  `start.cs_next_var <= c4.cs_next_var /\
   start.cs_next_var <= c5.cs_next_var /\ start.cs_next_var <= c6.cs_next_var` by decide_tac >>
  `!x. not_fresh_at start x ==> lookup_var x zf = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint Tf (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at c4 x /\ not_fresh_at c5 x /\ not_fresh_at c6 x` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`not_fresh_at start x`, `start.cs_next_var <= c4.cs_next_var`,
           `start.cs_next_var <= c5.cs_next_var`, `start.cs_next_var <= c6.cs_next_var`] >>
        rpt (pop_assum kall_tac) >> metis_tac[not_fresh_at_mono]) >>
     map_every (fn pat => qpat_assum pat (qspec_then `x` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at start x ==> lookup_var x z4 = _ /\ _`,
        `!x. not_fresh_at c4 x ==> lookup_var x z5 = _ /\ _`,
        `!x. not_fresh_at c5 x ==> lookup_var x z6 = _ /\ _`,
        `!x. not_fresh_at c6 x ==> lookup_var x zf = _ /\ _`] >>
     asm_rewrite_tac[]) >>
  `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP zf.vs_allocas aid = SOME b` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK zf,Gf,Tf)`
       (qspec_then `DF (@H. V H)` (mp_tac o CONJUNCT2 o
         MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
     disch_then (mp_tac o MATCH_MP forPtrAllocationFrameTheory.gas_path_ptr_old_allocations) >>
     simp[]) >>
  `IO zf` by
    (qpat_assum `Abbrev (IO = _)` (fn th =>
       qpat_assum `IO s` (mp_tac o BETA_RULE o PURE_REWRITE_RULE
         [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th] >> BETA_TAC) >>
     disch_tac >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`start`] >> rpt conj_tac >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `Tf.t_mem SUBSET tn.t_mem /\
   (!i. d <= i /\ i < d+(32+c) ==> i NOTIN Tf.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Tf.t_mem = _`, `T6.t_mem = _`, `T5.t_mem SUBSET T4.t_mem`,
        `T4.t_mem = _`, `T3.t_mem = _`, `Ty.t_mem = tn.t_mem`] >>
     rpt (pop_assum kall_tac) >> simp[SUBSET_DEF,IN_DIFF] >> metis_tac[]) >>
  `mem_bytes_at (w2n input_word) (LENGTH input_bytes) z6.vs_memory =
   mem_bytes_at (w2n input_word) (LENGTH input_bytes) u.vs_memory` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       map_every (fn pat => qpat_assum pat (assume_tac o cj 5 o
          BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]))
         [`OS c6 z6 G6 T6`, `OS sh u Gu Tu`]) >>
     asm_rewrite_tac[]) >>
  `mem_word_at (w2n input_word+off) z6.vs_memory =
   mem_word_at (w2n input_word+off) u.vs_memory` by
    (irule (cj 1 (Q.INST [`c` |-> `0`] abiDecoderBytestringSourceTheory.abi_decode_bytestring_copy_views)) >>
     rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
     `off+32 <= LENGTH input_bytes` by decide_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`off+32 <= LENGTH input_bytes`,
        `mem_bytes_at (w2n input_word) _ z6.vs_memory = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     map_every (fn mem =>
       qspecl_then [`w2n input_word`,`off`,`32`,`LENGTH input_bytes`,mem]
          (drule_then assume_tac) abiCanonicalHeadSizeTheory.mem_bytes_at_window)
       [`u.vs_memory`,`z6.vs_memory`] >> metis_tac[]) >>
  `mem_word_at d zf.vs_memory = n2w c` by
    (qpat_assum `mem_word_at (w2n input_word+off) z6.vs_memory = _`
       (assume_tac o REWRITE_RULE [mem_word_at_eq_mload]) >>
     qpat_assum `zf = _` SUBST1_TAC >>
     simp[mem_word_at_eq_mload,abiEncoderPathPropsTheory.mload_inst_idx,
          stmtReasonMemoryTheory.mload_mcopy_same,GSYM (Abbr `wc`)]) >>
  `!v. value_has_type tv v /\ val_in_memory tv v d zf.vs_memory ==>
       val_footprint tv v = 32+c` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decoder_coherent ce env sf ty tv`, `DecBytestring n = _`,
        `n < dimword (:256)`, `c < dimword (:256)`,
        `mem_word_at d zf.vs_memory = n2w c`] >>
     rpt (pop_assum kall_tac) >> ntac 5 disch_tac >>
     `tv = BaseTV (BytesT (Dynamic n)) \/ tv = BaseTV (StringT n)` by
       metis_tac[abi_decoder_bytestring_cases] >>
     qx_gen_tac `vv` >> Cases_on `vv` >>
     gvs[vyperTypingTheory.value_has_type_def,valueEncodingDefsTheory.val_in_memory_def,
         loweringPostsTheory.val_footprint_def] >>
     strip_tac >> rename1 `LENGTH payload <= n` >>
     `LENGTH payload < dimword (:256)` by decide_tac >>
     gvs[arithmeticTheory.LESS_MOD]) >>
  `!v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d zf.vs_memory ==>
       !mem. mem_agree_outside Tf.t_mem zf.vs_memory mem ==> val_in_memory tv v d mem` by
    (qx_gen_tac `vv` >> strip_tac >>
     `val_footprint tv vv = 32+c` by (first_x_assum irule >> simp[]) >>
     gen_tac >> disch_tac >> irule val_in_memory_clean_footprint_ptr >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Tf.t_mem`,`zf.vs_memory`] >>
     conj_tac >-
       (qpat_assum `val_footprint tv vv = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN Tf.t_mem ==>
       i IN tn.t_mem` by
    (qpat_assum `Tf.t_mem SUBSET tn.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qexistsl_tac [`OK zf`,`Gf`,`Tf`] >>
  conj_tac >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `zf` >> asm_rewrite_tac[]
QED
