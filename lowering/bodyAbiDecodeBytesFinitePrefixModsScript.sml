Theory bodyAbiDecodeBytesFinitePrefixMods
Ancestors
  bodyFullAbiDecodeFiniteCasesObserved bodyFullAbiDecodeGuardReadObserved
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeOwnedStateProps
  abiDecodePtrBytesMember abiDecodePtrMemberFrame abiDecoderBytestringCases
  abiDecoderBytesRuntime abiDecoderBytesBound abiDecoderGuard abiDecoderCoherence
  decoderGhostFramePtr forPtrAllocationFrame gasOriginPtrLabels
  fragExec fragGasOriginPtr fragGasOriginPtrLoop fragGasPath
  valueEncodingProps emitHelper emitHelperProps loweringShapeRules entryDecodeStructure
  exprLowering builtinAbi abiEncoder exprLoweringProps
  stateRelProj stateFrame bodyPtrDefs compileEnv loweringStateRelDefs freshWrites
  abiDecoderReentry venomState ptrDiscipline
  words arithmetic relation pair finite_map list rich_list pred_set

(* Keep the phase inputs independent of the proofs that produce them. *)
local
  fun normalize tm = rhs (concl (DEPTH_CONV BETA_CONV tm))
  fun close tm = list_mk_forall (free_vars_lr (normalize tm), tm)
  fun append_field f tm =
    if is_conj tm then let val (l,r) = dest_conj tm
      in mk_conj (l, append_field f r) end
    else mk_conj (tm,f)
  fun extend_exists f tm = let val (vs,body) = strip_exists tm
    in list_mk_exists (vs,append_field f body) end
  val cut = ``\a b. cs_extends a b /\
    LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
    a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id``
  val finite = ``\a b q q'. !D.
    RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
      (LENGTH b.cs_current_insts - LENGTH a.cs_current_insts) q q'``
  val path = ``\s G tn r Gf tf. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,Gf,tf)``
  val obs = ``\a b s r. !obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r``
  val frame = ``\a s (G:string |-> num # num) tn t Gf tf. !x. not_fresh_at a x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)``
  val cursor = ``\a s. ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts``
  val reserve = ``\a. (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
                      not_fresh_at a x) /\
                     (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
                      not_fresh_at a x)``
  val (original_vs, prefix_body) = strip_forall
    (concl abi_decode_bytes_case_observed_conditional)
  val fin = ``fin:compile_state``
  val finish = List.find (fn v => fst (dest_var v) = "finish") original_vs |> valOf
  val prefix_vs = map (subst [finish |-> fin]) original_vs
  val pre = subst [finish |-> fin] (fst (dest_imp prefix_body))
  val os = ``\st s G tn.
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
    EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``
  val io = ``\s.
    ((?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
       ib <= w2n (input_word:256 word) /\
       w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
     (?name ib isz. local_region ce es.scopes s name ib isz /\
       ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``
  fun abort a b = ``?z Gz Tz. (^path) ^(``s:venom_state``) G tn
      (Abort Revert_abort z) Gz Tz /\ (^obs) ^a ^b s (Abort Revert_abort z)``
  fun guard th =
    let val (p,q) = dest_imp (concl th)
        val (normal,reject) = dest_disj q
        val fields = ``cs_extends sa sb /\ LENGTH sa.cs_current_insts <= LENGTH sb.cs_current_insts /\
          sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
          (^finite) sa sb (s,G,tn) (t,Gf,tnf)``
    in close (mk_imp (p,mk_disj (extend_exists fields normal,reject))) end
  val (load_pre,load_post) = dest_imp (concl abi_decode_bytes_owned_load_frame_joint_observed)
  val load = close (mk_imp (load_pre,extend_exists
    ``(^finite) sa sc (s,G,tn) (t,Gf,tnf)`` load_post))
  val payload = close ``
    abi_decode_bytes_payload_guard head cnt hi sc = ((),sg) /\
    hi <> Lit 0w /\ fn_has_code sc sg fn /\
    ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (^os) sc s G tn /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    not_fresh_at sc input /\ local_ptrs_reserved ce sc /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    abi_decoder_operand_live sc.cs_next_var head /\
    abi_decoder_operand_live sc.cs_next_var cnt /\
    abi_decoder_operand_live sc.cs_next_var hi /\
    eval_operand head s = SOME (n2w (off+32)) /\
    eval_operand cnt s = SOME (n2w c) /\ eval_operand hi s = SOME (n2w h) /\
    off+32 < dimword (:256) /\ c < dimword (:256) /\ h < dimword (:256) /\
    op_prov G head = NONE /\ op_taint tn head = {} /\
    op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
    op_prov G hi = NONE /\ op_taint tn hi = {} ==>
    (?y Gy Ty. (^path) s G tn (OK y) Gy Ty /\
      ~y.vs_halted /\ y.vs_current_bb = sg.cs_current_bb /\
      y.vs_inst_idx = LENGTH sg.cs_current_insts /\
      (^os) sg y Gy Ty /\ off+32+c <= h /\
      y.vs_memory = s.vs_memory /\ Ty.t_mem = tn.t_mem /\ allocas_from lo y /\
      (^frame) sc s G tn y Gy Ty /\ (^obs) sc sg s (OK y) /\
      cs_extends sc sg /\ LENGTH sc.cs_current_insts <= LENGTH sg.cs_current_insts /\
      sc.cs_next_var <= sg.cs_next_var /\ sc.cs_next_id <= sg.cs_next_id /\
      (^finite) sc sg (s,G,tn) (y,Gy,Ty)) \/
    ^(abort ``sc:compile_state`` ``sg:compile_state``)``
  val reached = ``?sg dstv ar cnt off h c y Gy Ty.
    dst = Var dstv /\ (^cut) start sg /\
    (^path) s G tn (OK y) Gy Ty /\ (^obs) start sg s (OK y) /\
    (^finite) start sg (s,G,tn) (y,Gy,Ty) /\ (^frame) start s G tn y Gy Ty /\
    y.vs_memory = s.vs_memory /\ Ty.t_mem = tn.t_mem /\
    abi_decode_bytes_runtime_tail (Var dstv) (Var ar) cnt sg = ((),(fin:compile_state)) /\
    cs_extends sg fin /\ fn_has_code sg fin fn /\ fn_inst_ids_distinct fn /\ (?H. V H) /\
    (^cursor) sg y /\ (^os) sg y Gy Ty /\ (^io) y /\
    local_ptrs_reserved ce sg /\ not_fresh_at sg input /\
    not_fresh_at sg dstv /\ not_fresh_at sg ar /\ (^reserve) sg /\
    lookup_var dstv y = SOME (n2w d) /\ FLOOKUP Gy dstv = SOME (output_base,output_cap) /\
    op_taint Ty (Var dstv) = {} /\ ptr_covers Gy Ty dstv y (type_memory_size tv) /\
    abi_decode_ptr_window Gy Ty y ar (n2w (w2n input_word+off)) (32+c) /\
    abi_decoder_operand_live sg.cs_next_var cnt /\ eval_operand cnt y = SOME (n2w c) /\
    op_prov Gy cnt = NONE /\ op_taint Ty cnt = {} /\
    off+32 <= h /\ c <= n /\ off+32+c <= h /\ h <= LENGTH input_bytes /\
    w2n input_word+LENGTH input_bytes < dimword (:256) /\
    mem_word_at (w2n input_word+off) y.vs_memory = n2w c /\
    n+31 < dimword (:256) /\ type_memory_size tv = 32+32*((n+31) DIV 32) /\
    abi_decoder_coherent ce env sf ty tv /\ DecBytestring n = type_to_abi_dec_info sf ce ty /\
    output_base <= d /\ d <= d /\ d+type_memory_size tv <= output_base+output_cap /\
    (w2n input_word+LENGTH input_bytes <= d \/ d+type_memory_size tv <= w2n input_word) /\
    EVERY (\(aid,p,b,k,bytes). aid < sg.cs_next_id /\
      (b+k <= d \/ d+type_memory_size tv <= b)) live /\
    EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+type_memory_size tv <= a) protected``
  val prefix = close (list_mk_forall (prefix_vs,
    mk_imp (pre,mk_disj (abort ``start:compile_state`` ``fin:compile_state``,reached))))
  val packed = list_mk_imp ([guard abi_decode_bytes_head_joint_observed,load,
    guard abi_decode_bytes_count_joint_observed,payload],prefix)
in
  val prefix_raw = packed
  val prefix_closed = rhs (concl (DEPTH_CONV BETA_CONV packed))
  val owned_decoder_state = os
  val input_origin = io
  val finite_packet = finite
  val frame_packet = frame
end

Theorem prefix_finite_append[local]:
  LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
  LENGTH b.cs_current_insts <= LENGTH c.cs_current_insts /\
  (^finite_packet) a b q p /\ (^finite_packet) b c p r ==>
  (^finite_packet) a c q r
Proof
  BETA_TAC >> strip_tac >> gen_tac >>
  `LENGTH c.cs_current_insts - LENGTH a.cs_current_insts =
   (LENGTH b.cs_current_insts - LENGTH a.cs_current_insts) +
   (LENGTH c.cs_current_insts - LENGTH b.cs_current_insts)` by decide_tac >>
  asm_rewrite_tac[] >> irule NRC_ADD_I >> qexists_tac `p` >> simp[]
QED

Theorem prefix_operand_frame[local]:
  (^frame_packet) a s G tn t Gtf Tt /\ t.vs_labels = s.vs_labels /\
  abi_decoder_operand_live a.cs_next_var op ==>
  eval_operand op t = eval_operand op s /\
  op_prov Gtf op = op_prov G op /\ op_taint Tt op = op_taint tn op
Proof
  BETA_TAC >> Cases_on `op` >>
  simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def,
       eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]
QED

Theorem prefix_length_mono[local]:
  inst_extends a b ==> LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts
Proof
  simp[inst_extends_def]
QED

fun owned_facts state tt =
  qpat_assum `Abbrev (OS = _)` (fn ab =>
    qpat_assum `OS _ ^state _ _`
      (tt o BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]));

fun owned_fmp_at state =
  owned_facts state (map_every assume_tac o CONJUNCTS) >>
  strip_tac >> irule owned_decoder_allocas_below_fmp >>
  qexistsl_tac [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (drule_then (ACCEPT_TAC o CONJUNCT1));

fun phase l = qpat_assum `Abbrev (OS = _)` (fn ab =>
  asm_x l (drule_all o BETA_RULE o
    PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)] o SPEC_ALL));

Theorem bytes_prefix_raw[local]:
  ^prefix_raw
Proof
  map_every (fn l => disch_then (mk_asm l)) ["phase_head","phase_load","phase_count","phase_payload"] >>
  rpt gen_tac >> qabbrev_tac `OS = (^owned_decoder_state)` >>
  qabbrev_tac `IO = (^input_origin)` >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size tv = 32+32*((n+31) DIV 32)` by
    (drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >>
     gvs[valueEncodingTheory.type_memory_size_def,vfmConstantsTheory.word_size_def]) >>
  `output_base+output_cap < dimword (:256)` by
    (owned_facts ``s:venom_state`` (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC) >>
  `n+31 < dimword (:256)` by
    (mp_tac (abi_decode_bytes_round_bounds |> Q.INST [`c` |-> `n`]) >> decide_tac) >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _` kall_tac >>
  qpat_x_assum `?off h. _`
    (qx_choose_then `off` (qx_choose_then `h` (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `dstv` strip_assume_tac) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`dst = Var dstv`, `base_op = Var input`, `opc = MLOAD`] >>
  drule_all abi_decode_bytes_member_phases >>
  strip_tac >>
  rename [`abi_decode_bytes_head src hi start = (head,sh)`,
    `compile_abi_dec_addr (Var input) src sh = (addr,sa)`,
    `emit_op MLOAD [addr] sa = (cnt,sl)`,
    `abi_decode_le_guard cnt (Lit (n2w n)) sl = ((),sc)`,
    `abi_decode_bytes_payload_guard head cnt hi sc = ((),sg)`] >>
  `cs_extends start sh /\ cs_extends sh sa /\ cs_extends sa sl /\
   cs_extends sl sc /\ cs_extends sc sg /\ cs_extends sg fin` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND]) >>
  `cs_extends sh sl` by (irule cs_extends_trans >> qexists_tac `sa` >> simp[]) >>
  `cs_extends sc fin` by (irule cs_extends_trans >> qexists_tac `sg` >> simp[]) >>
  `cs_extends sl fin` by (irule cs_extends_trans >> qexists_tac `sc` >> simp[]) >>
  `cs_extends sh fin` by (irule cs_extends_trans >> qexists_tac `sl` >> simp[]) >>
  `fn_has_code start sh fn /\ fn_has_code sh sl fn /\ fn_has_code sl sc fn /\
   fn_has_code sc sg fn /\ fn_has_code sg fin fn` by
    (map_every (fn args => qspecl_then args mp_tac fn_has_code_split >> simp[] >> strip_tac)
       [[`start`,`sh`,`fin`,`fn`], [`sh`,`sl`,`fin`,`fn`],
        [`sl`,`sc`,`fin`,`fn`], [`sc`,`sg`,`fin`,`fn`]] >> simp[]) >>
  `h < dimword (:256)` by decide_tac >>
  `allocas_from lo s /\ origin.cs_next_var <= start.cs_next_var` by
    (owned_facts ``s:venom_state`` (map_every assume_tac o CONJUNCTS) >>
     simp[] >> qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _` mp_tac >>
     qpat_assum `?H. V H` mp_tac >> rpt (pop_assum kall_tac) >>
     metis_tac[ghost_inv_at_def]) >>
  `not_fresh_at start input /\ not_fresh_at start dstv` by
    fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by (owned_fmp_at ``s:venom_state``) >>
  phase "phase_head" >>
  reverse (disch_then (qspecl_then [`explicit`,`PG`]
    (DISJ_CASES_THEN2
      (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `Tu` strip_assume_tac)))
      (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac))))))
  >- (disj1_tac >> qexistsl_tac [`z`,`Gz`,`Tz`] >> conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `obs` >> disch_tac >>
      qspecl_then [`start`,`sh`,`fin`,`obs`] mp_tac fn_has_code_split >> simp[]) >>
  suspend "load"
QED

Resume bytes_prefix_raw[load]:
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK u,Gu,Tu)`
      (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_preserves_labels)) >> simp[]) >>
  `eval_operand src u = SOME (n2w off) /\ op_taint Tu src = {}` by
    (`eval_operand src u = eval_operand src s /\ op_prov Gu src = op_prov G src /\
      op_taint Tu src = op_taint tn src` by
       (irule (BETA_RULE prefix_operand_frame) >> simp[] >> qexists_tac `start` >> simp[]) >>
     simp[]) >>
  `not_fresh_at sh input /\ local_ptrs_reserved ce sh /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x)` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
  `off+32 <= LENGTH input_bytes` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by (owned_fmp_at ``u:venom_state``) >>
  phase "phase_load" >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `out` (qx_choose_then `ar` (qx_choose_then `v`
      (qx_choose_then `Gv` (qx_choose_then `Tv` strip_assume_tac)))))) >>
  suspend "count"
QED

Resume bytes_prefix_raw[count]:
  `cs_extends start sl` by (irule cs_extends_trans >> qexists_tac `sh` >> simp[]) >>
  `sh.cs_next_var <= sl.cs_next_var /\ sh.cs_next_id <= sl.cs_next_id` by
    (`emit_op ADD [Var input;src] sh = (addr,sa)` by fs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     qpat_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP emit_op_next_id) >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_tac o MATCH_MP emit_op_next_id) >> decide_tac) >>
  `LENGTH sh.cs_current_insts <= LENGTH sl.cs_current_insts` by
    (irule prefix_length_mono >> irule inst_extends_trans >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sl input /\ local_ptrs_reserved ce sl /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x)` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sh` >> simp[]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sh` >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sh` >> simp[]) >>
  qabbrev_tac `c = w2n (mload (w2n input_word+off) u)` >>
  `mload (w2n input_word+off) u = (n2w c:bytes32) /\ c < dimword (:256)` by
    simp[Abbr `c`,w2n_lt] >>
  `eval_operand cnt v = SOME (n2w c) /\ n < dimword (:256)` by (simp[] >> decide_tac) >>
  `abi_decoder_operand_live sl.cs_next_var cnt` by
    fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by (owned_fmp_at ``v:venom_state``) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,Gv,Tv)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`Tu`] >> simp[]) >>
  `!obs. fn_has_code start sl obs ==> gas_path ctx obs s 0 (OK v)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sh`,`sl`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `u` >> simp[]) >>
  phase "phase_count" >>
  reverse (disch_then (qspecl_then [`explicit`,`PG`]
    (DISJ_CASES_THEN2
      (qx_choose_then `w` (qx_choose_then `Gw` (qx_choose_then `Tw` strip_assume_tac)))
      (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac))))))
  >- (disj1_tac >> qexistsl_tac [`z`,`Gz`,`Tz`] >> conj_tac
      >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[]) >>
      qx_gen_tac `obs` >> disch_tac >>
      qspecl_then [`start`,`sl`,`fin`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
      qspecl_then [`sl`,`sc`,`fin`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
      qexists_tac `v` >> simp[]) >>
  suspend "payload"
QED

Resume bytes_prefix_raw[payload]:
  `cs_extends start sc` by (irule cs_extends_trans >> qexists_tac `sl` >> simp[]) >>
  `v.vs_labels = u.vs_labels /\ w.vs_labels = v.vs_labels` by
    (conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,Tu) _ (OK v,Gv,Tv)`
          (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_preserves_labels)) >> simp[]) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,Gv,Tv) _ (OK w,Gw,Tw)`
       (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_preserves_labels)) >> simp[]) >>
  `abi_decoder_operand_live sh.cs_next_var head` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     simp[abi_decode_bytes_head_def,compile_abi_decode_range_check_def,emit_op_def,emit_void_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def]) >>
  `start.cs_next_var <= sc.cs_next_var /\ sh.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live sc.cs_next_var head /\
   abi_decoder_operand_live sc.cs_next_var cnt /\ abi_decoder_operand_live sc.cs_next_var hi` by
    (conj_tac >- (irule abi_decoder_operand_live_mono >> qexists_tac `sh.cs_next_var` >> simp[]) >>
     conj_tac >- (irule abi_decoder_operand_live_mono >> qexists_tac `sl.cs_next_var` >> simp[]) >>
     irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  `!x. not_fresh_at sh x ==> lookup_var x w = lookup_var x u /\
       FLOOKUP Gw x = FLOOKUP Gu x /\ op_taint Tw (Var x) = op_taint Tu (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sl x` by (irule not_fresh_at_mono >> qexists_tac `sh` >> simp[]) >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x w = lookup_var x s /\
       FLOOKUP Gw x = FLOOKUP G x /\ op_taint Tw (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sh x` by (irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >> simp[]) >>
  `eval_operand head w = eval_operand head u /\
   op_prov Gw head = op_prov Gu head /\ op_taint Tw head = op_taint Tu head` by
    (irule (BETA_RULE prefix_operand_frame) >> simp[] >> qexists_tac `sh` >> simp[]) >>
  `eval_operand hi w = eval_operand hi s /\
   op_prov Gw hi = op_prov G hi /\ op_taint Tw hi = op_taint tn hi` by
    (irule (BETA_RULE prefix_operand_frame) >> simp[] >> qexists_tac `start` >> simp[]) >>
  `eval_operand cnt w = eval_operand cnt v /\
   op_prov Gw cnt = op_prov Gv cnt /\ op_taint Tw cnt = op_taint Tv cnt` by
    (irule (BETA_RULE prefix_operand_frame) >> simp[] >> qexists_tac `sl` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,GSYM not_fresh_at_def]) >>
  `eval_operand head w = SOME (n2w (off+32)) /\ op_prov Gw head = NONE /\ op_taint Tw head = {} /\
   eval_operand hi w = SOME (n2w h) /\ op_prov Gw hi = NONE /\ op_taint Tw hi = {} /\
   eval_operand cnt w = SOME (n2w c) /\ op_prov Gw cnt = NONE /\ op_taint Tw cnt = {}` by simp[] >>
  `off+32 < dimword (:256)` by decide_tac >>
  `not_fresh_at sc input /\ local_ptrs_reserved ce sc /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sl` >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp w` by (owned_fmp_at ``w:venom_state``) >>
  suspend "apply_payload"
QED

Resume bytes_prefix_raw[apply_payload]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK w,Gw,Tw)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[]) >>
  `!obs. fn_has_code start sc obs ==> gas_path ctx obs s 0 (OK w)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sl`,`sc`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `v` >> simp[]) >>
  phase "phase_payload" >>
  reverse (disch_then (qspecl_then [`explicit`,`PG`]
    (DISJ_CASES_THEN2
      (qx_choose_then `y` (qx_choose_then `Gy` (qx_choose_then `Ty` strip_assume_tac)))
      (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `Tz` strip_assume_tac))))))
  >- (disj1_tac >> qexistsl_tac [`z`,`Gz`,`Tz`] >> conj_tac
      >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gw`,`w`,`Tw`] >> simp[]) >>
      qx_gen_tac `obs` >> disch_tac >>
      qspecl_then [`start`,`sc`,`fin`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
      qspecl_then [`sc`,`sg`,`fin`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
      qexists_tac `w` >> simp[]) >>
  suspend "reached"
QED

Resume bytes_prefix_raw[reached]:
  `cs_extends start sg` by (irule cs_extends_trans >> qexists_tac `sc` >> simp[]) >>
  `LENGTH start.cs_current_insts <= LENGTH sl.cs_current_insts /\
   LENGTH start.cs_current_insts <= LENGTH sc.cs_current_insts /\
   LENGTH start.cs_current_insts <= LENGTH sg.cs_current_insts /\
   start.cs_next_var <= sg.cs_next_var /\ start.cs_next_id <= sg.cs_next_id /\
   sl.cs_next_var <= sg.cs_next_var` by decide_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK y,Gy,Ty)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gw`,`w`,`Tw`] >> simp[]) >>
  `!obs. fn_has_code start sg obs ==> gas_path ctx obs s 0 (OK y)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qspecl_then [`start`,`sc`,`sg`,`obs`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
     irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `w` >> simp[]) >>
  `!D. RELPOW (\(a,Ga,Ta) (b,Gb,Tb).
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (a,Ga,Ta) [] (OK b,Gb,Tb))
     (LENGTH sl.cs_current_insts - LENGTH start.cs_current_insts) (s,G,tn) (v,Gv,Tv)` by
    (gen_tac >> irule (BETA_RULE prefix_finite_append) >>
     qexistsl_tac [`sh`,`(u,Gu,Tu)`] >> simp[]) >>
  `!D. RELPOW (\(a,Ga,Ta) (b,Gb,Tb).
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (a,Ga,Ta) [] (OK b,Gb,Tb))
     (LENGTH sc.cs_current_insts - LENGTH start.cs_current_insts) (s,G,tn) (w,Gw,Tw)` by
    (gen_tac >> irule (BETA_RULE prefix_finite_append) >>
     qexistsl_tac [`sl`,`(v,Gv,Tv)`] >> simp[]) >>
  `!D. RELPOW (\(a,Ga,Ta) (b,Gb,Tb).
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (a,Ga,Ta) [] (OK b,Gb,Tb))
     (LENGTH sg.cs_current_insts - LENGTH start.cs_current_insts) (s,G,tn) (y,Gy,Ty)` by
    (gen_tac >> irule (BETA_RULE prefix_finite_append) >>
     qexistsl_tac [`sc`,`(w,Gw,Tw)`] >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x y = lookup_var x s /\
       FLOOKUP Gy x = FLOOKUP G x /\ op_taint Ty (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sc x` by (irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >> simp[]) >>
  `!x. not_fresh_at sl x ==> lookup_var x y = lookup_var x v /\
       FLOOKUP Gy x = FLOOKUP Gv x /\ op_taint Ty (Var x) = op_taint Tv (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sc x` by (irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >> simp[]) >>
  suspend "tail_entry"
QED

Resume bytes_prefix_raw[tail_entry]:
  `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP y.vs_allocas aid = SOME b` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK y,Gy,Ty)`
       (qspec_then `ARB` (mp_tac o CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections)) >>
     disch_then (mp_tac o MATCH_MP gas_path_ptr_old_allocations) >> simp[]) >>
  `IO y` by
    (qpat_assum `Abbrev (IO = _)` (fn th =>
       qpat_assum `IO s` (mp_tac o BETA_RULE o PURE_REWRITE_RULE
         [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th] >> BETA_TAC) >>
     disch_tac >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`start`] >> simp[]) >>
  `not_fresh_at sg input /\ not_fresh_at sg dstv /\ not_fresh_at sg ar` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
     conj_tac >- (irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
     irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
  `local_ptrs_reserved ce sg /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x)` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
  `lookup_var dstv y = SOME (n2w d) /\
   FLOOKUP Gy dstv = SOME (output_base,output_cap) /\ op_taint Ty (Var dstv) = {}` by
    (qpat_x_assum `eval_operand (Var dstv) s = _`
       (assume_tac o REWRITE_RULE [eval_operand_def]) >> simp[]) >>
  `ptr_covers Gy Ty dstv y (type_memory_size tv)` by
    (`ptr_covers G tn dstv s (type_memory_size tv)` by
       (qpat_assum `ptr_covers G tn dstv s _` (mp_tac o SIMP_RULE (srw_ss()) []) >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x y = _ /\ _`
       (qspec_then `dstv` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Gy Ty y ar (input_word+n2w off) (LENGTH input_bytes-off)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gv`,`v`,`Tv`] >> simp[]) >>
  `w2n input_word+off < dimword (:256) /\ 32+c <= LENGTH input_bytes-off` by decide_tac >>
  `input_word + n2w off = (n2w (w2n input_word + off):bytes32)` by
    (CONV_TAC (RHS_CONV (REWR_CONV (GSYM word_add_n2w))) >> simp[n2w_w2n]) >>
  `abi_decode_ptr_window Gy Ty y ar (n2w (w2n input_word+off)) (32+c)` by
    (qpat_x_assum `abi_decode_ptr_window Gy Ty y ar (input_word+n2w off) _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_ptr_window_def]) >>
     simp[abi_decode_ptr_window_def] >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `LENGTH input_bytes-off` >> simp[]) >>
  suspend "publish"
QED

Resume bytes_prefix_raw[publish]:
  `abi_decoder_operand_live sg.cs_next_var cnt` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `sl.cs_next_var` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,GSYM not_fresh_at_def]) >>
  `eval_operand cnt y = SOME (n2w c) /\ op_prov Gy cnt = NONE /\ op_taint Ty cnt = {}` by
    (qpat_assum `cnt = Var out` SUBST_ALL_TAC >>
     qpat_assum `eval_operand (Var out) v = SOME (n2w c)`
       (assume_tac o REWRITE_RULE [eval_operand_def]) >>
     qpat_assum `op_prov Gv (Var out) = NONE`
       (assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >> simp[eval_operand_def,op_prov_def]) >>
  `mem_word_at (w2n input_word+off) y.vs_memory = n2w c` by
    (qpat_assum `mload (w2n input_word+off) u = _`
       (mp_tac o PURE_REWRITE_RULE [GSYM mem_word_at_eq_mload]) >> asm_rewrite_tac[]) >>
  `EVERY (\(aid,p,b,k,bytes). aid < sg.cs_next_id /\
     (b+k <= d \/ d+type_memory_size tv <= b)) live` by
    (qpat_assum `EVERY _ live` (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     simp[EVERY_MEM,FORALL_PROD] >> rpt strip_tac >> res_tac >> decide_tac) >>
  disj2_tac >> qexistsl_tac [`sg`,`dstv`,`ar`,`cnt`,`off`,`h`,`c`,`y`,`Gy`,`Ty`] >>
  qpat_assum `addr = Var ar` SUBST_ALL_TAC >> asm_rewrite_tac[] >> simp[]
QED

Finalise bytes_prefix_raw

Theorem bytes_prefix_finite_if_phases:
  ^prefix_closed
Proof
  ACCEPT_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) bytes_prefix_raw)
QED
