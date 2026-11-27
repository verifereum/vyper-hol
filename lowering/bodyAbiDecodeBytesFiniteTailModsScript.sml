Theory bodyAbiDecodeBytesFiniteTailMods
Ancestors
  bodyFullAbiDecodeGuardReadObserved bodyFullAbiDecodeOwnedWordStoreObserved
  bodyFullAbiDecodeOwnedCopyEffect bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeOwnedStateProps abiDecoderBytesPhases abiDecoderBytestringCases
  abiCanonicalHeadSize abiDecoderBytestringSource abiDecodePtrBytesMember
  bodyPtrBopScalarSeq[qualified,ignore_grammar] bodyPtrBopScalarCompile
  fragGasOriginPtr fragGasPath fragExec forPtrAllocationFrame
  emitHelperProps exprLoweringProps loweringShapeRules freshWrites compileEnv
  abiDecoderReentry abiDecodePtrMemberFrame stateRelProj bodyPtrDefs ptrDiscipline loweringStateRelDefs
  allocaSiteResource fragGasOriginPtrLoop gasOriginPtrLabels ghostPcTransportPtr
  exprSimCopy valueEncodingProps assignTuplePtrStoreWord
  venomState venomInst venomExecSemantics venomMemDefs words pair
  finite_map relation pred_set rich_list list

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

val finite_slice = ``\a b q q'. !D.
  RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH b.cs_current_insts - LENGTH a.cs_current_insts) q q'``;

fun close_implicit tm =
  let
    val normalized = rhs (concl (QCONV (DEPTH_CONV BETA_CONV) tm))
    val (qs,body) = strip_forall normalized
  in list_mk_forall (qs @ free_vars_lr normalized,body) end;

(* Append fields inside the existing success binders, without changing the
   preceding contract or introducing a shared logical constant. *)
fun finite_phase th append_obs clean_pre =
  let
    val old = concl (BETA_RULE th)
    val (pre,post) = dest_imp old
    val (ws,fields) = strip_exists post
    val (t,gf,tf) = case ws of [t,gf,tf] => (t,gf,tf)
      | _ => raise Fail "expected phase result triple"
    fun arg name = valOf (List.find (fn v => fst (dest_var v) = name) (free_vars old))
    val sa = arg "sa" and sb = arg "sb" and s = arg "s"
    val ctx = arg "ctx" and lo = arg "lo" and explicit = arg "explicit"
    val fn_tm = arg "fn" and pg = arg "PG" and g = arg "G" and tn = arg "tn"
    val obs = ``!obs. fn_has_code ^sa ^sb obs ==> gas_path ^ctx obs ^s 0 (OK ^t)``
    val finite = ``!D. RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,^lo,^explicit,^ctx,^fn_tm,^pg) (u,Gu,tu) [] (OK v,Gv,tv))
      (LENGTH ^sb.cs_current_insts - LENGTH ^sa.cs_current_insts) (^s,^g,^tn) (^t,^gf,^tf)``
    fun add tm =
      if is_conj tm then
        let val (p,q) = dest_conj tm in mk_conj (p,add q) end
      else list_mk_conj (tm :: (if append_obs then [obs,finite] else [finite]))
  in close_implicit (mk_imp (clean_pre pre,list_mk_exists (ws,add fields))) end;

val scalar_phase = finite_phase abi_decode_bytes_scalar_frame_joint true I;
val copy_phase = finite_phase abi_decode_owned_mcopy_joint_effect true I;
fun zero_pre tm =
  if is_conj tm then
    let val (p,q) = dest_conj tm in
      if can (match_term ``eval_operand (Lit 0w) s = SOME 0w``) p orelse
         can (match_term ``op_taint tn (Lit 0w) = {}``) p
      then zero_pre q else mk_conj (p,zero_pre q)
    end
  else tm;

val zero_phase = finite_phase
  (Q.INST [`value` |-> `Lit 0w`, `w` |-> `0w`] abi_decode_owned_word_store_observed_exact)
  false zero_pre;

val round_phase = close_implicit ``
  emit_op ADD [cnt;Lit 31w] sg = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,c3) /\
  emit_op ADD [Var dstv;rounded] c3 = (Var padvar,c4) /\
  fn_has_code sg c4 fn /\
  ~y.vs_halted /\ y.vs_current_bb = sg.cs_current_bb /\
  y.vs_inst_idx = LENGTH sg.cs_current_insts /\
  (^owned_decoder_state) sg y Gy Ty /\ (^input_origin) y /\
  (?H. V H) /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sg /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
  not_fresh_at sg input /\ not_fresh_at sg dstv /\
  lookup_var dstv y = SOME (n2w d) /\
  FLOOKUP Gy dstv = SOME (output_base,output_cap) /\ op_taint Ty (Var dstv) = {} /\
  ptr_covers Gy Ty dstv y (type_memory_size tv) /\
  abi_decoder_operand_live sg.cs_next_var cnt /\
  eval_operand cnt y = SOME (n2w c) /\ op_prov Gy cnt = NONE /\ op_taint Ty cnt = {} /\
  c <= n /\ n+31 < dimword (:256) /\ type_memory_size tv = 32+32*((n+31) DIV 32) /\
  output_base <= d /\ d <= d /\ d+type_memory_size tv <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+type_memory_size tv <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+type_memory_size tv <= b) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+type_memory_size tv <= a) protected ==>
  ?z4 G4 T4.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (y,Gy,Ty) [] (OK z4,G4,T4)) /\
    ~z4.vs_halted /\ z4.vs_current_bb = c4.cs_current_bb /\
    z4.vs_inst_idx = LENGTH c4.cs_current_insts /\
    (^owned_decoder_state) c4 z4 G4 T4 /\
    lookup_var padvar z4 = SOME (n2w (d+32*((c+31) DIV 32))) /\
    ptr_covers G4 T4 padvar z4 32 /\ (^input_origin) z4 /\
    z4.vs_memory = y.vs_memory /\ T4.t_mem = Ty.t_mem /\
    (!x. not_fresh_at sg x ==> lookup_var x z4 = lookup_var x y /\
      FLOOKUP G4 x = FLOOKUP Gy x /\ op_taint T4 (Var x) = op_taint Ty (Var x)) /\
    cs_extends sg c4 /\ LENGTH sg.cs_current_insts <= LENGTH c4.cs_current_insts /\
    sg.cs_next_var <= c4.cs_next_var /\ sg.cs_next_id <= c4.cs_next_id /\
    (!obs. fn_has_code sg c4 obs ==> gas_path ctx obs y 0 (OK z4)) /\
    (^finite_slice) sg c4 (y,Gy,Ty) (z4,G4,T4)``;

val tail_contract = close_implicit ``
  abi_decode_bytes_runtime_tail (Var dstv) (Var ar) cnt sg = ((),fin) /\
  cs_extends sg fin /\ fn_has_code sg fin fn /\ fn_inst_ids_distinct fn /\
  (?H. V H) /\ ~y.vs_halted /\ y.vs_current_bb = sg.cs_current_bb /\
  y.vs_inst_idx = LENGTH sg.cs_current_insts /\
  (^owned_decoder_state) sg y Gy Ty /\ (^input_origin) y /\
  local_ptrs_reserved ce sg /\
  not_fresh_at sg input /\ not_fresh_at sg dstv /\ not_fresh_at sg ar /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
  lookup_var dstv y = SOME (n2w d) /\
  FLOOKUP Gy dstv = SOME (output_base,output_cap) /\ op_taint Ty (Var dstv) = {} /\
  ptr_covers Gy Ty dstv y (type_memory_size tv) /\
  abi_decode_ptr_window Gy Ty y ar (n2w (w2n input_word+off)) (32+c) /\
  abi_decoder_operand_live sg.cs_next_var cnt /\
  eval_operand cnt y = SOME (n2w c) /\ op_prov Gy cnt = NONE /\ op_taint Ty cnt = {} /\
  off+32 <= h /\ c <= n /\ off+32+c <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  mem_word_at (w2n input_word+off) y.vs_memory = n2w c /\ n+31 < dimword (:256) /\
  type_memory_size tv = 32+32*((n+31) DIV 32) /\
  abi_decoder_coherent ce env sf ty tv /\ DecBytestring n = type_to_abi_dec_info sf ce ty /\
  output_base <= d /\ d <= d /\ d+type_memory_size tv <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+type_memory_size tv <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+type_memory_size tv <= b) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+type_memory_size tv <= a) protected ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (y,Gy,Ty) [] (OK t,G',tn')) /\
    (!obs. fn_has_code sg fin obs ==> gas_path ctx obs y 0 (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = fin.cs_current_bb /\
    t.vs_inst_idx = LENGTH fin.cs_current_insts /\
    (^owned_decoder_state) fin t G' tn' /\
    (!x. not_fresh_at sg x ==> lookup_var x t = lookup_var x y /\
      FLOOKUP G' x = FLOOKUP Gy x /\ op_taint tn' (Var x) = op_taint Ty (Var x)) /\
    (^input_origin) t /\
    (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tn'.t_mem ==>
      i IN Ty.t_mem) /\
    (!v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
      !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) /\
    (^finite_slice) sg fin (y,Gy,Ty) (t,G',tn')``;

Theorem tail_op_cut[local]:
  emit_op op args a = (out,b) ==>
  cs_extends a b /\ inst_extends a b /\ b.cs_current_bb = a.cs_current_bb /\
  LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
  rpt conj_tac >> simp[cs_extends_same_block, IS_PREFIX_APPEND, inst_extends_emit_op] >>
  metis_tac[cs_extends_same_block,IS_PREFIX_APPEND,inst_extends_emit_op]
QED

Theorem tail_void_cut[local]:
  emit_void op args a = ((),b) ==>
  cs_extends a b /\ LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem tail_frame_operand[local]:
  abi_decoder_operand_live a.cs_next_var op /\ t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  eval_operand op t = eval_operand op s /\
  op_prov Gf op = op_prov G op /\ op_taint tf op = op_taint tn op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def,
       eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]
QED

Theorem tail_finite_then[local]:
  LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
  LENGTH b.cs_current_insts <= LENGTH c.cs_current_insts /\
  RELPOW R (LENGTH b.cs_current_insts - LENGTH a.cs_current_insts) x y /\
  RELPOW R (LENGTH c.cs_current_insts - LENGTH b.cs_current_insts) y z ==>
  RELPOW R (LENGTH c.cs_current_insts - LENGTH a.cs_current_insts) x z
Proof
  strip_tac >>
  `LENGTH c.cs_current_insts - LENGTH a.cs_current_insts =
   (LENGTH b.cs_current_insts - LENGTH a.cs_current_insts) +
   (LENGTH c.cs_current_insts - LENGTH b.cs_current_insts)` by decide_tac >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  irule arithmeticTheory.NRC_ADD_I >> qexists_tac `y` >> simp[]
QED

fun open_owned pat =
  qpat_assum `Abbrev (OS = _)` (fn ab =>
    qpat_assum pat (map_every assume_tac o CONJUNCTS o BETA_RULE o
      PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]));

fun fold_abbrev th =
  let
    val eq = REWRITE_RULE [markerTheory.Abbrev_def] th
    val args = map (genvar o type_of) (#1 (strip_abs (rhs (concl eq))))
  in GSYM (BETA_RULE (List.foldl (fn (arg,t) => AP_THM t arg) eq args)) end;

fun apply_phase label args =
  qpat_assum `Abbrev (OS = _)` (fn os =>
    qpat_assum `Abbrev (IO = _)` (fn io =>
      asm_x label (mp_tac o PURE_REWRITE_RULE (map fold_abbrev [os,io]) o
        BETA_RULE o Q.INST args o SPEC_ALL)));

Theorem bytes_tail_finite_if_phases:
  ^round_phase ==> ^zero_phase ==> ^scalar_phase ==> ^copy_phase ==> ^tail_contract
Proof
  disch_then (mk_asm "round") >> disch_then (mk_asm "store") >>
  disch_then (mk_asm "scalar") >> disch_then (mk_asm "copy") >>
  rpt gen_tac >>
  qabbrev_tac `OS = (^owned_decoder_state)` >>
  qabbrev_tac `IO = (^input_origin)` >>
  qpat_assum `Abbrev (OS = _)` (fn os =>
    qpat_assum `Abbrev (IO = _)` (fn io => PURE_REWRITE_TAC (map fold_abbrev [os,io]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emit_op ADD [cnt;Lit 31w] sg` >>
  rename1 `emit_op ADD [cnt;Lit 31w] sg = (up,c1)` >>
  Cases_on `emit_op NOT [Lit 31w] c1` >>
  rename1 `emit_op NOT [Lit 31w] c1 = (mask,c2)` >>
  Cases_on `emit_op AND [up;mask] c2` >>
  rename1 `emit_op AND [up;mask] c2 = (rounded,c3)` >>
  Cases_on `emit_op ADD [Var dstv;rounded] c3` >>
  rename1 `emit_op ADD [Var dstv;rounded] c3 = (last,c4)` >>
  `?padvar. last = Var padvar` by
    (qpat_assum `emit_op ADD [Var dstv;rounded] c3 = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  qpat_x_assum `last = Var padvar` SUBST_ALL_TAC >>
  Cases_on `emit_void MSTORE [Var padvar;Lit 0w] c4` >>
  rename1 `emit_void MSTORE [Var padvar;Lit 0w] c4 = (u,c5)` >> Cases_on `u` >>
  Cases_on `emit_op ADD [Lit 32w;cnt] c5` >>
  rename1 `emit_op ADD [Lit 32w;cnt] c5 = (copysz,c6)` >>
  `emit_void MCOPY [Var dstv;Var ar;copysz] c6 = ((),fin)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_bytes_runtime_tail _ _ _ _ = _`,
        `emit_op ADD [cnt;Lit 31w] sg = _`, `emit_op NOT _ c1 = _`,
        `emit_op AND _ c2 = _`, `emit_op ADD _ c3 = _`,
        `emit_void MSTORE _ c4 = _`, `emit_op ADD _ c5 = _`] >>
     rpt (pop_assum kall_tac) >> ntac 6 disch_tac >>
     simp[abi_decode_bytes_runtime_tail_def,comp_bind_def,comp_ignore_bind_def]) >>
  map_every (fn pat => qpat_assum pat (mp_then Any strip_assume_tac tail_op_cut))
    [`emit_op ADD [cnt;Lit 31w] sg = _`,`emit_op NOT _ c1 = _`,
     `emit_op AND _ c2 = _`,`emit_op ADD _ c3 = _`,`emit_op ADD _ c5 = _`] >>
  map_every (fn pat => qpat_assum pat (mp_then Any strip_assume_tac tail_void_cut))
    [`emit_void MSTORE _ c4 = _`,`emit_void MCOPY _ c6 = _`] >>
  `cs_extends sg c4` by
    (irule cs_extends_trans >> qexists_tac `c3` >> asm_rewrite_tac[] >>
     irule cs_extends_trans >> qexists_tac `c2` >> asm_rewrite_tac[] >>
     irule cs_extends_trans >> qexists_tac `c1` >> asm_rewrite_tac[]) >>
  `cs_extends c5 fin` by (irule cs_extends_trans >> qexists_tac `c6` >> asm_rewrite_tac[]) >>
  `cs_extends c4 fin` by (irule cs_extends_trans >> qexists_tac `c5` >> asm_rewrite_tac[]) >>
  map_every (fn args => qspecl_then args mp_tac fn_has_code_split >>
    (impl_tac >- asm_rewrite_tac[]) >> strip_tac)
    [[`sg`,`c4`,`fin`,`fn`],[`c4`,`c5`,`fin`,`fn`],[`c5`,`c6`,`fin`,`fn`]] >>
  apply_phase "round" [] >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choose_then `z4` (qx_choose_then `G4` (qx_choose_then `T4`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "store"
QED

Resume bytes_tail_finite_if_phases[store]:
  `32*((c+31) DIV 32) <= 32*((n+31) DIV 32)` by
    (`(c+31) DIV 32 <= (n+31) DIV 32` by (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
     decide_tac) >>
  qabbrev_tac `pad = d + 32*((c+31) DIV 32)` >>
  `d <= pad /\ pad+32 <= d+type_memory_size tv` by
    (simp[Abbr `pad`] >> decide_tac) >>
  `output_base+output_cap <= z4.vs_alloca_next /\ output_base+output_cap < dimword (:256)` by
    (open_owned `OS c4 z4 G4 T4` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     `alloca_inv z4` by
       (qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
          qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ z4 /\ _`
            (assume_tac o CONJUNCT1 o (fn th => MATCH_MP th vh)))) >>
        drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     irule alloca_site_registered_below >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `output_id` >> first_assum ACCEPT_TAC) >>
  `pad < dimword (:256)` by decide_tac >>
  `w2n (n2w pad : 256 word) = pad` by simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `lookup_var padvar z4 = SOME (n2w pad)` by simp[Abbr `pad`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z4` by
    (open_owned `OS c4 z4 G4 T4` >> strip_tac >> irule owned_decoder_allocas_below_fmp >>
     qexistsl_tac [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ z4 /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `local_ptrs_reserved ce c4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sg` >> asm_rewrite_tac[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sg` >> simp[]) >>
  Q.SUBGOAL_THEN
    `output_base <= w2n (n2w pad : 256 word) /\
     w2n (n2w pad : 256 word)+32 <= output_base+output_cap /\
     w2n (n2w pad : 256 word)+32 <= z4.vs_alloca_next /\
     (w2n input_word + LENGTH input_bytes <= w2n (n2w pad : 256 word) \/
      w2n (n2w pad : 256 word)+32 <= w2n input_word)`
    (map_every assume_tac o CONJUNCTS) >- decide_tac >>
  Q.SUBGOAL_THEN
    `EVERY (\(aid,p,b,k,bytes). b+k <= w2n (n2w pad : 256 word) \/
       w2n (n2w pad : 256 word)+32 <= b) live /\
     EVERY (\(b,bytes). b+LENGTH bytes <= w2n (n2w pad : 256 word) \/
       w2n (n2w pad : 256 word)+32 <= b) protected`
    (map_every assume_tac o CONJUNCTS) >-
    (conj_tac >-
      (simp[NoAsms,EVERY_MEM,FORALL_PROD] >> rpt gen_tac >> disch_tac >>
       qpat_assum `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ _) live`
         (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM,FORALL_PROD]) >>
       disch_then drule >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
     simp[NoAsms,EVERY_MEM,FORALL_PROD] >> rpt gen_tac >> disch_tac >>
     qpat_assum `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ _) protected`
       (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM,FORALL_PROD]) >>
     disch_then drule >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  apply_phase "store" [`sa` |-> `c4`, `sb` |-> `c5`, `s` |-> `z4`,
    `G` |-> `G4`, `tn` |-> `T4`, `dst` |-> `padvar`, `dw` |-> `n2w pad`] >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choose_then `z5` (qx_choose_then `G5` (qx_choose_then `T5`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "scalar"
QED

Resume bytes_tail_finite_if_phases[scalar]:
  `z4.vs_labels = y.vs_labels /\ z5.vs_labels = z4.vs_labels` by
    (conj_tac >- (qpat_assum `!obs. fn_has_code sg c4 obs ==> _`
       (qspec_then `fn` (drule_then (mp_tac o MATCH_MP gas_path_labels))) >> simp[]) >>
     qpat_assum `!obs. fn_has_code c4 c5 obs ==> _`
       (qspec_then `fn` (drule_then (mp_tac o MATCH_MP gas_path_labels))) >> simp[]) >>
  `abi_decoder_operand_live c4.cs_next_var cnt /\
   abi_decoder_operand_live c5.cs_next_var cnt` by
    (qpat_assum `abi_decoder_operand_live sg.cs_next_var cnt` mp_tac >>
     qpat_assum `sg.cs_next_var <= c4.cs_next_var` mp_tac >>
     qpat_assum `c4.cs_next_var <= c5.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
  `eval_operand cnt z4 = SOME (n2w c) /\ op_prov G4 cnt = NONE /\ op_taint T4 cnt = {}` by
    (qpat_assum `!x. not_fresh_at sg x ==> lookup_var x z4 = _ /\ _`
      (mp_then Any mp_tac tail_frame_operand) >>
     disch_then (qspec_then `cnt` mp_tac) >> simp[]) >>
  `eval_operand cnt z5 = SOME (n2w c) /\ op_prov G5 cnt = NONE /\ op_taint T5 cnt = {}` by
    (qpat_assum `!x. not_fresh_at c4 x ==> lookup_var x z5 = _ /\ _`
      (mp_then Any mp_tac tail_frame_operand) >>
     disch_then (qspec_then `cnt` mp_tac) >> simp[]) >>
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
    (irule bop_scalar_seq_emit_op >> conj_tac >- simp[] >>
     qexistsl_tac [`ADD`,`[Lit 32w;cnt]`] >> simp[]) >>
  `!op. op IN {Lit 32w;cnt} ==> op_prov G5 op = NONE /\ op_taint T5 op = {}` by
    (qpat_assum `op_prov G5 cnt = NONE` mp_tac >>
     qpat_assum `op_taint T5 cnt = {}` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[] >> rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts c5 c6)` by
    (qpat_assum `emit_op ADD [Lit 32w;cnt] c5 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  `sg.cs_next_var <= c5.cs_next_var /\ sg.cs_next_var <= c6.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce c5 /\ not_fresh_at c5 input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x)` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sg` >> simp[]) >>
     rpt conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sg` >> simp[]) >>
  `allocas_from lo z5 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z5)` by
    (open_owned `OS c5 z5 G5 T5` >>
     qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
       qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ z5 /\ _`
         (strip_assume_tac o (fn th => MATCH_MP th vh)))) >>
     conj_tac >- fs[ghost_inv_at_def] >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  apply_phase "scalar" [`sa` |-> `c5`, `sb` |-> `c6`, `s` |-> `z5`,
    `G` |-> `G5`, `tn` |-> `T5`, `t` |-> `raw6`,
    `A` |-> `{Lit 32w;cnt}`, `B` |-> `copysz INSERT {Lit 32w;cnt}`] >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choose_then `z6` (qx_choose_then `G6` (qx_choose_then `T6`
    (map_every assume_tac o CONJUNCTS)))) >>
  `eval_operand copysz z6 = SOME (n2w (32+c))` by
    (qpat_assum `z6 = _` SUBST1_TAC >> simp[eval_operand_inst_idx]) >>
  `op_taint T6 copysz = {}` by
    (qpat_assum `!op. op IN _ ==> op_prov G6 op = _ /\ _`
       (qspec_then `copysz` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live c6.cs_next_var copysz` by
    (qpat_assum `emit_op ADD _ c5 = _`
       (mp_then Any ACCEPT_TAC abi_decoder_operand_live_emit)) >>
  suspend "copy"
QED

Resume bytes_tail_finite_if_phases[copy]:
  `!x. not_fresh_at sg x ==> lookup_var x z6 = lookup_var x y /\
     FLOOKUP G6 x = FLOOKUP Gy x /\ op_taint T6 (Var x) = op_taint Ty (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at c4 x /\ not_fresh_at c5 x` by
       (conj_tac >> irule not_fresh_at_mono >> qexists_tac `sg` >> simp[]) >>
     map_every (fn pat => qpat_assum pat (qspec_then `x` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at sg x ==> lookup_var x z4 = _ /\ _`,
        `!x. not_fresh_at c4 x ==> lookup_var x z5 = _ /\ _`,
        `!x. not_fresh_at c5 x ==> lookup_var x z6 = _ /\ _`] >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved ce c6 /\ not_fresh_at c6 input /\ not_fresh_at c6 dstv /\
   not_fresh_at c6 ar /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x)` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sg` >> simp[]) >>
     rpt conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sg` >> simp[]) >>
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
    (open_owned `OS c6 z6 G6 T6` >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     `alloca_inv z6` by
       (qpat_assum `?H. V H` (qx_choose_then `horizon` (fn vh =>
          qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ z6 /\ _`
            (assume_tac o CONJUNCT1 o (fn th => MATCH_MP th vh)))) >>
        drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     irule alloca_site_registered_below >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `output_id` >> first_assum ACCEPT_TAC) >>
  `c <= 32*((n+31) DIV 32)` by
    (qpat_assum `c <= n` mp_tac >> rpt (pop_assum kall_tac) >>
     mp_tac (arithmeticTheory.DIVISION |> Q.SPEC `32`) >>
     rewrite_tac [DECIDE ``0 < 32``] >>
     disch_then (qspec_then `n+31` strip_assume_tac) >> strip_tac >> decide_tac) >>
  `32+c <= type_memory_size tv` by decide_tac >>
  Q.SUBGOAL_THEN
    `w2n input_word+off < dimword (:256) /\ d < dimword (:256) /\
     32+c < dimword (:256) /\ d+(32+c) <= output_base+output_cap /\
     d+(32+c) <= z6.vs_alloca_next /\ (w2n input_word+off)+(32+c) <= z6.vs_alloca_next /\
     (w2n input_word+LENGTH input_bytes <= d \/ d+(32+c) <= w2n input_word)`
    (map_every assume_tac o CONJUNCTS) >- decide_tac >>
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
    `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+(32+c) <= b) live /\
     EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+(32+c) <= b) protected`
    (map_every assume_tac o CONJUNCTS) >-
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY (\(aid,p,b,k,bytes). b+k <= d \/ _) live`,
        `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+type_memory_size tv <= b) protected`,
        `32+c <= type_memory_size tv`] >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM,FORALL_PROD] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  apply_phase "copy" [`sa` |-> `c6`, `sb` |-> `fin`, `s` |-> `z6`,
    `G` |-> `G6`, `tn` |-> `T6`, `src` |-> `ar`, `dst` |-> `dstv`,
    `a` |-> `w2n input_word+off`, `b` |-> `d`, `n` |-> `32+c`,
    `count_op` |-> `copysz`] >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choose_then `zf` (qx_choose_then `Gf` (qx_choose_then `Tf`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "join"
QED

Resume bytes_tail_finite_if_phases[join]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (y,Gy,Ty) [] (OK zf,Gf,Tf)` by
    (gen_tac >>
     map_every (fn ws => irule gas_origin_ptr_path_trans >> qexistsl_tac ws >>
       (conj_tac >- first_assum MATCH_ACCEPT_TAC))
       [[`G4`,`z4`,`T4`],[`G5`,`z5`,`T5`],[`G6`,`z6`,`T6`]] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `!obs. fn_has_code sg fin obs ==> gas_path ctx obs y 0 (OK zf)` by
    (qx_gen_tac `obs` >> disch_tac >>
     map_every (fn args => qspecl_then args mp_tac fn_has_code_split >>
       (impl_tac >- asm_rewrite_tac[]) >> strip_tac)
       [[`sg`,`c4`,`fin`,`obs`],[`c4`,`c5`,`fin`,`obs`],[`c5`,`c6`,`fin`,`obs`]] >>
     map_every (fn pat => qpat_assum pat (qspec_then `obs` (drule_then assume_tac)))
       [`!obs. fn_has_code sg c4 obs ==> _`, `!obs. fn_has_code c4 c5 obs ==> _`,
        `!obs. fn_has_code c5 c6 obs ==> _`, `!obs. fn_has_code c6 fin obs ==> _`] >>
     map_every (fn mid =>
       irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
       qexists_tac mid >> (conj_tac >- first_assum ACCEPT_TAC))
       [`z4`,`z5`,`z6`] >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sg x ==> lookup_var x zf = lookup_var x y /\
       FLOOKUP Gf x = FLOOKUP Gy x /\ op_taint Tf (Var x) = op_taint Ty (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at c6 x` by (irule not_fresh_at_mono >> qexists_tac `sg` >> simp[]) >>
     map_every (fn pat => qpat_assum pat (qspec_then `x` (drule_then strip_assume_tac)))
       [`!x. not_fresh_at sg x ==> lookup_var x z6 = _ /\ _`,
        `!x. not_fresh_at c6 x ==> lookup_var x zf = _ /\ _`] >> asm_rewrite_tac[]) >>
  `!aid b. FLOOKUP y.vs_allocas aid = SOME b ==> FLOOKUP zf.vs_allocas aid = SOME b` by
    (qpat_assum `!D. gas_origin_ptr_path _ (y,Gy,Ty) [] (OK zf,Gf,Tf)`
       (qspec_then `DF (@H. V H)` (mp_tac o CONJUNCT2 o
         MATCH_MP gas_origin_ptr_path_projections)) >>
     disch_then (qspec_then `zf` mp_tac o MATCH_MP gas_path_ptr_old_allocations) >>
     simp[NoAsms]) >>
  `IO zf` by
    (qpat_assum `Abbrev (IO = _)` (fn th =>
       qpat_assum `IO y` (mp_tac o BETA_RULE o PURE_REWRITE_RULE
         [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th] >> BETA_TAC) >>
     disch_tac >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`y`,`sg`] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
     FIRST [qx_gen_tac `x` >> disch_tac >>
       qpat_assum `!x. not_fresh_at sg x ==> lookup_var x zf = _ /\ _`
         (qspec_then `x` (drule_then (ACCEPT_TAC o CONJUNCT1))),
       rpt strip_tac >> qpat_assum `!aid b. FLOOKUP y.vs_allocas aid = SOME b ==> _`
         irule >> first_assum ACCEPT_TAC]) >>
  suspend "in_memory"
QED

Resume bytes_tail_finite_if_phases[in_memory]:
  `Tf.t_mem SUBSET Ty.t_mem /\
   (!i. d <= i /\ i < d+(32+c) ==> i NOTIN Tf.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Tf.t_mem = _`, `T6.t_mem = _`, `T5.t_mem SUBSET T4.t_mem`, `T4.t_mem = _`] >>
     rpt (pop_assum kall_tac) >> simp[SUBSET_DEF,IN_DIFF] >> metis_tac[]) >>
  `mem_bytes_at (w2n input_word) (LENGTH input_bytes) z6.vs_memory =
   mem_bytes_at (w2n input_word) (LENGTH input_bytes) y.vs_memory` by
    (open_owned `OS c6 z6 G6 T6` >> open_owned `OS sg y Gy Ty` >> asm_rewrite_tac[]) >>
  `mem_word_at (w2n input_word+off) z6.vs_memory =
   mem_word_at (w2n input_word+off) y.vs_memory` by
    (irule (cj 1 (Q.INST [`c` |-> `0`] abi_decode_bytestring_copy_views)) >>
     rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
     `off+32 <= LENGTH input_bytes` by decide_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`off+32 <= LENGTH input_bytes`,
        `mem_bytes_at (w2n input_word) _ z6.vs_memory = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     map_every (fn mem =>
       qspecl_then [`w2n input_word`,`off`,`32`,`LENGTH input_bytes`,mem]
          (drule_then assume_tac) mem_bytes_at_window)
       [`y.vs_memory`,`z6.vs_memory`] >> metis_tac[]) >>
  `mem_word_at d zf.vs_memory = n2w c` by
    (`mem_word_at (w2n input_word+off) z6.vs_memory = n2w c` by
       (qpat_assum `mem_word_at _ z6.vs_memory = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `mem_word_at (w2n input_word+off) z6.vs_memory = n2w c`
       (mp_tac o REWRITE_RULE [mem_word_at_eq_mload]) >>
     qpat_assum `zf = _` SUBST1_TAC >>
     simp[mem_word_at_eq_mload,abiEncoderPathPropsTheory.mload_inst_idx,
          stmtReasonMemoryTheory.mload_mcopy_same]) >>
  `!v. value_has_type tv v /\ val_in_memory tv v d zf.vs_memory ==>
       val_footprint tv v = 32+c` by
    (`n < dimword (:256) /\ c < dimword (:256)` by decide_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
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
     `LENGTH payload < dimword (:256)` by decide_tac >> gvs[arithmeticTheory.LESS_MOD]) >>
  `!v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d zf.vs_memory ==>
       !mem. mem_agree_outside Tf.t_mem zf.vs_memory mem ==> val_in_memory tv v d mem` by
    (qx_gen_tac `vv` >> strip_tac >>
     `val_footprint tv vv = 32+c` by (first_x_assum irule >> asm_rewrite_tac[]) >>
     gen_tac >> disch_tac >> irule val_in_memory_clean_footprint_ptr >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Tf.t_mem`,`zf.vs_memory`] >>
     conj_tac >-
       (qpat_assum `val_footprint tv vv = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`zf`,`Gf`,`Tf`] >>
  ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `Tf.t_mem SUBSET Ty.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `LENGTH c4.cs_current_insts <= LENGTH fin.cs_current_insts /\
   LENGTH c5.cs_current_insts <= LENGTH fin.cs_current_insts` by decide_tac >>
  gen_tac >>
  map_every (fn (b,q) => irule tail_finite_then >> qexistsl_tac [b,q] >>
    ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum MATCH_ACCEPT_TAC))
    [(`c4`,`(z4,G4,T4)`),(`c5`,`(z5,G5,T5)`),(`c6`,`(z6,G6,T6)`)] >>
  first_assum MATCH_ACCEPT_TAC
QED

Finalise bytes_tail_finite_if_phases
