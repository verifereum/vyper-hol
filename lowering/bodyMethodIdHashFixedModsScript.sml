(* A fixed-bytes hash writes only its registered scratch word. *)
Theory bodyMethodIdHashFixedMods
Ancestors
  bodyFullAllocGeneric bodyFullHashCleanFrame bodyPtrHashBuiltinsCursor
  assignTuplePtrAlloc allocaFootprint bodyMemBiMethodIdSuffix abiBuiltinAllocation
  wordLoadStorePtr instSeqPtrLo bodyPtrIfExpAllocCompiler ghostPcTransportPtr
  venomMemProps valueEncodingProps revertReasonPrefixFramePtr
  stateRelProj bodyMemBiMethodIdEndpoint bodyFullHashKeccakFixed bodyFullGhostFrame
  bodyFullUnwrapSlotPost exprSimHash exprOperandVar exprSimAlloc fragGasSeqPtr
  allocaHistoryFragment bodyPtrHashBuiltinsKeccakFixedRun
  bodyPtrHashBuiltinsKeccak bodyPtrHashBuiltinsAllocFrame
  instIdxIndep memSafeRun ptrDiscipline venomMemDefs loweringPosts fragExecMem
  contextCodegenRel memLocDefs bodyPtrDefs exprSimDefs exprSimProps
  exprSimHypsDefs exprLoweringProps builtinHashing compileEnv loweringStateRelDefs
  vyperStorageTrace venomState venomInst venomExecSemantics finite_map list rich_list
  words vyperStorageFootprint arithmetic fragExec pred_set context emitHelperProps
  bodyFullHashAllocFrame loweringHalt bodyPtrPrecompileBuiltinsAllocationFrame
  bodyMemoryDefs

Theorem hash_fixed_scratch_memory[local]:
  FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id = SOME (b,32) /\
  b + 32 < dimword (:256) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  eval_operand x a = SOME w /\ op_taint ta x = {} /\
  a = update_var p (n2w b) (abi_builtin_allocate_state id 32 s) /\
  j = mk_inst jid MSTORE [Var p;x] [] /\
  k = mk_inst kid SHA3 [Var p;Lit (n2w m)] [q] /\
  t = mstore b w a /\ u = update_var q h t /\
  ta = step_taint (mk_inst id ALLOCA [Lit 32w] [p]) s a tn /\
  tz = step_taint k t u (step_taint j a t ta) ==>
  FLOOKUP u.vs_allocas id = SOME (b,32) /\ lo <= b /\
  u.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
     FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off) /\
  (!off sz. off + sz <= b \/ b + 32 <= off ==>
     mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory) /\
  tz.t_mem SUBSET tn.t_mem /\ tz.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32}
Proof
  strip_tac >>
  `a.vs_memory = s.vs_memory /\ a.vs_data_section = s.vs_data_section /\
   s.vs_alloca_next <= a.vs_alloca_next` by
    simp[update_var_def, abi_builtin_allocate_state_def, COND_RAND] >>
  `FLOOKUP a.vs_allocas id = SOME (b,32)` by gvs[update_var_def] >>
  `lo <= b` by
    (qpat_assum `FLOOKUP (abi_builtin_allocate_state _ _ _).vs_allocas _ = _` mp_tac >>
     simp[alloca_site_cases] >> strip_tac >> fs[allocas_from_def] >> metis_tac[]) >>
  `!aid off sz. FLOOKUP a.vs_allocas aid = SOME (off,sz) ==>
     FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off` by
    (rpt gen_tac >> simp[update_var_def, abi_builtin_allocate_state_def, COND_RAND] >>
     rw[FLOOKUP_UPDATE] >> Cases_on `id = aid` >> gvs[]) >>
  `lookup_var p a = SOME (n2w b)` by simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `32 < dimword (:256) /\ b < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK a` by
    (drule (Q.INST [`n` |-> `32`] step_alloca_site) >> simp[]) >>
  `ta.t_mem SUBSET tn.t_mem UNION {i | b <= i /\ i < b+32}` by
    (drule_all (SRULE [] (Q.INST [`n` |-> `32`] alloca_step_memory_taint_bound)) >> simp[]) >>
  `tz.t_mem = ta.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`ARB`, `ARB`, `jid`] strip_assume_tac) >>
     gvs[MOD_LESS, hash_sha3_ghost]) >>
  `tn.t_mem SUBSET ta.t_mem` by
    simp[alloca_ghost_frames, SUBSET_DEF] >>
  `tz.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (qpat_x_assum `tz.t_mem = _` SUBST1_TAC >>
     simp[EXTENSION] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  `tz.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF] >>
  `u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
   u.vs_data_section = a.vs_data_section` by gvs[update_var_def, mstore_def] >>
  `LENGTH a.vs_memory <= LENGTH u.vs_memory` by
    (qspecl_then [`b`, `w`, `a`] mp_tac mstore_memory_nondecreasing >>
     simp[update_var_def]) >>
  `!off sz. off + sz <= b \/ b + 32 <= off ==>
      mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz a.vs_memory` by
    (rpt gen_tac >>
     qspecl_then [`off`, `sz`, `b`, `w`, `a`] mp_tac mstore_mem_bytes_at_disjoint >>
     simp[update_var_def]) >>
  metis_tac[]
QED

(* The three instructions' canonical ghost updates do not depend on the
   dead mask or the floor used to certify the path. *)
Theorem hash_fixed_scratch_physical[local]:
  compile_keccak256_bytesm x m sm = (hash,sh) /\ m <= 32 /\
  eval_operand x s = SOME w /\ op_taint tn x = {} /\
  (!p. x = Var p ==> not_fresh_at sm p) /\
  fn_has_code sm sh func /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx mid s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sm sh) s = OK raw ==>
  ?Gh tnh b.
  (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sh) s Gh tnh) /\
  (!H:(bool # bytes32 # type_value) list # num list. !D.
     stmt_state_rel H ctx func cenv cx mid s /\
     ghost_inv_at D 0 d cenv cx mid G tn s ==>
     ghost_inv_at D 0 d cenv cx mid Gh tnh raw) /\
  op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
  (!p. not_fresh_at sm p ==>
     FLOOKUP Gh p = FLOOKUP G p /\ op_taint tnh (Var p) = op_taint tn (Var p)) /\
  (!p. not_fresh_at sm p ==> FLOOKUP tnh.t_var p = FLOOKUP tn.t_var p) /\
  MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func) /\
  FLOOKUP raw.vs_allocas sm.cs_next_id = SOME (b,32) /\ lo <= b /\
  raw.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH raw.vs_memory /\ s.vs_alloca_next <= raw.vs_alloca_next /\
  (!aid off sz. FLOOKUP raw.vs_allocas aid = SOME (off,sz) ==>
     FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off) /\
  (!off sz. off + sz <= b \/ b + 32 <= off ==>
     mem_bytes_at off sz raw.vs_memory = mem_bytes_at off sz s.vs_memory) /\
  tnh.t_mem SUBSET tn.t_mem /\ tnh.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32}
Proof
  strip_tac >>
  drule hash_fixed_keccak_emission >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `q = STRING #"%" (toString (sm.cs_next_var+1))` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]` >>
  qabbrev_tac `j = mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []` >>
  qabbrev_tac `k = mk_inst (sm.cs_next_id+2) SHA3 [Var p;Lit (n2w m)] [q]` >>
  `MEM i (fn_insts func)` by
    (simp[Abbr `i`, Abbr `p`] >>
     irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >>
     goal_assum (drule_at Any) >> simp[] >> qexistsl [`m`, `hash`, `x`] >> simp[]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)] [p]) (fn_insts func)` by
    fs[Abbr `i`] >>
  drule_all method_id_alloc_site_bound >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  qabbrev_tac `a = update_var p (n2w b) (abi_builtin_allocate_state sm.cs_next_id 32 s)` >>
  `step_inst_base i s = OK a` by
    (simp[Abbr `i`, Abbr `a`] >>
     drule (Q.INST [`n` |-> `32`] step_alloca_site) >> simp[]) >>
  `FLOOKUP a.vs_allocas sm.cs_next_id = SOME (b,32)` by simp[Abbr `a`, update_var_def] >>
  `!r. x = Var r ==> r <> p` by
    (rpt strip_tac >> gvs[Abbr `p`, not_fresh_at_def]) >>
  `lookup_var p a = SOME (n2w b)` by simp[Abbr `a`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qabbrev_tac `ta = step_taint i s a tn` >>
  `eval_operand x a = SOME w /\ op_taint ta x = {}` by
    (simp[Abbr `ta`, Abbr `i`] >> irule
       (SRULE [] (INST_TYPE [gamma |-> ``:256``] (Q.INST [`n` |-> `32`] hash_alloca_old_operand))) >>
     `x <> Var p` by metis_tac[] >> simp[] >>
     qexistsl [`H0`, `cenv`, `ctx`, `cx`, `mid`, `func`] >> simp[]) >>
  qabbrev_tac `t = mstore b w a` >>
  `step_inst_base j a = OK t` by
    (simp[Abbr `j`, Abbr `t`, Once step_inst_base_def,
          mk_inst_def, exec_write2_def, eval_operand_def, MOD_LESS] >> decide_tac) >>
  `step_inst_base k t = OK raw` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def] >>
     Cases_on `step_inst_base k t` >> simp[]) >>
  suspend "canonical"
QED

Resume hash_fixed_scratch_physical[canonical]:
  `?h. raw = update_var q h t` by
    (`step_inst_base k t = OK (update_var q (word_of_bytes T (0w:bytes32)
        (Keccak_256_w64 (mem_bytes_at (w2n (n2w b:bytes32))
          (w2n (n2w m:bytes32)) t.vs_memory))) t)`
       suffices_by (strip_tac >> qpat_x_assum `step_inst_base k t = OK raw` mp_tac >>
         simp[] >> metis_tac[]) >>
     simp[NoAsms, Abbr `k`] >> irule step_SHA3_bytes >>
     simp[eval_operand_def, Abbr `t`, lookup_var_def, mstore_def]) >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                      d_imm := K {}; d_ret := K {}|>` >>
  `?Gh tnh. inst_seq_ptr D0 0 ctx func PG G tn [i;j;k] s Gh tnh` by
    (simp[Abbr `i`, Abbr `j`, Abbr `k`] >>
     irule (INST_TYPE [alpha |-> ``:256``, gamma |-> ``:256``] hash_alloc_store_sha3_seq_ptr) >>
     fs[Abbr `ta`] >> qexistsl [`H0`, `cenv`, `cx`, `mid`] >> simp[]) >>
  `Gh = step_prov PG (step_prov PG (step_prov PG G i a) j t) k raw /\
   tnh = step_taint k t raw (step_taint j a t ta)` by
    (`~is_terminator j.inst_opcode /\ ~is_terminator k.inst_opcode` by
       simp[Abbr `j`, Abbr `k`, mk_inst_def, is_terminator_def] >>
     drule_all hash_inst_seq_triple_endpoint_raw >> fs[Abbr `ta`]) >>
  qexistsl [`Gh`, `tnh`, `b`] >>
  conj_tac >-
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[NoAsms] >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexists_tac `D0` >> gvs[Abbr `D0`]) >>
  conj_tac >- suspend "zero_ghost" >>
  suspend "effects"
QED

Resume hash_fixed_scratch_physical[zero_ghost]:
  rpt gen_tac >> strip_tac >>
  `?buf sc. compile_alloc_buffer 32 sm = (buf,sc) /\ fn_has_code sm sc func /\
     buf.buf_operand = Var p` by suspend "alloc_code" >>
  `stmt_state_rel H ctx func cenv cx mid a /\
   (!n b' sz. local_region cenv mid.scopes a n b' sz ==>
       regions_disjoint b 32 b' sz)` by suspend "alloc_rel" >>
  `ghost_kept_at 0 cenv mid sm G tn s (step_prov PG G i a) ta` by
    (fs[Abbr `i`, Abbr `ta`] >>
     irule (SRULE [] (INST_TYPE [alpha |-> ``:256``]
       (Q.SPECL [`H`, `ctx`, `func`] hash_compile_alloc_entry_kept_at))) >>
     simp[] >> goal_assum (drule_at Any)) >>
  `ghost_inv_at D 0 d cenv cx mid (step_prov PG G i a) ta a` by
    (fs[Abbr `i`, Abbr `ta`] >>
     irule (SRULE [] (Q.SPECL [`H`, `D`, `0`, `ctx`, `func`]
       compile_alloc_buffer_ghost_frame_at)) >>
     simp[] >> conj_tac >- (qexists_tac `sm` >> simp[]) >>
     qexistsl [`H`, `ctx`, `func`] >> simp[]) >>
  `!n b' sz z. local_region cenv mid.scopes a n b' sz /\
    b' <= z /\ z < b'+sz ==> ~(b <= z /\ z < b+32)` by
    (rpt strip_tac >> qpat_assum `!n b' sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `w2n (n2w b:bytes32) = b` by (simp[MOD_LESS] >> decide_tac) >>
  `!n b' sz z. local_region cenv mid.scopes a n b' sz /\
    b' <= z /\ z < b'+sz ==>
    ~(w2n (n2w b:bytes32) <= z /\ z < w2n (n2w b:bytes32)+32)` by metis_tac[] >>
  qunabbrev_tac `j` >> qunabbrev_tac `t` >>
  `ghost_inv_at D 0 d cenv cx mid
     (step_prov PG (step_prov PG G i a) (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] [])
       (mstore (w2n (n2w b:bytes32)) w a))
     (step_taint (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) a
       (mstore (w2n (n2w b:bytes32)) w a) ta)
     (mstore (w2n (n2w b:bytes32)) w a) /\
   ghost_kept_at 0 cenv mid sm G tn s
     (step_prov PG (step_prov PG G i a) (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] [])
       (mstore (w2n (n2w b:bytes32)) w a))
     (step_taint (mk_inst (sm.cs_next_id+1) MSTORE [Var p;x] []) a
       (mstore (w2n (n2w b:bytes32)) w a) ta)` by
    (irule (INST_TYPE [alpha |-> ``:256``] hash_clean_mstore_frame_at) >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl [`H`, `ctx`, `func`] >> simp[]) >>
  fs[] >>
  `~not_fresh_at sm q` by simp[Abbr `q`, not_fresh_at_def] >>
  qunabbrev_tac `k` >>
  drule_all hash_sha3_fresh_frame_at >>
  disch_then (qspecl_then [`h`, `PG`, `sm.cs_next_id+2`, `Var p`, `Lit (n2w m)`]
    strip_assume_tac) >> gvs[]
QED

Resume hash_fixed_scratch_physical[alloc_code]:
  `?buf sc. compile_alloc_buffer 32 sm = (buf,sc)` by metis_tac[pairTheory.PAIR] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qexistsl [`buf`, `sc`] >> simp[Abbr `p`] >>
  `cs_extends sm sc` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sc sh` by
    (mp_tac cs_appends_emit_helpers >> simp[cs_appends_def] >> strip_tac >>
     qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
     simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> Cases_on `_0` >>
     metis_tac[cs_extends_trans]) >>
  metis_tac[fn_has_code_split]
QED

Resume hash_fixed_scratch_physical[alloc_rel]:
  fs[Abbr `i`, Abbr `p`] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx mid s` (mp_then Any mp_tac
    literal_alloc_buffer_run) >>
  disch_then (fn th => qpat_assum `compile_alloc_buffer 32 sm = _`
    (mp_then Any mp_tac th)) >>
  simp[] >> strip_tac >>
  drule emitted_allocation_singleton >> strip_tac >>
  `run_inst_seq (emitted_insts sm sc) s = OK a` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sc) _ = _` kall_tac >>
     simp[run_inst_seq_def]) >>
  gvs[MOD_LESS] >> metis_tac[]
QED

Resume hash_fixed_scratch_physical[effects]:
  `~not_fresh_at sm q` by simp[Abbr `q`, not_fresh_at_def] >>
  `~not_fresh_at sm p` by simp[Abbr `p`, not_fresh_at_def] >>
  `op_taint tnh hash = {} /\ op_prov Gh hash = NONE` by
    gvs[Abbr `k`, hash_sha3_ghost, op_taint_def, op_prov_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `r` >> disch_tac >>
     drule revertReasonPrefixFramePtrTheory.inst_seq_ptr_other_output_frame >>
     disch_then (qspec_then `r` mp_tac) >>
     gvs[Abbr `i`, Abbr `j`, Abbr `k`, mk_inst_def] >> metis_tac[]) >>
  conj_tac >- suspend "var_map" >>
  conj_tac >- simp[Abbr `i`, Abbr `p`] >>
  irule hash_fixed_scratch_memory >>
  simp[] >>
  qexistsl_tac [`h`, `sm.cs_next_id + 1`, `sm.cs_next_id + 2`, `m`, `p`, `q`, `w`, `x`] >>
  simp[Abbr `i`, Abbr `j`, Abbr `k`, Abbr `t`, Abbr `a`] >>
  fs[Abbr `t`, Abbr `a`]
QED
Resume hash_fixed_scratch_physical[var_map]:
  qx_gen_tac `r` >> disch_tac >>
  `r <> p /\ r <> q` by metis_tac[] >>
  `FLOOKUP (step_taint j a t ta).t_var r = FLOOKUP ta.t_var r` by
    simp[Abbr `j`, step_taint_def, mk_inst_def, set_var_taint_def, FLOOKUP_DRESTRICT] >>
  simp[Abbr `k`, hash_sha3_ghost, FLOOKUP_UPDATE] >>
  simp[Abbr `ta`, Abbr `i`, step_taint_def, mk_inst_def, set_var_taint_def, FLOOKUP_UPDATE]
QED
Finalise hash_fixed_scratch_physical

Theorem method_id_hash_fixed_scratch_run:
 !DF lo d explicit ctx func PG cenv cx e es sa sm sh s0 st0 mid v x s G tn hash bty.
 expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
 ~is_bytestring_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
 value_has_type (BaseTV bty) v /\
 lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
 compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
 fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
 return_buf_frame d cenv sm s /\
 MAP FDOM es.scopes = MAP FDOM mid.scopes /\
 storage_trace_domain cx st0 mid.storage_trace /\
 ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
 s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
   ghost_inv_at (DF H) 0 d cenv cx mid G tn s /\
   ptr_val_ok cx (post_value_type cenv e) v x G tn s)
 ==>
 ?bs t u Gh tnh b.
 LENGTH bs = 32 /\
 (!ann. builtin_result cx mid.accounts ann MethodId [expr_type e] [v] =
   INL (BytesV (TAKE 4 bs))) /\
 run_inst_seq (emitted_insts sm sh) s = OK t /\
 u = (t with vs_inst_idx := LENGTH sh.cs_current_insts) /\
 eval_operand hash u = SOME
   (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
 op_taint tnh hash = {} /\ op_prov Gh hash = NONE /\
 ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
 u.vs_inst_idx = LENGTH sh.cs_current_insts /\ alloca_history func u /\
 local_ptrs_reserved cenv sh /\ return_buf_frame d cenv sh u /\
 sm.cs_next_var <= sh.cs_next_var /\ sm.cs_next_id <= sh.cs_next_id /\
 (!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s /\
   FLOOKUP Gh p = FLOOKUP G p /\ op_taint tnh (Var p) = op_taint tn (Var p)) /\
 (!p. not_fresh_at sm p ==> FLOOKUP tnh.t_var p = FLOOKUP tn.t_var p) /\
 (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
   FLOOKUP u.vs_allocas aid = SOME (a,len) /\
   (aid < sm.cs_next_id ==>
     mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory)) /\
 locals_kept cenv mid mid s u /\ pure_frame cenv func mid sm s u /\
 MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func) /\
 FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,32) /\ lo <= b /\
 u.vs_data_section = s.vs_data_section /\
 LENGTH s.vs_memory <= LENGTH u.vs_memory /\ s.vs_alloca_next <= u.vs_alloca_next /\
 (!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off) /\
 (!off sz. off + sz <= b \/ b + 32 <= off ==>
    mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory) /\
 tnh.t_mem SUBSET tn.t_mem /\ tnh.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK u,Gh,tnh) /\
   stmt_state_rel H ctx func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) 0 d cenv cx mid Gh tnh u)
Proof
 rpt gen_tac >> strip_tac >>
 qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
 `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 drule_all method_id_hash_typed_post_run >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts sm sh) s = OK raw` >>
 `?m payload. bty = BytesT (Fixed m) /\ v = BytesV payload /\ m <= 32` by
   (Cases_on `bty` >>
    gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >>
    gvs[vyperTypeSystemTheory.is_bytes_or_string_type_def, is_bytestring_type_def] >>
    Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
 gvs[] >>
 `compile_keccak256_bytesm x m sm = (hash,sh)` by
   gvs[compile_method_id_hash_def, is_bytestring_type_def] >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 `?w. eval_operand x s = SOME w /\ LENGTH payload = m /\
      TAKE (LENGTH payload) (word_to_bytes_be w) = payload` by
   (drule_at (Pos hd) hash_fixed_post_view >> simp[]) >>
 `!p. x = Var p ==> not_fresh_at sm p` by
   (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
 `stmt_state_rel H0 ctx func cenv cx mid s` by fs[expr_post_def] >>
 `op_taint tn x = {}` by fs[ptr_val_ok_def, post_value_type_def, is_word_type_def] >>
 drule_all hash_fixed_scratch_physical >>
 disch_then (qspecl_then [`d`, `PG`, `G`] strip_assume_tac) >>
 suspend "finish"
QED
Resume method_id_hash_fixed_scratch_run[finish]:
 `same_blocks sm sh /\
  sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sh)` by (irule keccak_suffix_shape >> metis_tac[]) >>
 `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sh ++ rest` by
   (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
    metis_tac[APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
 `run_inst_seq_mem_ok (emitted_insts sm sh) s` by
   (irule (INST_TYPE [alpha |-> ``:256``] method_id_fixed_hash_mem_ok_any_block) >>
    conj_tac >- (qexistsl [`m`, `hash`, `x`, `w`] >> simp[]) >>
    qexistsl [`H0`, `cenv`, `ctx`, `cx`, `mid`, `func`] >> simp[]) >>
 `isPREFIX (emitted_insts sm sh) (DROP s.vs_inst_idx bb.bb_instructions)` by
   simp[IS_PREFIX_APPEND] >>
 `compile_keccak256_bytesm x (LENGTH payload) sm = (hash,sh)` by simp[] >>
 `LENGTH payload <= 32` by simp[] >>
 `!HH:(bool # bytes32 # type_value) list # num list.
   stmt_state_rel HH ctx func cenv cx mid s ==>
   stmt_state_rel HH ctx func cenv cx mid raw /\
   (!p. not_fresh_at sm p ==> lookup_var p raw = lookup_var p s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP raw.vs_allocas aid = SOME entry) /\
   (!aid a len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        mem_bytes_at a len raw.vs_memory = mem_bytes_at a len s.vs_memory) /\
   (!n a len. local_region cenv mid.scopes s n a len ==>
        mem_bytes_at a len raw.vs_memory = mem_bytes_at a len s.vs_memory) /\
   pure_frame cenv func mid sm s raw` by suspend "ordinary" >>
 pop_assum (fn th => assume_tac th >> qspec_then `H0` mp_tac th) >>
 (impl_tac >- simp[]) >> strip_tac >>
 suspend "package"
QED

Resume method_id_hash_fixed_scratch_run[ordinary]:
 gen_tac >> disch_tac >>
 qpat_assum `stmt_state_rel HH _ _ _ _ _ s`
   (mp_then Any mp_tac (INST_TYPE [alpha |-> ``:256``] compile_keccak256_bytesm_frame)) >>
 disch_then (fn th => qpat_assum `compile_keccak256_bytesm x (LENGTH payload) sm = _`
   (mp_then Any mp_tac th)) >>
 disch_then (qspec_then `w` mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Resume method_id_hash_fixed_scratch_run[package]:
 `~raw.vs_halted` by (drule_all fragExecTheory.run_inst_seq_preserves_halted >> simp[]) >>
 `raw.vs_current_bb = s.vs_current_bb` by
   (drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[]) >>
 drule method_id_hash_grows >> strip_tac >>
 `local_ptrs_reserved cenv sh` by
   (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
 qabbrev_tac `fin = raw with vs_inst_idx := LENGTH sh.cs_current_insts` >>
 `alloca_history func fin` by suspend "history" >>
 `return_buf_frame d cenv sh fin` by suspend "return" >>
 `locals_kept cenv mid mid s raw` by
   (irule locals_kept_regions >> fs[pure_frame_def]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK fin,Gh,tnh) /\
   stmt_state_rel H ctx func cenv cx mid fin /\ storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) 0 d cenv cx mid Gh tnh fin` by suspend "post" >>
 qexistsl [`bs`, `Gh`, `tnh`, `b`] >>
 suspend "conclude"
QED

Resume method_id_hash_fixed_scratch_run[history]:
 `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
 simp[NoAsms, Abbr `fin`] >>
 irule bodyFullUnwrapRunTheory.emitted_alloca_history >> simp[] >>
 qexistsl [`emitted_insts sm sh`, `s`, `sm`] >>
 fs[same_blocks_def, EVERY_MEM]
QED

Resume method_id_hash_fixed_scratch_run[return]:
 irule return_buf_frame_frame >>
 qexistsl [`cenv`, `s`, `sm`] >>
 simp[Abbr `fin`, lookup_var_def] >> rpt strip_tac >>
 qpat_x_assum `!p. not_fresh_at sm p ==> lookup_var _ _ = _` drule >>
 simp[lookup_var_def]
QED

Resume method_id_hash_fixed_scratch_run[post]:
 gen_tac >> disch_tac >>
 conj_tac >- suspend "path" >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
 (impl_tac >- simp[]) >> strip_tac >>
 `stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H)` by
   fs[expr_post_def] >>
 qpat_assum `!HH. stmt_state_rel HH _ _ _ _ _ _ ==> _` drule >> strip_tac >>
 qpat_assum `!HH D. stmt_state_rel HH _ _ _ _ _ _ /\ _ ==> _` drule_all >>
 simp[Abbr `fin`, stmt_state_rel_inst_idx, ghost_inv_at_inst_idx]
QED

Resume method_id_hash_fixed_scratch_run[path]:
 `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sh) = [] /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sh)` by
   (drule hash_fixed_keccak_emission >> simp[mk_inst_def]) >>
 `(ctx_has_dalloca ctx ==>
   !pre i post u. emitted_insts sm sh = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
   (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
    fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
 qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
   (qspec_then `DF H` assume_tac) >>
 `LENGTH sh.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sm sh)` by simp[] >>
 drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `fin`]
QED

Resume method_id_hash_fixed_scratch_run[conclude]:
 simp[Abbr `fin`, ghostPcTransportPtrTheory.eval_operand_inst_idx, lookup_var_def] >>
 conj_tac >- fs[same_blocks_def] >>
 conj_tac >-
   (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> lookup_var x raw = _`
      (drule_then (ACCEPT_TAC o REWRITE_RULE [lookup_var_def]))) >>
 conj_tac >-
   (rpt strip_tac >> qpat_assum `!aid a len. aid < _ /\ _ ==> _` irule >>
    goal_assum (drule_at Any) >> simp[]) >>
 first_assum ACCEPT_TAC
QED
Finalise method_id_hash_fixed_scratch_run
