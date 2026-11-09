(* Repeat-compatible navigation for the owned complex decoder fold. *)
Theory sourceOwnedComplexPtr
Ancestors sourceRecursiveComplexPtr sourceOwnedArrayConstructorPtr
  canonicalMemberTraversalPtr calldataScratchTuplePtr
  venomExecSemantics venomState abiDecoderMemberSetup abiDecoderContract
  decoderMemberPrefixPtr abiDecoderDynamicLoopSetup fragExec abiDecoderFrame
  exprLoweringProps bodyPtrDefs list abiDecoderMemberCode abiDecoderLoop compileEnv arithmetic finite_map

Theorem owned_member_navigation_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  eval_operand src s = SOME (n2w srcpos) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (srcpos + ao) : bytes32) s = n2w off /\
    srcpos + off < dimword (:256)) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\
  mid.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    abi_decode_sim ctx fn s r /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt limit r /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME (n2w (srcpos + if dyn then off else ao)) /\
    ptr_covers H u q r C /\ op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[] >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `frag_exec ctx sa mid (\s'. s' = s)
     (\r. r = t with vs_inst_idx := LENGTH mid.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >>
     fs[EVERY_CONJ] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `H`, `u`, `q`] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, lookup_var_def,
    ptr_covers_def, eval_operand_def] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  qpat_x_assum `!D. _` mp_tac >>
  qpat_x_assum `s with vs_inst_idx := _ = s` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD1, ADD_ASSOC, ADD_COMM]
QED

(* Interval composition is independent of decoder syntax.  P records the
   code-site certificate; the frontier bound is transported monotonically. *)
Theorem scratch_interval_chain:
  l <= m /\ m <= h /\ bnext <= cnext /\
  (!id p k. FLOOKUP a id = SOME (p,k) ==> FLOOKUP b id = SOME (p,k)) /\
  (!id p k. FLOOKUP b id = SOME (p,k) ==> FLOOKUP c id = SOME (p,k)) /\
  (!id. id < l \/ m <= id ==> FLOOKUP b id = FLOOKUP a id) /\
  (!id. id < m \/ h <= id ==> FLOOKUP c id = FLOOKUP b id) /\
  (!id p k. l <= id /\ id < m /\ FLOOKUP b id = SOME (p,k) ==>
    P id p k /\ p+k <= bnext) /\
  (!id p k. m <= id /\ id < h /\ FLOOKUP c id = SOME (p,k) ==>
    P id p k /\ p+k <= cnext) /\
  (!p k. MEM (p,k) fp ==> ?id. l <= id /\ id < m /\ FLOOKUP b id = SOME (p,k)) /\
  (!p k. MEM (p,k) gp ==> ?id. m <= id /\ id < h /\ FLOOKUP c id = SOME (p,k)) ==>
  (!id p k. FLOOKUP a id = SOME (p,k) ==> FLOOKUP c id = SOME (p,k)) /\
  (!id. id < l \/ h <= id ==> FLOOKUP c id = FLOOKUP a id) /\
  (!id p k. l <= id /\ id < h /\ FLOOKUP c id = SOME (p,k) ==>
    P id p k /\ p+k <= cnext) /\
  (!p k. MEM (p,k) (fp ++ gp) ==> ?id. l <= id /\ id < h /\ FLOOKUP c id = SOME (p,k))
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `id < m \/ h <= id` by decide_tac >>
      `id < l \/ m <= id` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `id < m`
      >- (`FLOOKUP b id = SOME (p,k)` by metis_tac[] >>
          `P id p k /\ p+k <= bnext` by metis_tac[] >>
          metis_tac[LESS_EQ_TRANS]) >>
      `m <= id` by decide_tac >> metis_tac[]) >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!p k. MEM (p,k) fp ==> _` drule >> strip_tac >>
      qexists_tac `id` >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `!p k. MEM (p,k) gp ==> _` drule >> strip_tac >>
  qexists_tac `id` >> metis_tac[LESS_EQ_TRANS]
QED
