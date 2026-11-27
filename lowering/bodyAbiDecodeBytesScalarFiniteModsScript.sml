Theory bodyAbiDecodeBytesScalarFiniteMods
Ancestors
  bodyFullAbiDecodeGuardReadObserved bodyFullAbiDecodeRelativeLoadExact[qualified]
  bodyFullAbiDecodeClampMemory[qualified] bodyFullAbiDecodeFiniteObserved
  bodyPtrBopScalarSeq[qualified] bodyPtrBopScalarOutcome instSeqPtrLo[qualified]
  fragGasOriginPtrLoop[qualified] fragGasOriginPtrDead[qualified] fragGasOriginPtr
  ptrDiscipline unitTransformDefs compileEnv exprLoweringProps emitHelperProps
  stateFrame venomState venomExecSemantics venomInst fragExec fragExecMem
  freshWrites gasOriginPtrLabels pred_set finite_map list arithmetic

(* These are independent hypotheses, not imports of the slice-lift producer. *)
val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                  d_imm := K {}; d_ret := K {}|>``;

fun close_implicit tm =
  let val (qs,body) = strip_forall tm
  in list_mk_forall (qs @ free_vars_lr tm,body) end;

val emitted_lift = close_implicit ``
  fn_has_code sa sb fn /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn)
    (t with vs_inst_idx := LENGTH sb.cs_current_insts,G',tn')``;

val dead_lift = close_implicit ``
  !n x y.
    RELPOW (\(u,Gu,tu) (v,Gv,tv). gas_origin_ptr_edge
      (^no_dead,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv)) n x y ==>
    RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv)) n x y``;

val scalar_finite =
  let
    val old = concl (BETA_RULE abi_decode_bytes_scalar_frame_joint)
    val (pre,post) = dest_imp old
    val (ws,fields) = strip_exists post
    val (u,gf,tf) = case ws of [u,gf,tf] => (u,gf,tf)
      | _ => raise Fail "expected scalar result triple"
    fun arg name = valOf (List.find (fn v => fst (dest_var v) = name) (free_vars old))
    val sa = arg "sa" and sb = arg "sb" and s = arg "s"
    val ctx = arg "ctx" and lo = arg "lo" and explicit = arg "explicit"
    val fn_tm = arg "fn" and pg = arg "PG" and g = arg "G" and tn = arg "tn"
    val obs = ``!obs. fn_has_code ^sa ^sb obs ==> gas_path ^ctx obs ^s 0 (OK ^u)``
    val finite = ``!D. RELPOW (\(v,Gv,tv) (w,Gw,tw).
      gas_origin_ptr_edge (D,^lo,^explicit,^ctx,^fn_tm,^pg) (v,Gv,tv) [] (OK w,Gw,tw))
      (LENGTH ^sb.cs_current_insts - LENGTH ^sa.cs_current_insts) (^s,^g,^tn) (^u,^gf,^tf)``
    fun append_success tm =
      if is_conj tm then
        let val (p,q) = dest_conj tm in mk_conj (p,append_success q) end
      else list_mk_conj [tm,obs,finite]
  in close_implicit (mk_imp (pre,list_mk_exists (ws,append_success fields))) end;

Theorem bytes_scalar_frame_finite:
  ^emitted_lift ==> ^dead_lift ==> ^scalar_finite
Proof
  disch_then (mk_asm "emitted") >> disch_then (mk_asm "dead") >>
  rpt gen_tac >> strip_tac >>
  drule_all (bodyPtrBopScalarSeqTheory.bop_scalar_seq_run |>
    Q.INST [`D` |-> `^no_dead`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `inst_seq_ptr ^no_dead lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `^no_dead` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bodyFullAbiDecodeClampMemoryTheory.abi_decode_scalar_seq_mem_ok] >>
  `ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory` by
    (simp[Abbr `u`] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  suspend "scalar_owned"
QED

Resume bytes_scalar_frame_finite[scalar_owned]:
  `!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`, lookup_var_def, op_taint_def] >> gvs[]) >>
  `alloca_history fn s` by fs[] >>
  `alloca_history fn u` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[] >>
     gvs[inst_extends_def]) >>
  qexistsl_tac [`u`, `G'`, `tn'`] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     asm_rewrite_tac[]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (irule (BETA_RULE bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower) >>
     conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> conj_tac >- metis_tac[allocas_from_def] >>
  conj_tac >-
    (simp_tac bool_ss [Abbr `u`] >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
     fs[inst_extends_def, EVERY_CONJ, LENGTH_NIL, FILTER_EQ_NIL]) >>
  simp_tac bool_ss [Abbr `u`] >> gen_tac >>
  asm "dead" irule >> asm "emitted" irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >> fs[EVERY_CONJ]
QED

Finalise bytes_scalar_frame_finite
