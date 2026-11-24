(* Closed installed intervals for memory RawCall and ownership of its native visits. *)
Theory entryCreateRawCallMemoryNative
Ancestors
  entryCreateNativeFirstExit entryCreateReplayBind entryCreateEffectFocus
  entryCreateIntervalLayout entryCreateAdminSequence createSizeOperandCode
  exprSimRawCall exprSimAbiDecodeSiteCoverage exprSimAbiGasBridge exprLoweringProps
  createSizeCutRegion createSizeCutCode createSizePrefixReplay fragExec compileEnv emitHelperProps
  entryCreateBodyCut entryCreateFocusSpec entryCreateOperandReplay
  dftGasFromListTraceDefs relation fragGasPath vyperStorageTrace vyperState
  venomRunBounded entryCreatePathScope gasCount createExprSizeExitDefs
  fragGasOriginPtrExec fragGasOriginPtr vyperStorageFootprint vyperInterpreter
  venomExecSemantics
  venomInst list rich_list pair pred_set arithmetic

Theorem raw_call_memory_header_code[local]:
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (dp,s4) ==>
  create_cut_code {} s2 s4 /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s2 s4)
Proof
  strip_tac >>
  `create_cut_code {} s2 s3` by
    (`create_cut_code {} s2 (SND (emit_op MLOAD [data] s2))` by
       simp[create_cut_code_emit_op, create_cut_targets_def] >>
     qpat_x_assum `create_cut_code {} _ (SND _)` mp_tac >> simp[]) >>
  `create_cut_code {} s3 s4` by
    (`create_cut_code {} s3 (SND (emit_op ADD [data; Lit 32w] s3))` by
       simp[create_cut_code_emit_op, create_cut_targets_def] >>
     qpat_x_assum `create_cut_code {} _ (SND _)` mp_tac >> simp[]) >>
  conj_tac >- metis_tac[create_cut_code_join] >>
  `cs_extends s2 s3 /\ cs_extends s3 s4` by fs[create_cut_code_def] >>
  drule_all abi_decode_frag_code_compose >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  fs[same_blocks_def, frag_code_def, emitted_blocks_def, mk_inst_def,
     DROP_LENGTH_NIL, EVERY_MEM] >> rpt strip_tac >> gvs[]
QED

Theorem raw_call_memory_gas_code[local]:
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) ==>
  create_cut_code {} s5 s6 /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s5 s6)
Proof
  Cases_on `go`
  >- (simp[] >> strip_tac >> conj_tac
      >- (`create_cut_code {} s5 (SND (emit_op GAS [] s5))` by
            simp[create_cut_code_emit_op, create_cut_targets_def] >>
     qpat_x_assum `create_cut_code {} _ (SND _)` mp_tac >> simp[]) >>
      drule emitted_insts_emit_op >> drule emit_op_extends >>
      simp[same_blocks_def, frag_code_def, emitted_blocks_def, mk_inst_def,
           DROP_LENGTH_NIL]) >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem raw_call_memory_inventory_join[local]:
  cs_extends a m /\ cs_extends m b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a m) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code m b) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)
Proof
  simp[EVERY_MEM] >> strip_tac >> drule_all abi_decode_frag_code_compose >>
  simp[] >> metis_tac[]
QED

(* The recursive keyword compiler and the request producers supply just
   their own static intervals. No statement about their execution is needed. *)
Theorem raw_call_memory_installed_splits:
  lower_value compile_expr ce (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr ce (expr_type data_e) data_e s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (dp,s4) /\
  compile_ext_call_kwargs compile_expr ce NoneT ks kws s4 = ((vo,go,ignored),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  compile_raw_call_outbuf n s6 = ((ov,optr),s7) /\
  compile_raw_call_finish addr dp len gas valop ct n rof ov optr s7 = (result,sb) /\
  fn_has_code sa sb f /\
  create_cut_code {} s4 s5 /\
  create_cut_code {} s6 s7 /\
  create_cut_code {} s7 sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s6 s7) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s7 sb) ==>
  (create_cut_code {} sa s1 /\ fn_has_code sa s1 f) /\
  (create_cut_code {} s1 s2 /\ fn_has_code s1 s2 f) /\
  (create_cut_code {} s2 s4 /\ fn_has_code s2 s4 f) /\
  (create_cut_code {} s4 s5 /\ fn_has_code s4 s5 f) /\
  (create_cut_code {} s5 s6 /\ fn_has_code s5 s6 f) /\
  (create_cut_code {} s6 s7 /\ fn_has_code s6 s7 f) /\
  (create_cut_code {} s7 sb /\ fn_has_code s7 sb f) /\
  (create_cut_code {} s1 sb /\ fn_has_code s1 sb f) /\
  (create_cut_code {} s2 sb /\ fn_has_code s2 sb f) /\
  (create_cut_code {} s4 sb /\ fn_has_code s4 sb f) /\
  (create_cut_code {} s5 sb /\ fn_has_code s5 sb f) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s2 s4) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s5 sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_cut_code {} sa s1 /\ create_cut_code {} s1 s2` by
    metis_tac[cj 2 create_operand_cut_code, SND] >>
  drule_all raw_call_memory_header_code >> strip_tac >>
  drule raw_call_memory_gas_code >> strip_tac >>
  `create_cut_code {} s6 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s5 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s4 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s2 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s1 sb` by metis_tac[create_cut_code_join] >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s5 sb)` by
    (`cs_extends s5 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb /\ cs_extends s6 sb` by
       fs[create_cut_code_def] >>
     `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s6 sb)` by
       (irule raw_call_memory_inventory_join >> qexists_tac `s7` >> simp[]) >>
     irule raw_call_memory_inventory_join >> qexists_tac `s6` >> simp[]) >>
  fs[create_cut_code_def] >>
  `fn_has_code sa s1 f /\ fn_has_code s1 sb f` by metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 f /\ fn_has_code s2 sb f` by metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s4 f /\ fn_has_code s4 sb f` by metis_tac[fn_has_code_split] >>
  `fn_has_code s4 s5 f /\ fn_has_code s5 sb f` by metis_tac[fn_has_code_split] >>
  `fn_has_code s5 s6 f /\ fn_has_code s6 sb f` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

(* Administrative header edges consume no readings, including on the
   supplied spine. The proof inspects the actual installed fetches. *)
Theorem raw_call_memory_zero_marks[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS) (frag_code a b) ==>
  !x y. RTC (create_operand_native_step a b E ctx f p) x y ==>
    create_cut_region a b (FST (SND (SND x))) ==>
    create_cut_region a b (FST (SND (SND y))) /\
    create_cut_marks E (SND (SND (SND y))) =
      create_cut_marks E (SND (SND (SND x)))
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  simp_tac bool_ss [FORALL_PROD] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `create_operand_native_step _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [create_operand_native_step_def,LET_THM]) >>
  drule_all create_cut_region_rules >> strip_tac >>
  fs[create_operand_fetch_def, create_operand_at_def] >>
  `MEM inst (frag_code a b)` by metis_tac[] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by fs[EVERY_MEM]
  >~ [`create_cut_region a b _`]
  >- (irule (cj 2 operand_cut_region_edge) >>
      qpat_assum `create_prefix_step a b _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
      qpat_assum `gas_origin_edge F _ _ _ _ _ (OK _)` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  fs[trace_step_noninvoke, create_cut_marks_def, FILTER_APPEND_DISTRIB]
QED

Theorem raw_call_memory_safe_hit[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b) /\
  create_interior_visit a b E ctx f (p,d,k) s (before,hit,after) ==>
  (case hit of (_,_,inst,t) => inst_create_size_ok inst t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_cut_region a b s` by
    (drule_all create_cut_region_rules >> strip_tac >>
     fs[create_interior_visit_def, create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region a b u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def, create_operand_at_def, EVERY_MEM] >>
  `MEM inst (frag_code a b)` by metis_tac[] >>
  gvs[venomRunBoundedTheory.inst_create_size_ok_def]
QED

(* A keyword visit propagates its own source cut through the request bind;
   a later visit is safe independently of the keyword or request outcome. *)
Theorem raw_call_memory_keyword_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code m b) /\
  create_operand_cut a m E ctx f tops cx st0 source (es,s) /\
  (!v. storage_trace_frame (next v)) ==>
  create_operand_cut a b E ctx f tops cx st0 (bind source next) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rw[create_operand_cut_def] >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> simp[] >> fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_all raw_call_memory_safe_hit >> simp[create_body_cut_def] >>
  PairCases_on `hit` >> simp[]
QED

(* The left data post and the keyword pre are related at the actual
   zero-mark header endpoint, not at an arbitrary state at its exit PC. *)
Theorem raw_call_memory_header_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2] /\ i.inst_opcode <> GAS)
    (frag_code a m) /\ ~s.vs_halted /\
  (!t. create_expr_prefix a m E ctx f s [] t /\ create_operand_at m t ==>
       create_operand_cut m b E ctx f tops cx st0 source (es,t)) ==>
  create_operand_cut a b E ctx f tops cx st0 source (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rw[create_operand_cut_def] >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (`EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a m)` by
        fs[EVERY_MEM] >>
      drule_all raw_call_memory_safe_hit >> simp[create_body_cut_def] >>
      PairCases_on `hit` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS) (frag_code a m)` by
    fs[EVERY_MEM] >>
  `create_cut_region a m s` by
    (`create_operand_at a s` by fs[create_interior_visit_def] >>
     fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `create_cut_marks E front = []` by
    (mp_tac (Q.INST [`a` |-> `a`, `b` |-> `m`, `E` |-> `E`, `p` |-> `p`]
       raw_call_memory_zero_marks) >>
     (impl_tac >- simp[]) >> disch_then (qspecl_then [`(d,k,s,[])`, `(d1,k1,t,front)`] mp_tac) >> simp[]) >>
  fs[] >>
  qpat_assum `!t. _ ==> create_operand_cut m b _ _ _ _ _ _ _ _` drule_all >>
  disch_then (mp_tac o REWRITE_RULE [create_operand_cut_def]) >>
  disch_then drule >> disch_tac >>
  `t.vs_gas_readings = s.vs_gas_readings` by
    (drule_all create_prefix_gas_path >> disch_then (mp_tac o MATCH_MP gas_path_suffix) >>
     simp[gas_count_suffix_def]) >>
  fs[create_body_cut_def] >> first_assum ACCEPT_TAC
QED

(* Instantiate the common replay bind only at the two effectful value
   operands; the callback exposes the normal post of the crossed child. *)
Theorem raw_call_memory_replay_step[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ ~s.vs_halted /\
  create_operand_cut a m E ctx f tops cx st0 source (es,s) /\
  gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 a m source (es,s,G0,tn0) Q /\
  (!H r ee G tn t. Q H r ee G tn t ==> ?v. r = INL v) /\
  (!v. storage_trace_frame (next v)) /\
  (!H0 marks v mid G tn t.
    valid_horizon cx st0 H0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G0,tn0) marks (OK t,G,tn) /\
      Q H (INL v) (mid with gas_obs := []) G tn t) ==>
    create_operand_cut m b E ctx f tops cx st0 (next v) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx f tops cx st0 (bind source next) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule create_operand_cut_bind_replay >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >>
      strip_tac >> simp[] >> disj2_tac >>
      qexistsl_tac [`t`,`d1`,`k1`,`front`,`back`] >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem raw_call_memory_native_cut:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\ ~s.vs_halted /\
  create_cut_code {} sa s1 /\ fn_has_code sa s1 f /\
  create_cut_code {} s1 s2 /\ fn_has_code s1 s2 f /\
  create_cut_code {} s2 s4 /\ fn_has_code s2 s4 f /\
  create_cut_code {} s4 s5 /\ fn_has_code s4 s5 f /\
  create_cut_code {} s5 sb /\ fn_has_code s5 sb f /\
  create_cut_code {} s1 sb /\ fn_has_code s1 sb f /\
  create_cut_code {} s2 sb /\ fn_has_code s2 sb f /\
  create_cut_code {} s4 sb /\ fn_has_code s4 sb f /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2] /\ i.inst_opcode <> GAS)
    (frag_code s2 s4) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code s5 sb) /\
  create_operand_cut sa s1 E ctx f tops cx st0
    (bind (eval_expr cx a) (read_result cx)) (es,s) /\
  gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 sa s1
    (bind (eval_expr cx a) (read_result cx)) (es,s,G0,tn0) QA /\
  (!H r ee G tn t. QA H r ee G tn t ==> ?v. r = INL v) /\
  (!H0 marks av ea G tn t.
    valid_horizon cx st0 H0 ea.storage_trace /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G0,tn0) marks (OK t,G,tn) /\
      QA H (INL av) (ea with gas_obs := []) G tn t) ==>
    create_operand_cut s1 s2 E ctx f tops cx st0
      (bind (eval_expr cx de) (read_result cx)) (ea with gas_obs := [],t) /\
    ?QD.
      gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 s1 s2
        (bind (eval_expr cx de) (read_result cx)) (ea with gas_obs := [],t,G,tn) QD /\
      (!H r ee G' tn' u. QD H r ee G' tn' u ==> ?v. r = INL v) /\
      (!H1 ms dv ed GD tnD u v.
        valid_horizon cx st0 H1 ed.storage_trace /\
        (!H. valid_horizon cx st0 H ed.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G,tn) ms (OK u,GD,tnD) /\
          QD H (INL dv) (ed with gas_obs := []) GD tnD u) /\
        create_expr_prefix s2 s4 E ctx f u [] v /\ create_operand_at s4 v ==>
        create_operand_cut s4 s5 E ctx f tops cx st0 (eval_exprs cx kws)
          (ed with gas_obs := [],v))) ==>
  create_operand_cut sa sb E ctx f tops cx st0
    (eval_expr cx (Call ann (RawCallTarget flags) (a::de::kws) dflt)) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `last = \av dv kvs. do
    type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
    target <- lift_option_type (dest_AddressV av) "raw_call target";
    data <- lift_option_type (dest_BytesV dv) "raw_call data";
    amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
    eval_raw_call cx flags target data amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
    od` >>
  `eval_expr cx (Call ann (RawCallTarget flags) (a::de::kws) dflt) =
    bind (bind (eval_expr cx a) (read_result cx)) (\av.
      bind (bind (eval_expr cx de) (read_result cx)) (\dv.
        bind (eval_exprs cx kws) (last av dv)))` by
    simp[Abbr `last`,raw_call_eval_action] >>
  asm_rewrite_tac[] >>
  `!av dv kvs. storage_trace_frame (last av dv kvs)` by
    (simp[Abbr `last`] >> rpt gen_tac >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_checks] >>
     irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
     irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_lifts,storage_trace_frame_raw_call]) >>
  `!av dv. storage_trace_frame (bind (eval_exprs cx kws) (last av dv))` by
    (rpt gen_tac >> irule storage_trace_frame_bind_all >> simp[cj 6 evaluate_storage_trace_frame]) >>
  irule raw_call_memory_replay_step >>
  qpat_assum `gas_completed_operand _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  first_assum (irule_at (Pat `create_cut_code {} s1 sb`)) >>
  BETA_TAC >> qexists_tac `ce` >> simp[] >> conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  reverse conj_tac >- metis_tac[] >>
  map_every qx_gen_tac [`H0`,`marks`,`av`,`ea`,`GA`,`tnA`,`ta`] >>
  disch_then (fn th =>
    qpat_assum `!H0 marks av ea G tn t. _ ==> _` (strip_assume_tac o C MATCH_MP th) >>
    strip_assume_tac th) >>
  `~ta.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==>
       gas_origin_ptr_path _ _ _ (OK ta,_,_) /\ _` (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec o cj 1) >>
     simp[exit_result_def]) >>
  irule raw_call_memory_replay_step >>
  qpat_assum `gas_completed_operand _ _ _ _ s1 s2 _ _ _` (irule_at Any) >>
  first_assum (irule_at (Pat `create_cut_code {} s2 sb`)) >>
  BETA_TAC >> qexists_tac `ce` >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  map_every qx_gen_tac [`H1`,`ms`,`dv`,`ed`,`GD`,`tnD`,`td`] >> strip_tac >>
  `~td.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==>
       gas_origin_ptr_path _ _ _ (OK td,_,_) /\ _` (qspec_then `H1` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec o cj 1) >>
     simp[exit_result_def]) >>
  irule raw_call_memory_header_cut >>
  first_assum (irule_at (Pat `create_cut_code {} s2 s4`)) >>
  qexists_tac `ce` >> simp[] >> gen_tac >> strip_tac >>
  irule raw_call_memory_keyword_cut >>
  qpat_assum `create_cut_code {} s4 s5` (irule_at Any) >>
  qexists_tac `ce` >> simp[] >>
  qpat_assum `!H1 ms dv ed GD tnD u v. _ ==> create_operand_cut s4 s5 _ _ _ _ _ _ _ _`
    drule_all >> simp[]
QED
