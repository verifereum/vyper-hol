(* The checked ADD/MCOPY/MSTORE suffix of an ordinary Slice write. *)
Theory bodySliceWritePathMods
Ancestors
  bodySliceWritePathModsCursor bodyFullUnwrapRun instSeqPtrLo
  exprSimSliceData exprLoweringProps fragExec fragExecMem fragGasOriginPtr
  fragGasSeqPtr instMemFrontier memSafeRun emitHelperProps
  compileEnv contextCodegenRel list rich_list pred_set words
  instSeqComposePtr logInstSeqPtr ghostPcTransportPtr instIdxIndep

Theorem slice_step_keeps_cursor[local]:
  step_inst_base inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> conj_tac
  >- (drule_all venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
  irule venomExecSemanticsTheory.step_inst_base_preserves_inst_idx >>
  qexists_tac `inst` >> simp[]
QED

Theorem slice_cursor_singleton[local]:
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK t /\
  step_prov PG G i t = G' /\ step_taint i s t tn = tn' /\
  ptr_inst_ok D 0 0 ctx func G tn i (s with vs_inst_idx := k) ==>
  inst_seq_ptr D 0 ctx func PG G tn [i] (s with vs_inst_idx := k) G' tn'
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn [i] (s with vs_inst_idx := k)
     (step_prov PG G i (t with vs_inst_idx := k))
     (step_taint i (s with vs_inst_idx := k) (t with vs_inst_idx := k) tn)`
    suffices_by simp[] >>
  irule inst_seq_ptr_singleton >>
  simp[step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem slice_write_path_mods:
  emit_op ADD [Var src;start] sd = (Var copy_var,se) /\
  emit_void MCOPY [Var dst;Var copy_var;cnt] se = ((),sf) /\
  emit_void MSTORE [Var root;cnt] sf = ((),sb) /\
  fn_has_code sd sb func /\ fn_inst_ids_distinct func /\
  alloca_history func v /\ alloca_inv v /\ ~v.vs_halted /\
  v.vs_current_bb = sd.cs_current_bb /\
  v.vs_inst_idx = LENGTH sd.cs_current_insts /\
  allocas_from lo v /\ lo <= v.vs_alloca_next /\
  lookup_var root za = SOME w /\ eval_operand cnt za = SOME (n2w k) /\
  op_taint tn3 cnt = {} /\
  ptr_covers G3 tn3 dst za k /\ ptr_covers G3 tn3 root za N /\
  32 <= N /\ w2n w + N <= za.vs_alloca_next /\
  w2n p + i + k <= za.vs_alloca_next /\ k < dimword (:256) /\
  (!D fuel. ptr_inst_ok D 0 fuel ctx func G2 tn2
      (mk_inst sd.cs_next_id ADD [Var src;start]
        [STRING #"%" (toString sd.cs_next_var)]) v) /\
  (!D fuel. ptr_inst_ok D 0 fuel ctx func G3 tn3
      (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) za) /\
  (!D fuel. ptr_inst_ok D 0 fuel ctx func G3 tn4
      (mk_inst sf.cs_next_id MSTORE [Var root;cnt] []) zc) /\
  step_inst_base
      (mk_inst sd.cs_next_id ADD [Var src;start]
        [STRING #"%" (toString sd.cs_next_var)]) v = OK za /\
  step_inst_base
      (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) za = OK zc /\
  step_inst_base
      (mk_inst sf.cs_next_id MSTORE [Var root;cnt] []) zc = OK zt /\
  step_prov PG G2
      (mk_inst sd.cs_next_id ADD [Var src;start]
        [STRING #"%" (toString sd.cs_next_var)]) za = G3 /\
  step_taint
      (mk_inst sd.cs_next_id ADD [Var src;start]
        [STRING #"%" (toString sd.cs_next_var)]) v za tn2 = tn3 /\
  step_prov PG G3
      (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) zc = G3 /\
  step_taint
      (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) za zc tn3 = tn4 /\
  step_prov PG G3
      (mk_inst sf.cs_next_id MSTORE [Var root;cnt] []) zt = G3 /\
  step_taint
      (mk_inst sf.cs_next_id MSTORE [Var root;cnt] []) zc zt tn4 = tm /\
  run_inst_seq_mem_ok
    [mk_inst sd.cs_next_id ADD [Var src;start]
       [STRING #"%" (toString sd.cs_next_var)];
     mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] [];
     mk_inst sf.cs_next_id MSTORE [Var root;cnt] []] v /\
  (!st. inst_dload_in_section
      (mk_inst sd.cs_next_id ADD [Var src;start]
        [STRING #"%" (toString sd.cs_next_var)]) st /\
    inst_dload_in_section
      (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) st /\
    inst_dload_in_section
      (mk_inst sf.cs_next_id MSTORE [Var root;cnt] []) st) /\
  (!pre i' post u.
    [mk_inst sd.cs_next_id ADD [Var src;start]
       [STRING #"%" (toString sd.cs_next_var)];
     mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] [];
     mk_inst sf.cs_next_id MSTORE [Var root;cnt] []] = pre ++ i'::post /\
    run_inst_seq pre v = OK u ==> dalloca_no_wrap i' u) /\
  ~is_terminator ADD /\ ~is_terminator MCOPY /\ ~is_terminator MSTORE /\
  zt.vs_current_bb = sd.cs_current_bb /\
  zt.vs_alloca_next = za.vs_alloca_next /\
  target = zt with vs_inst_idx := LENGTH sb.cs_current_insts /\
  sb.cs_current_bb = sd.cs_current_bb /\
  sb.cs_current_insts = sd.cs_current_insts ++
    [mk_inst sd.cs_next_id ADD [Var src;start]
       [STRING #"%" (toString sd.cs_next_var)];
     mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] [];
     mk_inst sf.cs_next_id MSTORE [Var root;cnt] []] ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (v,G2,tn2) [] (OK target,G3,tm)) /\
  alloca_history func target /\ ~target.vs_halted /\
  target.vs_current_bb = sd.cs_current_bb /\
  target.vs_inst_idx = LENGTH sb.cs_current_insts /\
  target.vs_alloca_next = za.vs_alloca_next
Proof
  strip_tac >>
  qabbrev_tac `offset_inst = mk_inst sd.cs_next_id ADD [Var src;start]
    [STRING #"%" (toString sd.cs_next_var)]` >>
  qabbrev_tac `copy_inst = mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []` >>
  qabbrev_tac `store_inst = mk_inst sf.cs_next_id MSTORE [Var root;cnt] []` >>
  `?bb. lookup_block sd.cs_current_bb func.fn_blocks = SOME bb /\
     !i. i < LENGTH [offset_inst;copy_inst;store_inst] ==>
       get_instruction bb (LENGTH sd.cs_current_insts + i) =
         SOME (EL i [offset_inst;copy_inst;store_inst])` by
    metis_tac[fragExecTheory.fn_has_code_same_block] >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb` by
    gvs[] >>
  `get_instruction bb v.vs_inst_idx = SOME offset_inst` by
    (qpat_assum `v.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator offset_inst.inst_opcode` by
    simp[Abbr `offset_inst`, venomInstTheory.mk_inst_def] >>
  `za.vs_current_bb = v.vs_current_bb /\ za.vs_inst_idx = v.vs_inst_idx` by
    (irule slice_step_keeps_cursor >> qexists_tac `offset_inst` >> simp[]) >>
  `~in_revert_forward func za` by
    (irule bodySliceWritePathModsCursorTheory.cursor_lookup_not_revert_forward >>
     qexistsl_tac [`bb`,`offset_inst`] >>
     gvs[Abbr `offset_inst`, venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def]) >>

  `!D k. ptr_inst_ok D 0 0 ctx func G3 tn3 copy_inst
      (za with vs_inst_idx := k)` by
    (rpt gen_tac >>
     irule bodySliceWritePathModsCursorTheory.ptr_inst_ok_cursor_transport >>
     (rpt conj_tac
      >- simp[Abbr `copy_inst`, venomInstTheory.mk_inst_def,
              venomInstTheory.is_terminator_def]
      >- simp[Abbr `copy_inst`, venomInstTheory.mk_inst_def]
      >- first_assum ACCEPT_TAC
      >- (qexists_tac `zc` >> first_assum ACCEPT_TAC)
      >- (qpat_x_assum `!D fuel. _` (fn th =>
            qspecl_then [`D`,`0`] mp_tac th) >> simp[]))) >>
  `~is_terminator copy_inst.inst_opcode` by
    simp[Abbr `copy_inst`, venomInstTheory.mk_inst_def] >>
  `zc.vs_current_bb = za.vs_current_bb /\ zc.vs_inst_idx = za.vs_inst_idx` by
    (irule slice_step_keeps_cursor >> qexists_tac `copy_inst` >> simp[]) >>
  `~in_revert_forward func zc` by
    (irule bodySliceWritePathModsCursorTheory.cursor_lookup_not_revert_forward >>
     qexistsl_tac [`bb`,`offset_inst`] >>
     gvs[Abbr `offset_inst`, venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def]) >>
  `!D k. ptr_inst_ok D 0 0 ctx func G3 tn4 store_inst
      (zc with vs_inst_idx := k)` by
    (rpt gen_tac >>
     irule bodySliceWritePathModsCursorTheory.ptr_inst_ok_cursor_transport >>
     (rpt conj_tac
      >- simp[Abbr `store_inst`, venomInstTheory.mk_inst_def,
              venomInstTheory.is_terminator_def]
      >- simp[Abbr `store_inst`, venomInstTheory.mk_inst_def]
      >- first_assum ACCEPT_TAC
      >- (qexists_tac `zt` >> first_assum ACCEPT_TAC)
      >- (qpat_x_assum `!D fuel. _` (fn th =>
            qspecl_then [`D`,`0`] mp_tac th) >> simp[]))) >>
  `~is_terminator store_inst.inst_opcode` by
    simp[Abbr `store_inst`, venomInstTheory.mk_inst_def] >>
  `!D. inst_seq_ptr D 0 ctx func PG G2 tn2 [offset_inst] v G3 tn3` by
    (gen_tac >>
     `inst_seq_ptr D 0 ctx func PG G2 tn2 [offset_inst] v
       (step_prov PG G2 offset_inst za) (step_taint offset_inst v za tn2)`
       suffices_by simp[] >>
     irule inst_seq_ptr_singleton >> simp[] >>
     qpat_assum `!D fuel. ptr_inst_ok D 0 fuel ctx func G2 tn2 offset_inst v`
       (qspecl_then [`D`,`0`] ACCEPT_TAC)) >>
  `!D j. inst_seq_ptr D 0 ctx func PG G3 tn3 [copy_inst]
       (za with vs_inst_idx := j) G3 tn4` by
    (rpt gen_tac >> irule slice_cursor_singleton >> simp[]) >>
  `!D j. inst_seq_ptr D 0 ctx func PG G3 tn4 [store_inst]
       (zc with vs_inst_idx := j) G3 tm` by
    (rpt gen_tac >> irule slice_cursor_singleton >> simp[]) >>
  `!D j. inst_seq_ptr D 0 ctx func PG G3 tn3 [copy_inst;store_inst]
       (za with vs_inst_idx := j) G3 tm` by
    (rpt gen_tac >>
     pure_once_rewrite_tac[GSYM (EVAL ``[x] ++ [y]``)] >>
     irule inst_seq_ptr_append_ok >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`G3`,`zc with vs_inst_idx := j`,`tn4`] >>
     simp[run_inst_seq_def, step_inst_inst_idx_indep, exec_result_map_def]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G2 tn2 [offset_inst;copy_inst;store_inst] v G3 tm` by
    (gen_tac >>
     pure_once_rewrite_tac[GSYM (EVAL ``[x] ++ [y;z]``)] >>
     irule inst_seq_ptr_append_ok >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`G3`,`za`,`tn3`] >> simp[run_inst_seq_def]) >>
  `run_inst_seq [offset_inst;copy_inst;store_inst] v = OK zt` by
    simp[exprLoweringPropsTheory.run_inst_seq_def,Abbr `offset_inst`,
         Abbr `copy_inst`,Abbr `store_inst`] >>
  `!D. inst_seq_ptr D lo ctx func PG G2 tn2 [offset_inst;copy_inst;store_inst] v G3 tm` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [offset_inst;copy_inst;store_inst]` by
    simp[Abbr `offset_inst`,Abbr `copy_inst`,Abbr `store_inst`,venomInstTheory.mk_inst_def] >>
  qpat_x_assum `target = _` SUBST1_TAC >>
  conj_tac >-
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     simp[] >> qexistsl_tac [`[offset_inst;copy_inst;store_inst]`,`sd`] >>
     simp[] >> qpat_assum `!pre i post u. _ ==> dalloca_no_wrap i u` mp_tac >>
     simp[] >> disch_tac >> disch_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
     simp[] >> qexistsl_tac [`[offset_inst;copy_inst;store_inst]`,`v`,`sd`] >> simp[]) >>
  imp_res_tac venomExecProofsTheory.step_inst_base_OK_preserves_halted >> simp[]
QED
