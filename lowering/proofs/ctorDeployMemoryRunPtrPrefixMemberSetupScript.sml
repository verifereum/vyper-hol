(* Zero-high-bound member-address setup. *)
Theory ctorDeployMemoryRunPtrPrefixMemberSetup
Ancestors
  ctorDeployMemoryRunPtrPrefixBoolBody ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence ctorDeployMemoryRunPtrPrefixCopyRun
  abiDecoderMemberCode
  abiDecoderMemberSetup abiDecoderReentryPointer abiDecoderReentry abiDecoderContract abiEncoder
  ASCIInumbers
  compileEnv emitHelper exprLoweringProps words list rich_list arithmetic
  venomState venomInst venomExecSemantics ptrDiscipline finite_map
  codegenRel pred_set ptrSafeRun fragExec

Theorem prefix_member_setup_code:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) ==>
  let x = "%" ++ toString st.cs_next_var;
      y = "%" ++ toString (st.cs_next_var+1);
      z = "%" ++ toString (st.cs_next_var+2);
      w = "%" ++ toString (st.cs_next_var+3)
  in
  (if dyn then
     ops = (Var z,Var w) /\
     emitted_insts st middle =
       [mk_inst st.cs_next_id ADD [src;Lit (n2w ao)] [x];
        mk_inst (st.cs_next_id+1) DLOAD [Var x] [y];
        mk_inst (st.cs_next_id+2) ADD [src;Var y] [z];
        mk_inst (st.cs_next_id+3) ADD [Var dst;Lit (n2w vo)] [w]]
   else
     ops = (Var x,Var y) /\
     emitted_insts st middle =
       [mk_inst st.cs_next_id ADD [src;Lit (n2w ao)] [x];
        mk_inst (st.cs_next_id+1) ADD [Var dst;Lit (n2w vo)] [y]])
Proof
  Cases_on `dyn` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  strip_tac >>
  qpat_x_assum `_ = middle` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
  REFL_TAC
QED

Theorem prefix_member_add_pair:
  eval_operand a s = SOME u /\ eval_operand c s = SOME v /\
  op_taint tn a = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid ADD [a;c] [x];
      t = update_var x (u+v) s;
      H = set_prov G [x] (first_prov G [a;c]);
      qt = step_taint i s t tn
  in
    step_inst_base i s = OK t /\
    ghost_step fuel ctx PG G tn i s = (H,qt) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    op_taint qt (Var x) = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!y. y <> x ==> FLOOKUP H y = FLOOKUP G y /\
                       op_taint qt (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `((update_var x (u+v) s).vs_allocas = s.vs_allocas) /\
   ((update_var x (u+v) s).vs_fmp = s.vs_fmp)` by simp[update_var_def] >>
  conj_tac >- (irule prefix_bool_body_add_step >> simp[]) >>
  conj_tac >-
    (irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >> simp[]) >>
  conj_tac >- (irule prefix_bool_body_arith_ptr_step >> simp[]) >>
  `let q = step_taint (mk_inst iid ADD [a;c] [x]) s (update_var x (u+v) s) tn in
     q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
     q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
     (!y. y <> x ==> op_taint q (Var y) = op_taint tn (Var y)) /\
     (op_taint tn a = {} /\ op_taint tn c = {} ==> op_taint q (Var x) = {})` by
    (match_mp_tac prefix_bool_body_arith_taint_frame >> simp[]) >>
  fs[] >>
  Cases_on `first_prov G [a;c]` >>
  simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem prefix_member_add_taint:
  op_taint tn a = {} /\ op_taint tn c = {} ==>
  step_taint (mk_inst iid ADD [a;c] [x]) s (update_var x w s) tn =
    tn with t_var := tn.t_var |+ (x,{})
Proof
  strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF,
       out_taint_def, taint_component_equality, EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem prefix_member_dload_pair:
  eval_operand off s = SOME a /\ op_taint tn off = {} /\
  abi_decode_load DLOAD a s = w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [off] [x];
      t = update_var x w s;
      H = DRESTRICT G (COMPL {x});
      qt = tn with t_var := tn.t_var |+ (x,{})
  in step_inst_base i s = OK t /\
     step_inst fuel ctx i s = OK t /\
     ghost_step fuel ctx PG G tn i s = (H,qt) /\
     ptr_safe_step D lo fuel ctx fn PG G tn i s
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst_base (mk_inst iid DLOAD [off] [x]) s = OK (update_var x w s)` by
    (drule prefix_dload_step >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     gvs[abi_decode_load_def, abi_decode_source_def]) >>
  simp[step_inst_non_invoke, mk_inst_def, prefix_dload_ptr_step] >>
  drule prefix_dload_ghost_step >>
  disch_then (qspecl_then [`iid`,`x`,`ctx`,`PG`,`G`,`tn`,`fuel`] mp_tac) >>
  gvs[abi_decode_load_def, abi_decode_source_def, mk_inst_def,
      SRULE [mk_inst_def] prefix_copy_pure_taint]
QED

Theorem prefix_member_add_block:
  eval_operand a s = SOME u /\ eval_operand c s = SOME v /\
  op_taint tn a = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid ADD [a;c] [x]) ==>
  (ptr_safe_block D lo fuel ctx fn PG
     (set_prov G [x] (first_prov G [a;c]))
     (tn with t_var := tn.t_var |+ (x,{})) bb
     ((update_var x (u+v) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
   ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst iid ADD [a;c] [x]) s =
     OK (update_var x (u+v) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >>
     irule prefix_bool_body_add_step >> simp[]) >>
  `~is_terminator (mk_inst iid ADD [a;c] [x]).inst_opcode` by simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  `ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid ADD [a;c] [x]) s` by
    (irule prefix_bool_body_arith_ptr_step >> simp[]) >>
  `ghost_step fuel ctx PG G tn (mk_inst iid ADD [a;c] [x]) s =
     (set_prov G [x] (first_prov G [a;c]),
      tn with t_var := tn.t_var |+ (x,{}))` by
    (`step_taint (mk_inst iid ADD [a;c] [x]) s (update_var x (u+v) s) tn =
        tn with t_var := tn.t_var |+ (x,{})` by
       (irule prefix_member_add_taint >> simp[]) >>
     pop_assum (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >> simp[]) >>
  simp[]
QED

Theorem prefix_member_dload_block:
  eval_operand off s = SOME a /\ op_taint tn off = {} /\
  abi_decode_load DLOAD a s = w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [off] [x]) ==>
  (ptr_safe_block D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
     (tn with t_var := tn.t_var |+ (x,{})) bb
     ((update_var x w s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
   ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst iid DLOAD [off] [x]) s = OK (update_var x w s) /\
   ghost_step fuel ctx PG G tn (mk_inst iid DLOAD [off] [x]) s =
     (DRESTRICT G (COMPL {x}),tn with t_var := tn.t_var |+ (x,{})) /\
   ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid DLOAD [off] [x]) s` by
    (drule_all prefix_member_dload_pair >> simp[]) >>
  `~is_terminator (mk_inst iid DLOAD [off] [x]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >> simp[]
QED

(* The static member path, at the actual successful sequence endpoint. *)
Theorem prefix_member_static_pair:
  eval_operand src s = SOME a /\ eval_operand off s = SOME ao /\
  eval_operand (Var dst) s = SOME d /\
  op_taint tn src = {} /\ op_taint tn off = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ dst <> x /\ x <> y /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst iid ADD [src;off] [x];
                mk_inst (iid+1) ADD [Var dst;Lit vo] [y]] s = OK t ==>
  ?H qt.
    FLOOKUP H y = SOME (b,sz) /\
    op_taint qt (Var x) = {} /\ op_taint qt (Var y) = {} /\
    eval_operand (Var x) t = SOME (a+ao) /\
    eval_operand (Var y) t = SOME (d+vo) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       get_instruction bb s.vs_inst_idx = SOME (mk_inst iid ADD [src;off] [x]) /\
       get_instruction bb (SUC s.vs_inst_idx) =
         SOME (mk_inst (iid+1) ADD [Var dst;Lit vo] [y]) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx+2) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (a+ao) s` >>
  qabbrev_tac `s2 = update_var y (d+vo) s1` >>
  qabbrev_tac `G1 = set_prov G [x] (first_prov G [src;off])` >>
  qabbrev_tac `G2 = set_prov G1 [y] (SOME (b,sz))` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  qabbrev_tac `q2 = q1 with t_var := q1.t_var |+ (y,{})` >>
  `eval_operand (Var dst) s1 = SOME d /\
   op_taint q1 (Var dst) = {} /\ FLOOKUP G1 dst = SOME (b,sz) /\
   allocas_from lo s1` by
    (simp[Abbr `s1`, Abbr `q1`, Abbr `G1`, eval_operand_def,
          lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE,
          allocas_from_def] >>
     fs[allocas_from_def] >>
     Cases_on `first_prov G [src;off]` >>
     gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
         eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst iid ADD [src;off] [x]) s = OK s1 /\
   step_inst_base (mk_inst (iid+1) ADD [Var dst;Lit vo] [y]) s1 = OK s2` by
    (unabbrev_all_tac >> conj_tac >> irule prefix_bool_body_add_step >>
     simp[eval_operand_def]) >>
  `t = s2` by gvs[run_inst_seq_def] >>
  qexistsl_tac [`G2`,`q2`] >>
  simp[Abbr `G2`, Abbr `q2`, Abbr `q1`, Abbr `s2`, Abbr `s1`,
       set_prov_def, FLOOKUP_UPDATE, op_taint_def, eval_operand_def,
       lookup_var_def, update_var_def] >>
  conj_tac >-
    (rpt strip_tac >> simp[Abbr `G1`] >>
     Cases_on `first_prov G [src;off]` >>
     simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  rpt gen_tac >> strip_tac >>
  strip_tac >> irule prefix_member_add_block >>
  simp[mk_inst_def] >>
  simp[eval_operand_def, op_taint_def] >>
  irule prefix_member_add_block >>
  simp[mk_inst_def, update_var_def, eval_operand_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE, first_prov_def, op_prov_def, set_prov_def] >>
  fs[eval_operand_def, lookup_var_def, op_taint_def, allocas_from_def] >>
  simp[ADD1, ADD_ASSOC] >> metis_tac[]
QED

Theorem prefix_member_offset_pair:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst iid ADD [src;Lit ao] [x];
                mk_inst (iid+1) DLOAD [Var x] [y]] s = OK t ==>
  ?H qt.
    t.vs_labels = s.vs_labels /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!v. v <> x /\ v <> y ==> eval_operand (Var v) t = eval_operand (Var v) s) /\
    (?w. eval_operand (Var y) t = SOME w) /\
    op_taint qt (Var y) = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       get_instruction bb s.vs_inst_idx = SOME (mk_inst iid ADD [src;Lit ao] [x]) /\
       get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (iid+1) DLOAD [Var x] [y]) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx+2) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (a+ao) s` >>
  qabbrev_tac `w = abi_decode_load DLOAD (a+ao) s1` >>
  qabbrev_tac `s2 = update_var y w s1` >>
  qabbrev_tac `G1 = set_prov G [x] (first_prov G [src;Lit ao])` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  `step_inst_base (mk_inst iid ADD [src;Lit ao] [x]) s = OK s1` by
    (simp[Abbr `s1`] >> irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
  `eval_operand (Var x) s1 = SOME (a+ao) /\
   op_taint q1 (Var x) = {} /\ allocas_from lo s1` by
    (simp[Abbr `s1`, Abbr `q1`, eval_operand_def, lookup_var_def, update_var_def,
          op_taint_def, FLOOKUP_UPDATE, allocas_from_def] >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (iid+1) DLOAD [Var x] [y]) s1 = OK s2` by
    (simp[Abbr `s2`, Abbr `w`] >>
     drule prefix_dload_step >>
     disch_then (qspecl_then [`iid+1`,`y`] mp_tac) >>
     simp[abi_decode_load_def, abi_decode_source_def]) >>
  `t = s2` by gvs[run_inst_seq_def] >>
  `t.vs_labels = s.vs_labels /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!v. v <> x /\ v <> y ==> eval_operand (Var v) t = eval_operand (Var v) s) /\
   (?w. eval_operand (Var y) t = SOME w)` by
    simp[Abbr `s2`, Abbr `s1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`DRESTRICT G1 (COMPL {y})`,`q1 with t_var := q1.t_var |+ (y,{})`] >>
  simp[Abbr `q1`, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac >-
    (rpt strip_tac >> simp[Abbr `G1`] >>
     Cases_on `first_prov G [src;Lit ao]` >>
     simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule prefix_member_add_block >> simp[mk_inst_def, eval_operand_def, op_taint_def] >>
  fs[op_taint_def] >>
  irule prefix_member_dload_block >>
  simp[Abbr `s1`, Abbr `s2`, Abbr `w`, update_var_def, mk_inst_def,
       eval_operand_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
       abi_decode_load_def, abi_decode_source_def, allocas_from_def] >>
  fs[allocas_from_def, abi_decode_load_def, abi_decode_source_def, update_var_def] >>
  simp[ADD1, ADD_ASSOC] >> metis_tac[]
QED

Theorem prefix_member_setup_static_pair:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) F ao vo st = (ops,middle) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  ?H qt child_dst.
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    eval_operand (FST ops) t = SOME (a+n2w ao) /\
    eval_operand (SND ops) t = SOME (d+n2w vo) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       (!j. j < LENGTH (emitted_insts st middle) ==>
          get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle)) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> drule prefix_member_setup_code >> simp[] >> strip_tac >> gvs[] >>
  `dst <> "%" ++ toString st.cs_next_var /\
   "%" ++ toString st.cs_next_var <> "%" ++ toString (st.cs_next_var+1)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, toString_11] >>
     metis_tac[LESS_EQ_REFL]) >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao) /\
   op_taint tn (Lit (n2w ao)) = {}` by simp[eval_operand_def, op_taint_def] >>
  fs[] >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_member_static_pair >>
  simp[toString_11] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`qt`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> first_x_assum irule >>
  qpat_x_assum `!j. j < _ ==> _` (fn th =>
    mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >> simp[ADD1]
QED

Theorem prefix_member_seq_split:
  run_inst_seq (xs ++ ys) s = OK t ==>
  ?u. run_inst_seq xs s = OK u /\ run_inst_seq ys u = OK t
Proof
  strip_tac >> Cases_on `?u. run_inst_seq xs s = OK u`
  >- (pop_assum strip_assume_tac >> drule run_inst_seq_append >>
      disch_then (qspec_then `ys` mp_tac) >> metis_tac[]) >>
  fs[] >> drule run_inst_seq_append_err >>
  disch_then (qspec_then `ys` mp_tac) >> metis_tac[]
QED

Theorem prefix_member_setup_dynamic_pair:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) T ao vo st = (ops,middle) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var src /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  ?H qt child_dst.
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       (!j. j < LENGTH (emitted_insts st middle) ==>
          get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle)) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> drule prefix_member_setup_code >> simp[] >> strip_tac >> gvs[] >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `y = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `z = "%" ++ toString (st.cs_next_var+2)` >>
  qabbrev_tac `w = "%" ++ toString (st.cs_next_var+3)` >>
  `?u. run_inst_seq [mk_inst st.cs_next_id ADD [src;Lit (n2w ao)] [x];
                     mk_inst (st.cs_next_id+1) DLOAD [Var x] [y]] s = OK u /\
       run_inst_seq [mk_inst (st.cs_next_id+2) ADD [src;Var y] [z];
                     mk_inst (st.cs_next_id+3) ADD [Var dst;Lit (n2w vo)] [w]] u = OK t` by
    (irule prefix_member_seq_split >> simp[Abbr `x`, Abbr `y`, Abbr `z`, Abbr `w`]) >>
  pop_assum strip_assume_tac >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_member_offset_pair >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `dst <> x /\ dst <> y /\ dst <> z /\ x <> y /\ z <> w` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        Abbr `x`, Abbr `y`, Abbr `z`, Abbr `w`, toString_11] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  `eval_operand src u = SOME a /\ op_taint qt src = {}` by
    (Cases_on `src` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        Abbr `x`, Abbr `y`, eval_operand_def, op_taint_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  `eval_operand (Var dst) u = SOME d /\ op_taint qt (Var dst) = {} /\
   FLOOKUP H dst = SOME (b,sz) /\ allocas_from lo u` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  qabbrev_tac `u2 = u with vs_inst_idx := s.vs_inst_idx+2` >>
  `run_inst_seq [mk_inst (st.cs_next_id+2) ADD [src;Var y] [z];
                 mk_inst ((st.cs_next_id+2)+1) ADD [Var dst;Lit (n2w vo)] [w]] u2 =
    OK (t with vs_inst_idx := s.vs_inst_idx+2)` by
    (fs[Abbr `u2`, run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def, ADD_ASSOC, mk_inst_def, is_terminator_def]) >>
  `eval_operand src u2 = SOME a /\ eval_operand (Var y) u2 = SOME w' /\
   eval_operand (Var dst) u2 = SOME d /\ allocas_from lo u2` by
    (simp[Abbr `u2`, eval_operand_def, lookup_var_def, allocas_from_def] >>
     Cases_on `src` >> fs[eval_operand_def, lookup_var_def, allocas_from_def] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_member_static_pair >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H'`,`qt'`] >>
  fs[Abbr `z`, Abbr `w`] >>
  conj_tac >-
    (rpt strip_tac >>
     `v <> x /\ v <> y /\
      v <> "%" ++ toString (st.cs_next_var+2) /\
      v <> "%" ++ toString (st.cs_next_var+3)` by
       (fs[not_fresh_at_def, Abbr `x`, Abbr `y`] >>
        metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
     qpat_x_assum `!v. _ ==> FLOOKUP H' v = _ /\ _`
       (qspec_then `v` mp_tac) >>
     qpat_x_assum `!v. _ ==> FLOOKUP H v = _ /\ _`
       (qspec_then `v` mp_tac) >> fs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst st.cs_next_id ADD [src;Lit (n2w ao)] [x]) /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (st.cs_next_id+1) DLOAD [Var x] [y]) /\
   get_instruction bb u2.vs_inst_idx = SOME (mk_inst (st.cs_next_id+2) ADD [src;Var y] ["%" ++ toString (st.cs_next_var+2)]) /\
   get_instruction bb (SUC u2.vs_inst_idx) = SOME (mk_inst (st.cs_next_id+3) ADD [Var dst;Lit (n2w vo)] ["%" ++ toString (st.cs_next_var+3)])` by
    (qpat_x_assum `!j. j < 4 ==> _` (fn th =>
       map_every mp_tac [Q.SPEC `0` th, Q.SPEC `1` th, Q.SPEC `2` th, Q.SPEC `3` th]) >>
     simp[Abbr `u2`, ADD1, ADD_COMM]) >>
  `u2.vs_inst_idx+2 = s.vs_inst_idx+4` by simp[Abbr `u2`, ADD_ASSOC] >>
  qpat_x_assum `!fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ G tn _ _` irule >>
  simp[] >>
  qpat_x_assum `!fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ H qt _ _` irule >>
  fs[]
QED

Theorem prefix_member_setup_ghost:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var src /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  ?H qt child_dst.
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       (!j. j < LENGTH (emitted_insts st middle) ==>
          get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle)) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> Cases_on `dyn`
  >- (irule prefix_member_setup_dynamic_pair >> metis_tac[]) >>
  drule_all prefix_member_setup_static_pair >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`qt`,`child_dst`] >> simp[]
QED

Theorem prefix_member_setup_pair:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb+ao) : bytes32) s = n2w payload_off /\
           sb+payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  ?H qt child_dst.
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st middle /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
       (!j. j < LENGTH (emitted_insts st middle) ==>
          get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))) ==>
       ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle)) ==>
       ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  gvs[] >>
  drule_all prefix_member_setup_ghost >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`qt`,`child_dst`] >> simp[]
QED

Theorem prefix_member_setup_layout:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) ==>
  middle.cs_current_bb = st.cs_current_bb /\
  middle.cs_current_insts = st.cs_current_insts ++ emitted_insts st middle /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)
Proof
  strip_tac >> drule prefix_member_setup_code >>
  Cases_on `dyn` >> simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  strip_tac >> qpat_x_assum `_ = middle` (SUBST1_TAC o SYM) >> simp[mk_inst_def]
QED

Theorem prefix_member_setup_current_bb:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> drule prefix_member_setup_layout >> strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st middle` >> simp[] >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by fs[EVERY_MEM] >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  metis_tac[venomInstPropsTheory.step_preserves_control_flow]
QED

Theorem prefix_member_setup_run_continuation:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!fuel bb.
     (!j. j < LENGTH (emitted_insts st middle) ==>
       get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))) ==>
     ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle)) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s) ==>
  ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := LENGTH middle.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule prefix_member_setup_layout >> strip_tac >>
  drule_all prefix_member_setup_current_bb >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX middle.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `!j. j < LENGTH (emitted_insts st middle) ==>
       get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts st middle))` by
    (fs[IS_PREFIX_APPEND] >> rpt strip_tac >>
     simp[get_instruction_def, EL_APPEND_EQN, LENGTH_APPEND]) >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st middle))` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
     fs[ptr_safe_run_def]) >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
    (qpat_x_assum `!fuel bb. _ ==> _ ==> _` irule >> simp[]) >>
  simp[ptr_safe_run_def]
QED
